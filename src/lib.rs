#![no_std]
#![warn(missing_docs)]

//! An embedded driver for TPIC6B595 shift registers. Devices can be daisy-chained. To save pins /SRCLR is not
//! used (tie it to VCC), clearing is done by shifting zeroes through all devices.

use embedded_hal::delay::DelayNs;
use embedded_hal::digital::{OutputPin, PinState};
use embedded_hal::spi::SpiDevice;

#[derive(Debug)]
/// Custom Error type for this crate
pub enum Error<SPI> {
    /// Supplied index is out of bounds
    IndexOutOfBounds,
    /// Error from GPIO pin
    IoError,
    /// Error from SPI
    Spi(SPI),
}

/// ShiftRegister structure for the TPIC6B595
pub struct ShiftRegister<const N: usize, SPI, OE, LATCH, D> {
    /// SPI device, connect SPI_MOSI to device pin "SER IN", SPI_CLK to "CRCLK"
    spi: SPI,
    /// Output enable (Pin /G)
    not_oe: OE,
    /// Latch (Pin RCK)
    latch: LATCH,
    /// Delay for pulse width
    delay: D,
    /// Buffer representing the outputs, each byte represents one Shift Register
    data: [u8; N],
}

impl<const N: usize, SPI, OE, LATCH, D> ShiftRegister<N, SPI, OE, LATCH, D>
where
    SPI: SpiDevice,
    OE: OutputPin,
    LATCH: OutputPin,
    D: DelayNs,
{
    /// Creates a new `ShiftRegister` instance.
    ///
    /// # Arguments
    ///
    /// * `not_oe` - The output enable pin (Pin /G; active low).
    /// * `latch` - The storage register clock (latch) pin (Pin RCK).
    /// * `delay` - A delay provider for timing operations.
    ///
    /// # Returns
    ///
    /// A new `ShiftRegister` instance initialized with the given pins and a zeroed internal data buffer.
    pub fn new(spi: SPI, not_oe: OE, latch: LATCH, delay: D) -> Self {
        ShiftRegister {
            spi,
            not_oe,
            latch,
            delay,
            data: [0u8; N],
        }
    }

    /// Enables or disables the output buffers.
    ///
    /// Enables the output buffers by pulling the /G pin low (enabled) or high (disabled)
    ///
    /// # Arguments
    ///
    /// * `enable` - enable (`true`) or disable (`false`) the output buffers.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success or an error if the operation fails.
    pub fn output_enable(&mut self, enable: bool) -> Result<(), OE::Error> {
        self.not_oe.set_state(PinState::from(!enable))
    }

    /// Latch data: Pulse RCK pin for 100 ns
    fn latch(&mut self) -> Result<(), LATCH::Error> {
        self.latch.set_high()?;
        self.delay.delay_ns(100);
        self.latch.set_low()
    }

    /// Retrieves the output state at the specified index.
    ///
    /// # Arguments
    ///
    /// * `idx` - The index of the output to retrieve.
    ///
    /// # Returns
    ///
    /// A `Result` which can be:
    /// - `Ok(bool)`: The value of the output at the given index (`true` for enabled, `false` for disabled).
    /// - `Err(Error::IndexOutOfBounds)`: The provided index `idx` is out of bounds for the bit array or if
    ///   `idx` is greater than or equal to the total number of bits (`N * 8`).
    pub fn get_output(&self, idx: usize) -> Result<bool, Error<SPI::Error>> {
        let max_bits: usize = N
            .checked_mul(size_of::<u8>())
            .ok_or(Error::IndexOutOfBounds)?;
        if idx >= max_bits {
            return Err(Error::IndexOutOfBounds);
        }
        let byte_idx = idx / 8;
        let bit_idx = idx % 8;
        Ok(self.data[byte_idx] & (1 << bit_idx) != 0)
    }

    /// Sets the output at the specified index.
    ///
    /// Note that this function only updates internal state of the ShiftRegister driver. To set the
    /// actual outputs of the device call [`ShiftRegister::write_all()`]
    /// # Arguments
    ///
    /// * `idx` - The index of the output to set.
    /// * `output_state` - desired state of the output (`true` for enabled, `false` for disabled) 
    ///
    /// # Returns
    ///
    /// A `Result` which can be:
    /// - `Ok()`
    /// - `Err(Error::IndexOutOfBounds)`: The provided index `idx` is out of bounds for the bit array or if
    ///   `idx` is greater than or equal to the total number of bits (`N * 8`).
    pub fn set_output(&mut self, idx: usize, output_state: bool) -> Result<(), Error<SPI::Error>> {
        let max_bits: usize = N
            .checked_mul(size_of::<u8>())
            .ok_or(Error::IndexOutOfBounds)?;
        if idx >= max_bits {
            return Err(Error::IndexOutOfBounds);
        }
        let byte_idx = idx / 8;
        let bit_idx = idx % 8;
        self.data[byte_idx] &= !(1u8 << bit_idx);
        if output_state {
            self.data[byte_idx] |= 1 << bit_idx;
        }
        Ok(())
    }

    /// Clears all outputs
    pub fn clear(&mut self) {
        self.data = [0u8; N];
    }

    /// Writes all current data to the shift register via SPI.
    pub fn write_all(&mut self) -> Result<(), Error<SPI::Error>> {
        self.spi.write(&self.data).map_err(Error::Spi)?;
        self.latch().map_err(|_| Error::IoError)?;
        Ok(())
    }

    /// Writes a specific output via SPI
    ///
    /// All other outputs are left untouched
    ///
    /// This is a convenience method equivalent to `set_output(idx, output_state); write_all();`
    pub fn write_output(&mut self, idx: usize, output_state: bool) -> Result<(), Error<SPI::Error>> {
        self.set_output(idx, output_state)?;
        self.write_all()
    }
}

// [X]  OE  /G
// [ ]  SER
// [ ]  CLK
// [X]  LATCH RCK  Pulse
// [X]  clear
// [x]  write_all
// Description from the datasheet, for reference while implementing....
//
// This device contains an 8-bit serial-in, parallel-out
// shift register that feeds an 8-bit D-type storage
// register.
// Data transfers through the shift and storage
// registers on the rising edge of the shift-register clock
// (SRCK) and the register clock (RCK), respectively.
//
// The storage register transfers data to the output buffer
// when shift-register clear ( SRCLR) is high.
//
// Write data
// and read data are valid only when RCK is low. When
// SRCLR is low, the input shift register is cleared.
// When output enable ( G) is held high, all data in the
// output buffers is held low and all drain outputs are off.
// When G is held low, data from the storage register
// is transparent to the output buffers. When data in the
// output buffers is low, the DMOS-transistor outputs are
// off. When data is high, the DMOS transistor outputs
// have sink-current capability. The serial output (SER
// OUT) allows for cascading of the data from the shift
// register to additional devices.
//
// DATASHEET https://www.ti.com/lit/ds/symlink/tpic6b595.pdf?ts=1764222514654
