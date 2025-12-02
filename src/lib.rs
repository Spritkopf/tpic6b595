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
    /// Error from a GPIO pin operation (e.g., setting output state of LATCH or Output Enable pins).
    IoError,
    /// Error from SPI device communication
    Spi(SPI),
}

/// ShiftRegister structure for the TPIC6B595
///
/// The parameter N is the number of daisy-chained shift registers. Data is shifted out MSB first,
/// so byte N in the data buffer is the first register, byte N-1 is the second and so on:
/// ```text
///      data[N]  data[N-1]  ...    data[0]   
///     ┌────────┌────────┌────────┌────────┐
///     │01234567│01234567│  ...   │01234567│
///     └────────└────────└────────└────────┘
/// idx  01234567 89 ...                  (N*8)
/// ```
/// The set_output / write_output functions will take care of the byte ordering, so all that is
/// needed is the index
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
    pub fn enable_output(&mut self, enable: bool) -> Result<(), Error<SPI::Error>> {
        self.not_oe.set_state(PinState::from(!enable)).map_err(|_| Error::IoError)
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
        let max_bits: usize = N.checked_mul(8).ok_or(Error::IndexOutOfBounds)?;
        if idx >= max_bits {
            return Err(Error::IndexOutOfBounds);
        }
        let byte_idx = N - 1 - (idx / 8);
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
        let max_bits: usize = N.checked_mul(8).ok_or(Error::IndexOutOfBounds)?;
        if idx >= max_bits {
            return Err(Error::IndexOutOfBounds);
        }
        let byte_idx = N - 1 - (idx / 8);
        let bit_idx = idx % 8;
        if output_state {
            self.data[byte_idx] |= 1 << bit_idx;
        } else {
            self.data[byte_idx] &= !(1u8 << bit_idx);
        }
        Ok(())
    }

    /// Clears all outputs
    ///
    /// Note that this function only updates internal state of the ShiftRegister driver. To set the
    /// actual outputs of the device call [`ShiftRegister::write_all()`]
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
    pub fn write_output(
        &mut self,
        idx: usize,
        output_state: bool,
    ) -> Result<(), Error<SPI::Error>> {
        self.set_output(idx, output_state)?;
        self.write_all()
    }
}

#[cfg(test)]
mod test {
    extern crate std;
    use super::*;
    use embedded_hal_mock::eh1::{
        delay::{NoopDelay as DelayMock, CheckedDelay, Transaction as DelayTransaction},
        digital::{Mock as PinMock, State, Transaction as PinTransaction},
        spi::{Mock as SpiMock, Transaction as SpiTransaction},
    };

    #[test]
    /// Clear all outputs
    fn test_clear() {
        let mut spi_mock: SpiMock<u8> = SpiMock::new(&[]);
        let mut oe_mock = PinMock::new(&[]);
        let mut latch_mock = PinMock::new(&[]);
        let delay_mock = DelayMock::new();

        let mut dev = ShiftRegister::<2, _, _, _, _>::new(
            spi_mock.clone(),
            oe_mock.clone(),
            latch_mock.clone(),
            delay_mock,
        );

        dev.data = [0xff, 0x12];
        dev.clear();

        assert_eq!(dev.data, [0u8, 0u8]);

        spi_mock.done();
        oe_mock.done();
        latch_mock.done();
    }

    #[test]
    /// Get a specific output
    fn test_get_output() {
        let mut spi_mock: SpiMock<u8> = SpiMock::new(&[]);
        let mut oe_mock = PinMock::new(&[]);
        let mut latch_mock = PinMock::new(&[]);
        let delay_mock = DelayMock::new();

        // Init with N=2 -> 16 output bits available
        let mut dev = ShiftRegister::<2, _, _, _, _>::new(
            spi_mock.clone(),
            oe_mock.clone(),
            latch_mock.clone(),
            delay_mock,
        );

        //      farthest , nearest
        dev.data = [0x81, 0x13];

        assert!(dev.get_output(0).unwrap()); // nearest
        assert!(dev.get_output(1).unwrap());
        assert!(!dev.get_output(2).unwrap());
        assert!(dev.get_output(8).unwrap());
        assert!(!dev.get_output(9).unwrap());
        assert!(!dev.get_output(12).unwrap());
        assert!(dev.get_output(15).unwrap()); // farthest

        // out of bounds error
        let err = dev.get_output(16).unwrap_err();
        assert!(matches!(err, Error::IndexOutOfBounds));

        spi_mock.done();
        oe_mock.done();
        latch_mock.done();
    }

    #[test]
    /// Set a specific output
    fn test_set_output() {
        let mut spi_mock: SpiMock<u8> = SpiMock::new(&[]);
        let mut oe_mock = PinMock::new(&[]);
        let mut latch_mock = PinMock::new(&[]);
        let delay_mock = DelayMock::new();

        // Init with N=2 -> 16 output bits available
        let mut dev = ShiftRegister::<2, _, _, _, _>::new(
            spi_mock.clone(),
            oe_mock.clone(),
            latch_mock.clone(),
            delay_mock,
        );
        dev.set_output(0, true).unwrap();
        dev.set_output(1, true).unwrap();
        dev.set_output(4, true).unwrap();
        dev.set_output(8, true).unwrap();
        dev.set_output(15, true).unwrap();
        assert_eq!(dev.data, [0x81, 0x13]);

        dev.set_output(1, false).unwrap();
        dev.set_output(8, false).unwrap();
        assert_eq!(dev.data, [0x80, 0x11]);

        // out of bounds error
        let err = dev.set_output(16, true).unwrap_err();
        assert!(matches!(err, Error::IndexOutOfBounds));

        spi_mock.done();
        oe_mock.done();
        latch_mock.done();
    }

    #[test]
    /// Tests that the output bin is enabled correctly
    fn test_enable_outputs() {
        // case 1: disable outputs
        {
            let mut spi: SpiMock<u8> = SpiMock::new(&[]);
            let mut latch_mock = PinMock::new(&[]);
            let delay_mock = DelayMock::new();

            // expect oe to go high (disable outputs)
            let mut oe_mock = PinMock::new(&[PinTransaction::set(State::High)]);

            let mut dev = ShiftRegister::<1, _, _, _, _>::new(
                spi.clone(),
                oe_mock.clone(),
                latch_mock.clone(),
                delay_mock,
            );

            dev.enable_output(false).unwrap();

            spi.done();
            oe_mock.done();
            latch_mock.done();
        }
        // case 2: enable outputs
        {
            let mut spi: SpiMock<u8> = SpiMock::new(&[]);
            let mut latch_mock = PinMock::new(&[]);
            let delay_mock = DelayMock::new();

            // expect oe to go low (enable outputs)
            let mut oe_mock = PinMock::new(&[PinTransaction::set(State::Low)]);

            let mut dev = ShiftRegister::<1, _, _, _, _>::new(
                spi.clone(),
                oe_mock.clone(),
                latch_mock.clone(),
                delay_mock,
            );

            dev.enable_output(true).unwrap();

            spi.done();
            oe_mock.done();
            latch_mock.done();
        }
    }

    #[test]
    /// Tests that the LATCH pin goes high and then low. Does NOT concern the delay in between
    fn test_latch() {
        let mut spi_mock: SpiMock<u8> = SpiMock::new(&[]);
        let mut oe_mock = PinMock::new(&[]);
        let mut delay_mock = CheckedDelay::new(&[
           DelayTransaction::delay_ns(100), 
        ]);

        // expect latch to go high and then low
        let mut latch_mock = PinMock::new(&[
            PinTransaction::set(State::High),
            PinTransaction::set(State::Low),
        ]);

        let mut dev = ShiftRegister::<1, _, _, _, _>::new(
            spi_mock.clone(),
            oe_mock.clone(),
            latch_mock.clone(),
            delay_mock.clone(),
        );

        dev.latch().unwrap();

        spi_mock.done();
        oe_mock.done();
        latch_mock.done();
        delay_mock.done();
    }

    #[test]
    /// Tests writing of all outputs via SPI (can't simulate bus errors)
    fn test_write_all() {
        let mut oe_mock = PinMock::new(&[]);
        let delay_mock = DelayMock::new();

        let expectations = [
            SpiTransaction::transaction_start(),
            SpiTransaction::write_vec(std::vec![0x33, 0x22, 0x11]),
            SpiTransaction::transaction_end(),
        ];

        let mut spi_mock = SpiMock::new(&expectations);
        // expect latch to go high and then low
        let mut latch_mock = PinMock::new(&[
            PinTransaction::set(State::High),
            PinTransaction::set(State::Low),
        ]);

        let mut dev = ShiftRegister::<3, _, _, _, _>::new(
            spi_mock.clone(),
            oe_mock.clone(),
            latch_mock.clone(),
            delay_mock,
        );

        dev.data = [0x33, 0x22, 0x11];

        dev.write_all().unwrap();

        spi_mock.done();
        oe_mock.done();
        latch_mock.done();
    }

    #[test]
    /// Tests writing of a single output via SPI without touching the others
    fn test_write_output() {
        {
            let mut oe_mock = PinMock::new(&[]);
            let delay_mock = DelayMock::new();

            let expectations = [
                SpiTransaction::transaction_start(),
                SpiTransaction::write_vec(std::vec![0x00, 0x01, 0x00]),
                SpiTransaction::transaction_end(),
            ];

            let mut spi_mock = SpiMock::new(&expectations);
            // expect latch to go high and then low
            let mut latch_mock = PinMock::new(&[
                PinTransaction::set(State::High),
                PinTransaction::set(State::Low),
            ]);

            let mut dev = ShiftRegister::<3, _, _, _, _>::new(
                spi_mock.clone(),
                oe_mock.clone(),
                latch_mock.clone(),
                delay_mock,
            );

            dev.write_output(8, true).unwrap();

            spi_mock.done();
            oe_mock.done();
            latch_mock.done();
        }
        {
            let mut oe_mock = PinMock::new(&[]);
            let delay_mock = DelayMock::new();

            let expectations = [
                SpiTransaction::transaction_start(),
                SpiTransaction::write_vec(std::vec![0xFF, 0xFE, 0xFF]),
                SpiTransaction::transaction_end(),
            ];

            let mut spi_mock = SpiMock::new(&expectations);
            // expect latch to go high and then low
            let mut latch_mock = PinMock::new(&[
                PinTransaction::set(State::High),
                PinTransaction::set(State::Low),
            ]);

            let mut dev = ShiftRegister::<3, _, _, _, _>::new(
                spi_mock.clone(),
                oe_mock.clone(),
                latch_mock.clone(),
                delay_mock,
            );
            
            dev.data = [0xFF, 0xFF, 0xFF];
            dev.write_output(8, false).unwrap();

            spi_mock.done();
            oe_mock.done();
            latch_mock.done();
        }
    }
}
