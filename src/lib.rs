#![no_std]
#![warn(missing_docs)]

//! An embedded driver for TPIC6B595 shift registers. To save pins /SRCLR is not used, clearing is
//! done by shifting zeroes through all devices

use embedded_hal::digital::{OutputPin, PinState};

struct ShiftRegister<OE, SER, CLK, LATCH> {
    /// Output enable (Pin /G)
    not_oe: OE,
    /// Serial data (Pin SER IN)
    ser: SER,
    /// Serial clock (Pin CRCLK)
    clk: CLK,
    /// Latch (Pin RCK)
    latch: LATCH,
}

impl<OE, SER, CLK, LATCH> ShiftRegister<OE, SER, CLK, LATCH>
where
    OE: OutputPin,
    SER: OutputPin,
    CLK: OutputPin,
    LATCH: OutputPin,
{
    pub fn new(not_oe: OE, serial_data: SER, serial_clock: CLK, latch: LATCH) -> Self {
        ShiftRegister {
            not_oe,
            ser: serial_data,
            clk: serial_clock,
            latch,
        }
    }

    pub fn output_enable(&mut self, enable: bool) -> Result<(), OE::Error> {
        self.not_oe.set_state(PinState::from(!enable))
    }
}


// Description from the datasheet, for reference while implementing....
//
// This device contains an 8-bit serial-in, parallel-out
// shift register that feeds an 8-bit D-type storage
// register. Data transfers through the shift and storage
// registers on the rising edge of the shift-register clock
// (SRCK) and the register clock (RCK), respectively.
// The storage register transfers data to the output buffer
// when shift-register clear ( SRCLR) is high. Write data
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
