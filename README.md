# TPIC6B595

An `embedded-hal` driver for the TPIC6B595 Shift Register

This crate provides an `embedded-hal` compatible driver for the TPIC6B595 power shift register. It supports daisy-chaining multiple devices to expand output capabilities. The driver is designed for `no_std` environments, making it suitable for bare-metal embedded applications.

## Features

*   `no_std` compatible.
*   Uses `embedded-hal` v1.0 traits for SPI, OutputPin, and DelayNs.
*   Supports daisy-chaining multiple TPIC6B595 devices (parameterized by `N`).
*   Functions for setting and getting individual output states by index.
*   Ability to clear all outputs.
*   Global Output Enable via (`/G`) pin.
*   Handles internal data buffering and SPI communication.

## Limitation

* takes ownership of the SPI Device, so no bus sharing possible at the moment

## Connections

*   `SPI_MOSI`: Connect to TPIC6B595 `SER IN` (Serial Data Input).
*   `SPI_CLK`: Connect to TPIC6B595 `SRCLK` (Shift Register Clock).
*   `LATCH` pin: Connect to TPIC6B595 `RCK` (Storage Register Clock). This pin is pulsed high-low to transfer the shift register contents to the storage register (outputs).
*   `/OE` (Output Enable) pin: Connect to TPIC6B595 `/G`. Active low; pull low to enable outputs, high to disable.
*   `/SRCLR`: **This driver does not use the `/SRCLR` pin.** It should be tied to VCC on your hardware. Clearing is performed by shifting all zeroes through the SPI interface.

## Note on Data Ordering

When daisy-chaining, the internal data buffer `data: [u8; N]` in the `ShiftRegister` struct expects data such that `data[N-1]` corresponds to the first shift register in the chain (closest to the `SER IN` input), `data[N-2]` to the second, and so on, with `data[0]` being the last shift register in the chain. The `set_output` and `get_output` methods handle this ordering automatically based on a single linear index `0` to `(N*8)-1`.

```text
     data[N-1]         data[N-2]    ...     data[0]   
    ┌────────────────┌────────────────┌────────────────┐
    │      SR 1      │      SR 2      │      SR N      │
    │0 1 2 3 4 5 6 7 │0 1 2 3 4 5 6 7 │0 1 2 3 4 5 6 7 │
    └────────────────└────────────────└────────────────┘
idx  0 1 2 3 4 5 6 7  8 9  ...                      (N*8)-1
```

## Usage

Add the following to your `Cargo.toml` dependencies:

````toml
# filepath: Cargo.toml
[dependencies]
tpic6b595-driver = "0.1.0"
embedded-hal = "1.0" 
````

### Example for STM32F4xx:

```rust

let p = pac::Peripherals::take().unwrap();
let cp = cortex_m::Peripherals::take().unwrap();

let mut rcc = p
    .RCC
    .freeze(Config::hsi().sysclk(100.MHz()));

let mut systick = cp.SYST.delay(&rcc.clocks);

let gpiod = p.GPIOD.split(&mut rcc);
let mut led = gpiod.pd14.into_push_pull_output();

// Shift register resources
let gpioc = p.GPIOC.split(&mut rcc);
let not_oe = gpioc.pc6.into_push_pull_output();
let latch = gpioc.pc7.into_push_pull_output();
let delay = p.TIM5.delay_us(&mut rcc);

// SPI1 Config
// SCK: PB3 / AF5
// MISO: NOT USED
// MOSI: PB5 / AF5
// CS: PB4
let gpiob = p.GPIOB.split(&mut rcc);
let sck = gpiob
    .pb3
    .into_alternate::<5>()
    .speed(Speed::VeryHigh)
    .internal_pull_up(true);
let mosi = gpiob
    .pb5
    .into_alternate::<5>()
    .speed(Speed::VeryHigh)
    .internal_pull_up(true);
let cs = dummy_pin::DummyPin::new_high();  // use crate dummy-pin

let mode = Mode {
    polarity: Polarity::IdleLow,
    phase: Phase::CaptureOnFirstTransition,
};
let spi_driver = Spi::new(
    p.SPI1,
    (Some(sck), pac::SPI1::NoMiso, Some(mosi)),
    mode,
    400.kHz(),
    &mut rcc,
);

// use crate embedded_hal_bus for SpiDevice trait
let spi_device = embedded_hal_bus::spi::ExclusiveDevice::new_no_delay(spi_driver, cs).unwrap();


// Create the ShiftRegister (2 daisy chained devices)
let mut shift_register = ShiftRegister::<2, _, _, _, _>::new(spi_device, not_oe, latch, delay);

// Only set internal state
shift_register.set_output(0, true);
shift_register.set_output(12, true);

// Write to device
if shift_register.write_output(13, true).is_err() {
    defmt::println!("Error write_output");
}

```
