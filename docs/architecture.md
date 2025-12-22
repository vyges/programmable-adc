# Architecture: Programmable ADC IP

## Overview

This document describes the internal architecture, interfaces, and design details of the Programmable ADC IP block. The ADC implements a Successive Approximation Register (SAR) architecture with configurable resolution (12, 14, 16 bits), 3 simultaneous differential channels, and an integrated Programmable Gain Amplifier (PGA) with gains of 1, 2, 3, and 4.

**Key Features:**
- SAR ADC architecture with 5 MSPS conversion rate
- Programmable resolution: 12, 14, or 16 bits
- 3 differential input channels with channel multiplexing
- Integrated PGA with gains: 1x, 2x, 3x, 4x
- APB4 slave interface for control and data access
- Ultra-low-power design (< 10 mW at 5 MSPS)
- Excellent linearity: DNL < 0.5 LSB, INL < 1 LSB

## Top-Level Block Diagram

```
                    ┌─────────────────────────────────────────┐
                    │         Programmable ADC                │
                    │                                         │
    ┌───────────────┤  APB Interface                          │
    │ PCLK          │  (programmable_adc_apb_interface)      │
    │ PRESETn       │                                         │
    │ PADDR[7:0]    │  ┌─────────────────────────────────┐   │
    │ PWDATA[31:0]  │  │ Register Map:                   │   │
    │ PENABLE       │  │ 0x00: Control Register          │   │
    │ PWRITE        │  │ 0x04: Status Register           │   │
    │ PSEL          │  │ 0x08: Data Register             │   │
    └───────────────┤  │ 0x0C: Configuration Register    │   │
                    │  └─────────────────────────────────┘   │
    ┌───────────────┤                                         │
    │ VIN0P/N       │  ┌─────────────────────────────────┐   │
    │ VIN1P/N       │  │ Channel Multiplexer             │   │
    │ VIN2P/N       │  │ (Selects channel 0, 1, or 2)   │   │
    └───────────────┤  └───────────┬─────────────────────┘   │
                    │              │                          │
    ┌───────────────┤  ┌──────────▼─────────────────────┐   │
    │ VREF, VCM     │  │ PGA Stage                       │   │
    │ VDDA, VSSA    │  │ (programmable_adc_pga_stage)    │   │
    └───────────────┤  │ Gain: 1x, 2x, 3x, 4x            │   │
                    │  └───────────┬─────────────────────┘   │
    ┌───────────────┤              │                          │
    │ adc_irq       │  ┌───────────▼─────────────────────┐   │
    │ busy_o        │  │ Sample & Hold                    │   │
    │ valid_o       │  │ (programmable_adc_sample_hold)   │   │
    │ data_o[15:0] │  │ Track/Hold circuit               │   │
    │ channel_o[1:0]│  └───────────┬─────────────────────┘   │
    └───────────────┤              │                          │
                    │  ┌───────────▼─────────────────────┐   │
                    │  │ SAR Controller                  │   │
                    │  │ (programmable_adc_sar_controller)│   │
                    │  │ Successive Approximation Logic  │   │
                    │  └───────┬──────────────┬──────────┘   │
                    │          │              │               │
                    │  ┌───────▼──────┐  ┌───▼────────────┐  │
                    │  │ DAC Array     │  │ Comparator     │  │
                    │  │ (programmable │  │ (programmable  │  │
                    │  │  _adc_dac_    │  │  _adc_         │  │
                    │  │  array)       │  │  comparator)   │  │
                    │  │ 12/14/16-bit  │  │ Dynamic latch  │  │
                    │  └───────────────┘  └────────────────┘  │
                    └─────────────────────────────────────────┘
```

## Detailed Architecture

### 1. APB Interface Module (`programmable_adc_apb_interface`)

The APB interface module implements the APB4 slave protocol and provides register-based control and data access.

**Key Functions:**
- APB protocol compliance (PSEL, PENABLE, PWRITE, PREADY)
- Register map implementation
- Control signal generation for ADC operation
- Status and data register management
- Interrupt enable/disable control

**Register Map:**

| Address | Name | Access | Description |
|---------|------|--------|-------------|
| `0x00` | `CONTROL` | R/W | Control register: Enable, Resolution, Channel, PGA Gain, Start Conversion |
| `0x04` | `STATUS` | RO | Status register: Busy, Valid, Channel, Error flags |
| `0x08` | `DATA` | RO | Data register: Latest conversion result (12/14/16-bit) |
| `0x0C` | `CONFIG` | R/W | Configuration register: IRQ Enable, Auto Mode, Power Management |

**Control Register (0x00) Bit Fields:**
```
[31:24] Reserved
[23:22] PGA_GAIN[1:0]    - PGA gain selection (00=1x, 01=2x, 10=3x, 11=4x)
[21:20] RESOLUTION[1:0]  - ADC resolution (00=12-bit, 01=14-bit, 10=16-bit)
[19:18] CHANNEL_SEL[1:0] - Channel selection (00=Ch0, 01=Ch1, 10=Ch2)
[17]    START_CONV       - Start conversion (auto-clears)
[16]    ENABLE           - ADC enable
[15:0]  Reserved
```

### 2. Channel Multiplexer

The channel multiplexer selects one of the three differential input channels based on the `CHANNEL_SEL` control signal from the APB interface.

**Input Channels:**
- Channel 0: VIN0P, VIN0N
- Channel 1: VIN1P, VIN1N
- Channel 2: VIN2P, VIN2N

**Operation:**
- Channel selection is synchronous with the conversion start
- Selected channel remains active for the entire conversion cycle
- Channel switching occurs only when a new conversion is started

### 3. PGA Stage (`programmable_adc_pga_stage`)

The Programmable Gain Amplifier amplifies the selected differential input signal before sampling.

**Features:**
- Configurable gains: 1x, 2x, 3x, 4x
- Switched capacitor architecture
- Bandwidth: > 2 MHz (sufficient for 1 MHz input signal)
- Noise: < 3 mV RMS
- Power: < 2 mW

**Gain Selection:**
- Gain is set via APB control register
- Gain change takes effect on next conversion
- All gains maintain differential operation

### 4. Sample & Hold (`programmable_adc_sample_hold`)

The Sample & Hold circuit captures the amplified input signal and holds it stable during the SAR conversion process.

**Specifications:**
- Track mode: Samples input signal
- Hold mode: Maintains sampled value during conversion
- Hold time: > 200 ns (sufficient for 16-bit conversion)
- Droop rate: < 1 LSB/μs
- Aperture jitter: < 1 ps RMS

**Operation:**
- Switched capacitor architecture
- Sample enable controlled by SAR controller
- Differential output maintains common mode rejection

### 5. SAR Controller (`programmable_adc_sar_controller`)

The SAR controller implements the successive approximation algorithm to determine the digital representation of the analog input.

**Features:**
- Configurable resolution: 12, 14, or 16 bits
- Conversion time: 200 ns (5 MSPS)
- Auto-conversion mode support
- Power: < 3 mW

**SAR Algorithm:**
1. Start with MSB (bit 15 for 16-bit mode)
2. Set DAC to mid-scale (0x8000)
3. Compare held input with DAC output
4. If input > DAC: set bit to 1, else set to 0
5. Move to next bit and repeat
6. Continue until LSB is determined

**State Machine:**
- IDLE: Waiting for start signal
- SAMPLE: Initiating sample & hold
- CONVERT: Performing SAR conversion (12/14/16 cycles)
- VALID: Conversion complete, data ready

### 6. DAC Array (`programmable_adc_dac_array`)

The DAC array generates the reference voltage for comparison during SAR conversion.

**Architecture:**
- Binary-weighted capacitor array
- Split-capacitor architecture for 16-bit mode
- Capacitor matching: < 0.1% for critical capacitors
- Optimized for 40nm process

**Operation:**
- Receives SAR controller data word
- Generates differential output (DAC_OUT_P, DAC_OUT_N)
- Reference voltage: VREF (2.8V)
- Common mode: VCM (1.4V)

### 7. Comparator (`programmable_adc_comparator`)

The comparator compares the held input signal with the DAC output to determine each bit during SAR conversion.

**Specifications:**
- Type: Dynamic latch comparator
- Resolution: < 1 mV
- Decision time: < 10 ns
- Power: < 1 mW

**Operation:**
- Compares differential inputs: (SH_OUT_P - SH_OUT_N) vs (DAC_OUT_P - DAC_OUT_N)
- Output: 1 if input > DAC, 0 otherwise
- Latched output for SAR controller

## Data Flow

### Conversion Sequence

1. **Configuration Phase:**
   - Software configures ADC via APB (resolution, channel, PGA gain)
   - ADC enable bit is set
   - Start conversion bit is asserted

2. **Sampling Phase:**
   - Channel multiplexer selects configured channel
   - PGA amplifies the differential input
   - Sample & Hold circuit tracks the amplified signal
   - SAR controller initiates hold

3. **Conversion Phase:**
   - SAR controller performs successive approximation
   - For each bit (MSB to LSB):
     - DAC generates reference voltage
     - Comparator compares input vs DAC
     - SAR controller updates bit value
   - Conversion completes after 12, 14, or 16 cycles

4. **Data Output Phase:**
   - SAR controller sets valid flag
   - Conversion data available in data register
   - Interrupt generated (if enabled)
   - Status register updated

## Control Flow

### State Machine (SAR Controller)

```
     IDLE
      │
      │ start_conv = 1
      ▼
   SAMPLE ──────┐
      │         │
      │         │ (sample_en)
      ▼         │
    HOLD        │
      │         │
      │         │
      ▼         │
  CONVERT ──────┘
      │
      │ (all bits done)
      ▼
    VALID
      │
      │ (read or new start)
      ▼
     IDLE
```

### Timing Diagram

```
PCLK:     __/‾\__/‾\__/‾\__/‾\__/‾\__/‾\__/‾\__/‾\__/‾\__/‾\__
          

START:    ____/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾

SAMPLE:   ________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾

BUSY:     ________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾

VALID:    ________________________________/‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾‾

DATA:     _______________________________<=====16-bit result=====>
```

## Power Domains

### Analog Domain
- **Supply**: VDDA = 2.8V (40nm) / 5.0V (Sky130)
- **Ground**: VSSA = 0V
- **Modules**: PGA, Sample & Hold, DAC Array, Comparator
- **Reference**: VREF = VDDA, VCM = VDDA/2

### Digital Domain
- **Supply**: VDDD = 1.8V (40nm) / 1.8V (Sky130)
- **Ground**: VSSD = 0V
- **Modules**: APB Interface, SAR Controller, Control Logic
- **Clock**: PCLK (50 MHz)

### Power Management
- ADC can be disabled to save power
- Individual module enable/disable (future enhancement)
- Power consumption: < 10 mW at 5 MSPS

## Clock Domains

### Single Clock Domain Design
- **Clock**: PCLK (50 MHz APB clock)
- All digital logic operates on PCLK
- Analog circuits use PCLK for sampling and control
- No clock domain crossing required

### Clock Requirements
- Frequency: 50 MHz ±1%
- Duty cycle: 45% - 55%
- Jitter: < 1 ps RMS
- Skew: < 100 ps

## Interface Summary

### APB Interface (Input)
- **PCLK**: APB clock (50 MHz)
- **PRESETn**: APB reset (active low)
- **PADDR[7:0]**: Address bus
- **PWDATA[31:0]**: Write data
- **PENABLE**: Enable signal
- **PWRITE**: Write enable
- **PSEL**: Select signal

### APB Interface (Output)
- **PRDATA[31:0]**: Read data
- **PREADY**: Ready signal

### Analog Interface (Input)
- **VIN0P, VIN0N**: Channel 0 differential input
- **VIN1P, VIN1N**: Channel 1 differential input
- **VIN2P, VIN2N**: Channel 2 differential input
- **VREF**: Reference voltage (2.8V)
- **VCM**: Common mode voltage (1.4V)
- **VDDA**: Analog supply (2.8V)
- **VSSA**: Analog ground

### Status Interface (Output)
- **adc_irq**: Interrupt output (conversion complete)
- **busy_o**: Conversion busy indicator
- **valid_o**: Data valid indicator
- **data_o[15:0]**: Conversion result
- **channel_o[1:0]**: Current channel number

## Module Interconnections

```
programmable_adc (top-level)
├── programmable_adc_apb_interface
│   ├── Control outputs: pga_gain, resolution, channel_sel, start_conv, adc_enable, irq_enable, auto_mode
│   └── Status inputs: adc_data, busy, valid
│
├── Channel Multiplexer (combinational)
│   ├── Inputs: VIN0P/N, VIN1P/N, VIN2P/N, channel_sel
│   └── Outputs: selected_in_p, selected_in_n
│
├── programmable_adc_pga_stage
│   ├── Inputs: selected_in_p/n, gain, enable
│   └── Outputs: pga_out_p, pga_out_n
│
├── programmable_adc_sample_hold
│   ├── Inputs: pga_out_p/n, sample_en, enable
│   └── Outputs: sh_out_p, sh_out_n
│
├── programmable_adc_sar_controller
│   ├── Inputs: start_conv, resolution, auto_mode, comp_out, enable
│   ├── Outputs: sar_data, sar_busy, sar_valid, dac_control
│   └── Controls: sample_en (to S/H)
│
├── programmable_adc_dac_array
│   ├── Inputs: sar_data, resolution, vref, vcm, enable
│   └── Outputs: dac_out_p, dac_out_n
│
└── programmable_adc_comparator
    ├── Inputs: sh_out_p/n, dac_out_p/n, enable
    └── Output: comp_out (to SAR controller)
```

## Design Considerations

### Linearity
- DNL < 0.5 LSB achieved through careful capacitor matching
- INL < 1 LSB through split-capacitor architecture
- Common mode rejection maintained throughout signal path

### Power Optimization
- Switched capacitor circuits reduce static power
- Clock gating for inactive modules (future enhancement)
- Low-power comparator design
- Optimized DAC switching sequence

### Noise Management
- Separate analog and digital power domains
- Shielding for sensitive analog signals
- Proper grounding strategy
- Low-noise reference voltage distribution

### Timing Constraints
- Sample & Hold aperture time: < 1 ps jitter
- Comparator decision time: < 10 ns
- SAR conversion: 12/14/16 cycles at 50 MHz = 240/280/320 ns
- Total conversion time: ~200 ns (including overhead)

## Technology Support

### 40nm Ultra Low Power
- Analog supply: 2.8V
- Digital supply: 1.8V
- Reference voltage: 2.8V
- Common mode: 1.4V

### Sky130 Open-Source PDK
- Analog supply: 5.0V
- Digital supply: 1.8V
- Reference voltage: 5.0V
- Common mode: 2.5V

## Future Enhancements

- Multi-channel simultaneous conversion
- Additional PGA gain options
- Built-in calibration routines
- Power-down modes
- Clock gating for power savings
- Enhanced error detection and reporting
