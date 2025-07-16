# Programmable ADC RTL Implementation

## Overview

This directory contains the RTL implementation of the Programmable ADC following Vyges conventions. The design implements a high-performance, ultra-low-power analog-to-digital converter with configurable resolution (12, 14, 16 bits), 3 simultaneous differential channels, and integrated PGA (gains 1,2,3,4).

## Architecture

The ADC uses a Successive Approximation Register (SAR) architecture with the following key components:

```
                    ┌─────────────────┐
                    │   PGA Stage     │
                    │  (Gain 1,2,3,4) │
                    └─────────┬───────┘
                              │
                    ┌─────────▼───────┐
                    │   Sample &      │
                    │   Hold (S/H)    │
                    └─────────┬───────┘
                              │
                    ┌─────────▼───────┐
                    │   SAR Logic     │
                    │   Controller    │
                    └─────────┬───────┘
                              │
                    ┌─────────▼───────┐
                    │   DAC Array     │
                    │   (12/14/16bit) │
                    └─────────┬───────┘
                              │
                    ┌─────────▼───────┐
                    │   Comparator    │
                    └─────────────────┘
```

## File Structure

### RTL Modules

| File | Module | Description |
|------|--------|-------------|
| `programmable_adc_top.sv` | `programmable_adc_top` | Top-level module with all interfaces |
| `apb_interface.sv` | `apb_interface` | APB slave interface with register map |
| `pga_stage.sv` | `pga_stage` | Programmable Gain Amplifier (1,2,3,4) |
| `sample_hold.sv` | `sample_hold` | Sample and Hold circuit |
| `sar_controller.sv` | `sar_controller` | SAR logic controller |
| `dac_array.sv` | `dac_array` | Binary-weighted capacitor DAC |
| `comparator.sv` | `comparator` | Dynamic latch comparator |

### Key Features

- **Resolution**: Programmable 12, 14, 16 bits
- **Channels**: 3 simultaneous differential channels
- **PGA**: Integrated with gains 1, 2, 3, 4
- **Interface**: APB slave interface
- **Performance**: 5 MSPS conversion rate
- **Linearity**: DNL < 0.5 LSB, INL < 1 LSB
- **Power**: < 10 mW at 5MSPS

## Module Descriptions

### programmable_adc_top

Top-level module that instantiates all sub-modules and provides the complete ADC interface.

**Key Interfaces:**
- APB slave interface for control and data
- 3 differential analog input channels
- Power supply and reference voltage inputs
- Status and interrupt outputs

### apb_interface

APB slave interface with complete register map implementation.

**Registers:**
- `0x00`: Control Register (R/W)
- `0x04`: Status Register (RO)
- `0x08`: Data Register (RO)
- `0x0C`: Configuration Register (R/W)

### pga_stage

Programmable Gain Amplifier with configurable gains of 1, 2, 3, and 4.

**Features:**
- Switched capacitor architecture
- Bandwidth > 2 MHz
- Noise < 3 mV RMS
- Power < 2 mW

### sample_hold

Track and Hold circuit using switched capacitor architecture.

**Specifications:**
- Hold time > 200 ns
- Droop rate < 1 LSB/μs
- Aperture jitter < 1 ps RMS

### sar_controller

Successive Approximation Register controller for ADC conversion.

**Features:**
- Configurable resolution (12, 14, 16 bits)
- Conversion time: 200 ns (5 MSPS)
- Power < 3 mW
- Auto-conversion mode support

### dac_array

Binary-weighted capacitor array DAC for SAR ADC.

**Features:**
- Split-capacitor architecture for 16-bit
- Matching < 0.1% for critical capacitors
- Optimized for 40nm process

### comparator

Dynamic latch comparator for SAR ADC.

**Specifications:**
- Resolution < 1 mV
- Speed < 10 ns decision time
- Power < 1 mW

## Usage

### Basic Operation

1. **Power-up Sequence:**
   ```verilog
   // Apply power supplies
   VDDA = 2.8V;
   VREF = 2.8V;
   VCM = 1.4V;
   
   // Release reset
   PRESETn = 1;
   ```

2. **Configuration:**
   ```verilog
   // Enable ADC with 16-bit resolution, Gain=1, Channel 0
   apb_write(0x00, 32'h00010000 | (2'b10 << 20) | (2'b00 << 22) | (2'b00 << 18));
   ```

3. **Start Conversion:**
   ```verilog
   // Start single conversion
   apb_write(0x00, 32'h00020000);
   ```

4. **Read Result:**
   ```verilog
   // Wait for conversion complete
   while (busy_o);
   while (!valid_o);
   
   // Read conversion result
   data = data_o;
   ```

### Register Configuration

#### Control Register (0x00)
```
[23:22] PGA_GAIN[1:0] - PGA Gain Selection
        00: Gain = 1
        01: Gain = 2  
        10: Gain = 3
        11: Gain = 4

[21:20] RESOLUTION[1:0] - ADC Resolution
        00: 12-bit
        01: 14-bit
        10: 16-bit
        11: Reserved

[19:18] CHANNEL_SEL[1:0] - Channel Selection
        00: Channel 0
        01: Channel 1
        10: Channel 2
        11: Reserved

[17]    START_CONV - Start Conversion (auto-clear)
[16]    ENABLE - ADC Enable
```

#### Configuration Register (0x0C)
```
[7]     IRQ_EN - Interrupt Enable
[6]     AUTO_MODE - Auto Conversion Mode
```

## Simulation

### Running Tests

```bash
# Navigate to testbench directory
cd ../tb

# Run simulation with VCS
make sim-vcs

# Run simulation with Verilator
make sim-verilator

# Run simulation with Icarus Verilog
make sim-iverilog

# Run all tests
make regression
```

### Test Coverage

The testbench includes comprehensive testing for:
- Basic functionality
- All resolution modes (12, 14, 16-bit)
- All PGA gains (1, 2, 3, 4)
- Multi-channel operation
- Linearity testing (DNL/INL)
- Performance verification

## Synthesis

### Target Technology

- **Technology**: 40nm Ultra Low Power
- **Supply Voltage**: 2.8V (analog), 1.8V (digital)
- **Temperature Range**: -40°C to +125°C

### Synthesis Commands

```bash
# Run synthesis
make synth

# Check timing
make timing

# Generate netlist
make netlist
```

## Verification

### Functional Verification

- **RTL Simulation**: Complete testbench with coverage
- **Formal Verification**: Protocol compliance checking
- **Timing Analysis**: All paths closed at 50 MHz

### Performance Verification

- **DNL/INL**: < 0.5 LSB, < 1 LSB respectively
- **SNR**: > 70 dB (16-bit mode)
- **Power**: < 10 mW at 5MSPS
- **Conversion Time**: 200 ns

## Integration Guidelines

### Power Supply Requirements

- **VDDA**: 2.8V ±5% (analog supply)
- **VREF**: 2.8V ±1% (reference voltage)
- **VCM**: 1.4V ±2% (common mode)
- **VDD**: 1.8V ±5% (digital supply)

### Clock Requirements

- **PCLK**: 50 MHz ±1%
- **Duty Cycle**: 45% - 55%
- **Jitter**: < 1 ps RMS

### Layout Considerations

- Separate analog and digital power domains
- Shielded routing for analog signals
- Proper grounding strategy
- Thermal management

## Troubleshooting

### Common Issues

1. **No Conversion Data**
   - Check ADC enable bit
   - Verify power supply voltages
   - Check clock and reset signals

2. **Poor Linearity**
   - Verify PGA gain setting
   - Check input signal levels
   - Ensure proper reference voltage

3. **High Power Consumption**
   - Reduce sample rate
   - Use lower resolution mode
   - Check temperature conditions

## Documentation

For detailed documentation, see:
- `../docs/programmable_adc_design_spec.md` - Complete design specification
- `../docs/user_manual.md` - User manual with examples
- `../docs/integration_guide.md` - Integration guidelines

## Support

For technical support or questions:
- Email: dev@vyges.com
- Documentation: https://vyges.com/catalog/programmable-adc
- Issues: GitHub repository issues

## License

This RTL implementation is licensed under Apache-2.0. See `../LICENSE` for details. 