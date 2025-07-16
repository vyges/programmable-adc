# Programmable ADC - Cadence PDK Implementation

## Overview

This directory contains the complete Cadence PDK implementation of the Programmable ADC IP, including Spectre simulation support, Virtuoso schematic capture, and LVS verification capabilities.

## Directory Structure

```
rtl/cadence_pdk/
├── README.md                    # This file
├── models.scs                   # Spectre device models for 40nm ULP
├── corners.scs                  # Process corners (TT, FF, SS, FS, SF)
├── programmable_adc_spectre.sp  # Main Spectre netlist
├── programmable_adc_lvs.sp      # LVS-compatible netlist
├── virtuoso_schematic.cds       # Virtuoso schematic capture file
├── lvs_setup.tcl               # LVS setup and execution script
└── Makefile                    # Build and simulation automation
```

## Features

### ✅ Spectre Simulation Support
- Complete behavioral models for all ADC blocks
- 40nm Ultra-Low-Power technology models
- Multiple process corners support
- Transient, DC, and AC analysis capabilities

### ✅ Virtuoso Schematic Capture
- Hierarchical schematic design
- Device-level circuit implementation
- Parameterized component models
- Schematic-to-layout flow ready

### ✅ LVS Verification
- Layout vs. Schematic verification setup
- Calibre LVS integration
- Comprehensive device mapping
- Tolerance and filter configuration

### ✅ Circuit Implementation
- **PGA (Programmable Gain Amplifier)**: Chopper-stabilized differential amplifier
- **Sample & Hold**: High-precision sampling circuit
- **SAR DAC**: 16-bit capacitor array DAC
- **Comparator**: Multi-stage comparator with latch

## Quick Start

### 1. Spectre Simulation

```bash
# Run Spectre simulation
make spectre_sim

# Run with specific corner
make spectre_sim CORNER=ff

# Run AC analysis
make spectre_ac

# Run DC sweep
make spectre_dc
```

### 2. LVS Verification

```bash
# Generate LVS runset
make lvs_runset

# Run LVS verification
make lvs_verify

# Check LVS results
make lvs_check
```

### 3. Virtuoso Integration

```bash
# Generate Virtuoso schematic
make virtuoso_schematic

# Extract layout netlist
make extract_layout
```

## Detailed Usage

### Spectre Simulation

The main Spectre netlist (`programmable_adc_spectre.sp`) includes:

- **Device Models**: 40nm ULP technology models
- **Process Corners**: TT, FF, SS, FS, SF
- **Analysis Types**: Transient, DC, AC
- **Test Stimuli**: Sine waves, pulses, ramps

#### Simulation Commands

```bash
# Basic transient simulation
spectre programmable_adc_spectre.sp

# Corner analysis
spectre -corner ff programmable_adc_spectre.sp

# Monte Carlo analysis
spectre -mc 100 programmable_adc_spectre.sp

# Temperature sweep
spectre -temp 125 programmable_adc_spectre.sp
```

#### Key Parameters

- **Supply Voltage**: 2.8V (typical), 2.5V-3.0V range
- **Temperature**: 27°C (typical), -40°C to 125°C
- **Clock Frequency**: 5MHz (SAR clock)
- **Chopper Frequency**: 500kHz
- **Input Range**: ±0.5V differential

### Virtuoso Schematic

The Virtuoso schematic (`virtuoso_schematic.cds`) provides:

- **Hierarchical Design**: Top-level and subcircuit schematics
- **Device Instances**: All transistors, capacitors, switches
- **Parameter Mapping**: Device sizes and properties
- **Wire Connections**: Complete signal routing

#### Schematic Features

- **PGA Circuit**: Chopper-stabilized differential amplifier
- **Sample & Hold**: High-precision sampling with hold capacitors
- **SAR DAC**: 16-bit binary-weighted capacitor array
- **Comparator**: Multi-stage comparator with output buffer

### LVS Verification

The LVS setup (`lvs_setup.tcl`) enables:

- **Device Mapping**: Schematic to layout device correspondence
- **Net Connectivity**: Signal path verification
- **Property Checking**: Device parameter validation
- **Hierarchical LVS**: Block-level verification

#### LVS Configuration

```tcl
# Device mapping
nmos_40nm -> nmos
pmos_40nm -> pmos
cap_40nm -> capacitor
res_40nm -> resistor

# Tolerances
Resistance: 1%
Capacitance: 5%
Voltage: 1mV
Current: 1nA
```

## Circuit Specifications

### PGA (Programmable Gain Amplifier)

- **Gain Range**: 1x to 16x (programmable)
- **Bandwidth**: 1MHz (typical)
- **Noise**: 10nV/√Hz input-referred
- **Offset**: <1mV (chopper-stabilized)
- **CMRR**: >80dB

### Sample & Hold

- **Sample Capacitance**: 10pF (differential)
- **Hold Capacitance**: 2pF (differential)
- **Switch Resistance**: 50Ω (on-state)
- **Hold Time**: >1ms
- **Droop Rate**: <1mV/ms

### SAR DAC

- **Resolution**: 16-bit
- **Capacitor Unit**: 1fF
- **Settling Time**: <100ns
- **DNL**: <0.5LSB
- **INL**: <1LSB

### Comparator

- **Offset**: <1μV (auto-zeroed)
- **Hysteresis**: 1μV
- **Delay**: <10ns
- **Power**: <1μW
- **Input Range**: Rail-to-rail

## Performance Metrics

### ADC Performance

- **Resolution**: 16-bit
- **Sampling Rate**: 100kSPS
- **ENOB**: 15.5 bits
- **SFDR**: >90dB
- **THD**: <-80dB
- **Power**: <1mW

### Power Consumption

- **PGA**: 200μW
- **Sample & Hold**: 50μW
- **SAR DAC**: 100μW
- **Comparator**: 50μW
- **Digital Logic**: 100μW
- **Total**: 500μW

## Integration Guidelines

### 1. Power Supply Requirements

```verilog
// Power supply connections
VDDA: 2.8V ±0.1V (analog supply)
VSSA: 0V (analog ground)
VDDD: 1.2V ±0.05V (digital supply)
VSSD: 0V (digital ground)
```

### 2. Clock Requirements

```verilog
// Clock specifications
clk: 5MHz ±1% (SAR clock)
chopper_clk: 500kHz ±5% (chopper clock)
duty_cycle: 50% ±5%
rise_time: <1ns
fall_time: <1ns
```

### 3. Input Interface

```verilog
// Input specifications
vin_p, vin_n: Differential input
input_range: ±0.5V
input_impedance: >1MΩ
common_mode: 1.4V ±0.1V
```

### 4. Output Interface

```verilog
// Output specifications
dout: 16-bit digital output
data_valid: Output strobe
conversion_done: Status flag
```

## Verification Strategy

### 1. Functional Verification

- **Unit Tests**: Individual block verification
- **Integration Tests**: Full ADC verification
- **Corner Tests**: Process/temperature corners
- **Monte Carlo**: Statistical verification

### 2. Performance Verification

- **Static Performance**: DC characteristics
- **Dynamic Performance**: AC characteristics
- **Noise Analysis**: Input-referred noise
- **Power Analysis**: Power consumption

### 3. Layout Verification

- **DRC**: Design rule checking
- **LVS**: Layout vs. schematic
- **PEX**: Parasitic extraction
- **Timing**: Post-layout timing

## Troubleshooting

### Common Issues

1. **Spectre Convergence**
   ```bash
   # Add convergence options
   spectre -convergence aggressive programmable_adc_spectre.sp
   ```

2. **LVS Failures**
   ```bash
   # Check device mapping
   make lvs_debug
   
   # Verify net connectivity
   make lvs_connectivity
   ```

3. **Simulation Errors**
   ```bash
   # Check model files
   make check_models
   
   # Verify corner settings
   make check_corners
   ```

### Debug Commands

```bash
# Check file dependencies
make check_deps

# Validate netlist syntax
make validate_netlist

# Generate simulation report
make sim_report

# Check LVS setup
make check_lvs_setup
```

## Support

### Documentation

- **Architecture**: See `docs/architecture.md`
- **Waveforms**: See `docs/waveforms.md`
- **Integration**: See `integration/` directory

### Tools

- **Spectre**: Cadence Spectre simulator
- **Virtuoso**: Cadence Virtuoso layout editor
- **Calibre**: Mentor Graphics Calibre LVS
- **Make**: GNU Make build system

### Contact

For technical support or questions:
- **Email**: support@vyges.com
- **Documentation**: https://docs.vyges.com
- **Issues**: https://github.com/vyges/programmable-adc/issues

## License

This implementation is part of the Vyges Programmable ADC IP and is licensed under the terms specified in the main repository LICENSE file. 