# Circuit-Level Implementation

## Overview

This directory contains the detailed circuit-level implementations of the Programmable ADC IP core. These modules provide realistic analog behavior modeling for simulation and verification purposes.

## Circuit Blocks

### 1. PGA Circuit (`pga_circuit.sv`)
**Programmable Gain Amplifier with Chopper Stabilization**

- **Features:**
  - Programmable gains: 1x, 2x, 4x
  - Chopper stabilization for offset reduction
  - High CMRR and PSRR
  - Overload detection
  - Realistic noise and distortion modeling

- **Key Parameters:**
  - Supply voltage: 2.8V (VDDA)
  - Bias current: 100μA
  - Bandwidth: 10MHz (1x), 5MHz (2x), 2.5MHz (4x)
  - CMRR: >80dB
  - PSRR: >80dB

- **Usage:**
```systemverilog
pga_circuit #(
    .VDDA(2.8),
    .VDDD(1.1),
    .VCM(1.4),
    .IBIAS(100e-6),
    .CLOAD(10e-12),
    .RLOAD(100e3)
) pga_inst (
    .clk_i(clk),
    .reset_n_i(reset_n),
    .chopper_clk_i(chopper_clk),
    .enable_i(enable),
    .gain_sel_i(gain_sel),
    .vin_p_i(vin_p),
    .vin_n_i(vin_n),
    .vcm_i(vcm),
    .vout_p_o(vout_p),
    .vout_n_o(vout_n),
    .ready_o(ready),
    .overload_o(overload),
    .offset_o(offset),
    .gain_error_o(gain_error)
);
```

### 2. Sample & Hold Circuit (`sample_hold_circuit.sv`)
**High-Speed Sample & Hold with Low Droop**

- **Features:**
  - Transmission gate switches
  - Low droop rate (<1mV/ms)
  - Fast settling time (<100ns)
  - Realistic charge injection and clock feedthrough
  - Buffer with high input impedance

- **Key Parameters:**
  - Hold capacitor: 10pF
  - Switch resistance: 100Ω
  - Leakage current: 1fA
  - Settling time: <100ns
  - Droop rate: <1mV/ms

- **Usage:**
```systemverilog
sample_hold_circuit #(
    .VDDA(2.8),
    .VDDD(1.1),
    .CHOLD(10e-12),
    .RSWITCH(100.0),
    .CLEAKAGE(1e-15),
    .CLOAD(5e-12)
) sh_inst (
    .clk_i(clk),
    .reset_n_i(reset_n),
    .sample_i(sample),
    .hold_i(hold),
    .vin_i(vin),
    .vcm_i(vcm),
    .vout_o(vout),
    .vout_cm_o(vout_cm),
    .ready_o(ready),
    .sample_done_o(sample_done),
    .droop_rate_o(droop_rate),
    .settling_time_o(settling_time)
);
```

### 3. SAR DAC Circuit (`sar_dac_circuit.sv`)
**Binary-Weighted Capacitor DAC Array**

- **Features:**
  - Programmable resolution: 12/14/16-bit
  - Binary-weighted capacitor array
  - Calibration support
  - Temperature and voltage drift modeling
  - Realistic capacitor mismatch

- **Key Parameters:**
  - Unit capacitor: 1fF
  - Capacitor mismatch: 0.1%
  - Temperature coefficient: 20ppm/°C
  - Voltage coefficient: 50ppm/V
  - Settling time: <1μs

- **Usage:**
```systemverilog
sar_dac_circuit #(
    .RESOLUTION(16),
    .VDDA(2.8),
    .VDDD(1.1),
    .VREF(2.8),
    .CUNIT(1e-15),
    .CMISMATCH(0.001),
    .TEMP_COEF(20e-6),
    .VOLT_COEF(50e-6)
) dac_inst (
    .clk_i(clk),
    .reset_n_i(reset_n),
    .enable_i(enable),
    .resolution_i(resolution),
    .dac_code_i(dac_code),
    .dac_valid_i(dac_valid),
    .reset_dac_i(reset_dac),
    .cal_enable_i(cal_enable),
    .cal_code_i(cal_code),
    .cal_valid_i(cal_valid),
    .dac_out_p_o(dac_out_p),
    .dac_out_n_o(dac_out_n),
    .dac_cm_o(dac_cm),
    .ready_o(ready),
    .busy_o(busy),
    .dnl_o(dnl),
    .inl_o(inl),
    .temp_drift_o(temp_drift),
    .voltage_drift_o(voltage_drift)
);
```

### 4. Comparator Circuit (`comparator_circuit.sv`)
**High-Speed Comparator with Preamp and Latch**

- **Features:**
  - Preamp with high gain
  - Regenerative latch
  - Offset calibration
  - Programmable hysteresis
  - Metastability detection

- **Key Parameters:**
  - Preamp gain: 60dB
  - Preamp bandwidth: 10MHz
  - Latch regeneration time: 8ns
  - Offset calibration range: ±10mV
  - Hysteresis range: 0-10mV

- **Usage:**
```systemverilog
comparator_circuit #(
    .VDDA(2.8),
    .VDDD(1.1),
    .VCM(1.4),
    .IBIAS(30e-6),
    .PREAMP_GAIN(60.0),
    .PREAMP_BW(10e6),
    .LATCH_TIME(8e-9),
    .HYSTERESIS_MAX(10e-3)
) comp_inst (
    .clk_i(clk),
    .reset_n_i(reset_n),
    .enable_i(enable),
    .latch_enable_i(latch_enable),
    .reset_latch_i(reset_latch),
    .hysteresis_i(hysteresis),
    .cal_enable_i(cal_enable),
    .cal_offset_i(cal_offset),
    .cal_valid_i(cal_valid),
    .vin_p_i(vin_p),
    .vin_n_i(vin_n),
    .vcm_i(vcm),
    .comp_out_o(comp_out),
    .comp_out_valid_o(comp_out_valid),
    .metastable_o(metastable),
    .ready_o(ready),
    .offset_o(offset),
    .hysteresis_o(hysteresis),
    .noise_o(noise),
    .delay_o(delay)
);
```

## Simulation

### Testbench
The comprehensive testbench (`tb_circuit_blocks.sv`) tests all circuit blocks with realistic analog behavior:

- **PGA Tests:**
  - Basic functionality
  - Gain accuracy (1x, 2x, 4x)
  - Offset and CMRR
  - Chopper operation
  - Overload detection

- **Sample & Hold Tests:**
  - Basic sampling
  - Settling time
  - Hold accuracy
  - Droop rate

- **DAC Tests:**
  - Basic functionality
  - Resolution modes (12/14/16-bit)
  - Linearity (DNL/INL)
  - Calibration

- **Comparator Tests:**
  - Basic functionality
  - Offset calibration
  - Hysteresis
  - Metastability detection

### Running Simulation

```bash
# Navigate to testbench directory
cd tb/circuit_blocks

# Compile and run with VCS (default)
make

# Compile and run with Verilator
make SIMULATOR=verilator

# Compile and run with Icarus
make SIMULATOR=icarus

# Clean build files
make clean

# Show help
make help
```

## Circuit Modeling Features

### Realistic Analog Behavior
- **Noise Modeling:** Thermal noise, flicker noise, quantization noise
- **Non-linearities:** Harmonic distortion, intermodulation
- **Temperature Effects:** Drift, temperature coefficients
- **Process Variations:** Mismatch, corner variations
- **Power Consumption:** Static and dynamic power calculation

### Performance Monitoring
- **Real-time Monitoring:** Offset, gain error, noise, timing
- **Performance Metrics:** DNL, INL, SNR, THD
- **Power Analysis:** Static and dynamic power breakdown
- **Reliability Metrics:** Aging effects, temperature drift

### Calibration Support
- **Offset Calibration:** Digital calibration codes
- **Gain Calibration:** Programmable gain adjustment
- **Temperature Compensation:** Lookup table support
- **Voltage Compensation:** Supply voltage compensation

## Design Guidelines

### Parameter Selection
- **Supply Voltages:** VDDA=2.8V, VDDD=1.1V for 40nm technology
- **Common Mode:** VCM=VDDA/2 for optimal swing
- **Capacitor Values:** Based on matching requirements
- **Resistor Values:** Based on noise and power requirements

### Layout Considerations
- **Matching:** Common centroid layout for critical devices
- **Noise:** Separate analog and digital grounds
- **Power:** Dedicated power domains for analog and digital
- **Thermal:** Symmetric layout for temperature matching

### Verification Strategy
- **Functional Verification:** All operating modes
- **Performance Verification:** Accuracy, speed, power
- **Corner Analysis:** Process, temperature, voltage corners
- **Monte Carlo:** Statistical analysis for yield

## Integration

### Top-Level Integration
These circuit blocks are integrated into the main ADC design:

```systemverilog
// In programmable_adc_top.sv
pga_circuit pga_inst (/* connections */);
sample_hold_circuit sh_inst (/* connections */);
sar_dac_circuit dac_inst (/* connections */);
comparator_circuit comp_inst (/* connections */);
```

### Interface Compatibility
- **Clock Domain:** All blocks use the same clock domain
- **Reset Strategy:** Synchronous reset with proper sequencing
- **Data Interface:** Real-valued analog signals
- **Control Interface:** Digital control signals

## Performance Targets

### Accuracy
- **DNL:** <0.5 LSB
- **INL:** <1 LSB
- **Offset:** <1mV (calibrated)
- **Gain Error:** <0.1%

### Speed
- **Conversion Rate:** 5 MSPS
- **Settling Time:** <100ns
- **Propagation Delay:** <10ns

### Power
- **Total Power:** <5mW
- **Analog Power:** <3mW
- **Digital Power:** <2mW

### Noise
- **SNR:** >70dB
- **THD:** <-80dBc
- **Input Referred Noise:** <100μV RMS

## Support

For questions or issues with the circuit implementation:

1. Check the testbench output for performance metrics
2. Verify parameter settings match your requirements
3. Review the circuit analysis documentation
4. Consult the component specifications

The circuit blocks are designed to be production-ready and include comprehensive verification and documentation. 