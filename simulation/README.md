# Simulation Directory

This directory contains simulation configurations, results, and waveforms for mixed-signal verification of the programmable ADC.

## Directory Structure

```
simulation/
├── configs/          # Simulation configuration files
├── results/          # Simulation results and reports
└── waveforms/        # Waveform files and plots
```

## Simulation Types

### Digital Simulation
- **Tool**: Verilator, ModelSim, Icarus Verilog
- **Purpose**: Verify digital control logic
- **Files**: Testbench outputs, coverage reports

### Analog Simulation
- **Tool**: ngspice, Xyce
- **Purpose**: Verify analog circuit performance
- **Files**: SPICE simulation results, AC/DC analysis

### Mixed-Signal Simulation
- **Tool**: ngspice (xspice), Xyce
- **Purpose**: Verify digital-analog interaction
- **Files**: Combined simulation results

## Configuration Files (configs/)

### Digital Simulation Configs
- `tb_config.json` - Testbench configuration
- `coverage_config.json` - Coverage settings
- `verilator_config.vlt` - Verilator configuration

### Analog Simulation Configs
- `dc_analysis.sp` - DC operating point analysis
- `ac_analysis.sp` - AC frequency response
- `transient_analysis.sp` - Transient simulation
- `monte_carlo.sp` - Monte Carlo analysis
- `corner_analysis.sp` - Process corner analysis

### Mixed-Signal Configs
- `mixed_signal.sp` - Combined digital-analog simulation
- `system_verification.sp` - System-level verification

## Results Directory (results/)

### Digital Results
- `coverage_report.html` - Code coverage reports
- `functional_test_results.txt` - Functional test results
- `timing_analysis.txt` - Timing analysis results

### Analog Results
- `dc_results.txt` - DC operating point results
- `ac_results.txt` - AC analysis results
- `transient_results.txt` - Transient simulation results
- `monte_carlo_results.txt` - Monte Carlo analysis results

### Mixed-Signal Results
- `system_verification_results.txt` - System-level verification
- `performance_characterization.txt` - Performance metrics

## Waveforms Directory (waveforms/)

### Digital Waveforms
- `tb_waves.vcd` - Digital testbench waveforms
- `control_signals.vcd` - Control signal waveforms

### Analog Waveforms
- `analog_signals.raw` - Analog signal waveforms
- `comparator_outputs.raw` - Comparator output waveforms
- `dac_outputs.raw` - DAC output waveforms

### Mixed-Signal Waveforms
- `adc_conversion.raw` - ADC conversion waveforms
- `system_response.raw` - System response waveforms

## Simulation Workflow

1. **Setup**: Configure simulation parameters in `configs/`
2. **Run**: Execute simulations using appropriate tools
3. **Analyze**: Review results in `results/`
4. **Visualize**: View waveforms in `waveforms/`
5. **Document**: Update documentation with findings

## Tools Integration

### Digital Tools
- **Verilator**: Fast digital simulation
- **Cocotb**: Python-based testbenches
- **GTKWave**: Waveform viewer

### Analog Tools
- **ngspice**: Circuit simulation
- **Xyce**: Parallel circuit simulation
- **Gnuplot**: Waveform plotting

### Mixed-Signal Tools
- **ngspice (xspice)**: Mixed-signal simulation
- **Xyce**: Advanced mixed-signal capabilities

## Performance Metrics

### ADC Performance
- **Resolution**: Effective number of bits (ENOB)
- **Sampling Rate**: Maximum conversion rate
- **DNL/INL**: Differential/Integral non-linearity
- **SNR/SFDR**: Signal-to-noise ratio, spurious-free dynamic range

### Power Performance
- **Static Power**: Quiescent power consumption
- **Dynamic Power**: Switching power consumption
- **Power Efficiency**: Power per conversion

### Timing Performance
- **Conversion Time**: Time to complete conversion
- **Setup/Hold Times**: Digital interface timing
- **Clock Frequency**: Maximum operating frequency 