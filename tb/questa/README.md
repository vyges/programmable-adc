# Questa Simulation Guide

This directory contains Questa/ModelSim simulation scripts and configuration files for the Programmable ADC IP.

## Prerequisites

- **Siemens Questa** or **ModelSim** installed and in PATH
- Questa license available
- RTL and testbench files in parent directories

## Directory Structure

```
tb/questa/
├── README.md          # This file
├── compile.do         # Compilation script
├── run.do             # Command-line simulation script
└── waves.do           # GUI waveform configuration script
```

## Quick Start

### Command-Line Simulation

```bash
# From tb/ directory
make sim-questa

# Or manually:
cd questa
vlog -sv -work work +incdir+../../rtl ../../rtl/*.sv ../tb_programmable_adc.sv
vsim -c -do run.do tb_programmable_adc
```

### GUI Simulation

```bash
# From tb/ directory
make sim-questa-gui

# Or manually:
cd questa
vlog -sv -work work +incdir+../../rtl ../../rtl/*.sv ../tb_programmable_adc.sv
vsim -gui -do waves.do tb_programmable_adc
```

## Scripts

### compile.do

Compiles all RTL and testbench files into the Questa work library.

**Usage:**
```tcl
vlog -sv -work work -do compile.do
```

**What it does:**
- Creates/cleans work library
- Compiles all RTL modules
- Compiles testbench
- Reports compilation status

### run.do

Runs command-line simulation with automatic completion.

**Usage:**
```tcl
vsim -c -do run.do tb_programmable_adc
```

**What it does:**
- Runs simulation for specified time
- Displays test summary
- Exits automatically

**Configuration:**
- Simulation time: 100,000 ns (configurable via `SIM_TIME` variable)

### waves.do

Configures waveform viewer for GUI simulation.

**Usage:**
```tcl
vsim -gui -do waves.do tb_programmable_adc
```

**What it does:**
- Opens waveform window
- Adds organized signal groups:
  - Clock and Reset
  - APB Interface
  - Analog Inputs
  - Power Supply
  - ADC Outputs
  - DUT Internal Signals
  - APB Interface Internal
  - SAR Controller State
- Runs simulation for 100us
- Zooms waveform to fit

## Makefile Targets

From the `tb/` directory:

- `make sim-questa` - Run command-line simulation
- `make sim-questa-gui` - Launch GUI simulation
- `make sim-questa-gui-stop` - Stop GUI simulation
- `make clean` - Clean Questa work files

## Manual Workflow

### Step 1: Compile

```bash
cd tb/questa
vlog -sv -work work +incdir+../../rtl \
    ../../rtl/programmable_adc.sv \
    ../../rtl/programmable_adc_apb_interface.sv \
    ../../rtl/programmable_adc_pga_stage.sv \
    ../../rtl/programmable_adc_sample_hold.sv \
    ../../rtl/programmable_adc_sar_controller.sv \
    ../../rtl/programmable_adc_dac_array.sv \
    ../../rtl/programmable_adc_comparator.sv \
    ../tb_programmable_adc.sv
```

### Step 2: Simulate (Command-Line)

```bash
vsim -c -do run.do tb_programmable_adc
```

### Step 2: Simulate (GUI)

```bash
vsim -gui -do waves.do tb_programmable_adc
```

## Waveform Analysis

### Viewing Waveforms

1. Launch GUI simulation: `make sim-questa-gui`
2. Waveforms are automatically configured by `waves.do`
3. Use Questa waveform viewer controls:
   - Zoom: Mouse wheel or toolbar buttons
   - Navigate: Scroll bars
   - Measure: Cursor tools

### Saving Waveforms

```tcl
# In Questa GUI, use TCL console:
log -r /*          # Log all signals recursively
run 100us          # Run simulation
save wave.do       # Save current wave configuration
```

### Loading Saved Waveforms

```tcl
# In Questa GUI:
do waves.do        # Load saved wave configuration
```

## Debugging

### Common Issues

1. **Compilation Errors:**
   - Check file paths are correct
   - Verify SystemVerilog syntax
   - Ensure all dependencies are compiled

2. **Simulation Hangs:**
   - Check for infinite loops in testbench
   - Verify clock generation
   - Check reset sequence

3. **Missing Signals:**
   - Verify signal names match RTL
   - Check hierarchy paths
   - Use `add wave -recursive /*` to add all signals

### Debug Commands

```tcl
# In Questa GUI TCL console:

# List all signals
ls /tb_programmable_adc/*

# Examine signal value
examine /tb_programmable_adc/data_o

# Set breakpoint
when {/tb_programmable_adc/valid_o == 1} {
    echo "Conversion complete!"
}

# Step simulation
step 10

# Continue simulation
run -continue
```

## Coverage Analysis

### Enable Coverage

```tcl
# In compile.do or vsim command:
vlog -sv -coverage=bcfst -work work <files>
vsim -coverage -c -do run.do tb_programmable_adc
```

### View Coverage

```tcl
# In Questa GUI:
coverage report -file coverage.rpt
coverage report -html -htmldir coverage_html
```

## Performance Tips

1. **Use command-line mode** for batch runs
2. **Limit waveform logging** to signals of interest
3. **Use `-novopt`** flag for debugging (disables optimizations)
4. **Use `-voptargs=+acc`** for full signal access

## Integration with CI/CD

```bash
# Example CI script
cd tb/questa
vlog -sv -work work +incdir+../../rtl ../../rtl/*.sv ../tb_programmable_adc.sv
vsim -c -do run.do tb_programmable_adc | tee sim.log
grep -q "ALL TESTS PASSED" sim.log && exit 0 || exit 1
```

## References

- [Questa User Guide](https://www.mentor.com/products/fv/questa/)
- [ModelSim Command Reference](https://www.mentor.com/products/fv/modelsim/)
- [SystemVerilog LRM](https://ieeexplore.ieee.org/document/8299595)

## Support

For issues or questions:
- Check compilation logs in `../logs/questa_compile.log`
- Check simulation logs in `../logs/questa_sim.log`
- Review testbench output for error messages
