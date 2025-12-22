#=============================================================================
# Questa Compilation Script
#=============================================================================
# Description: TCL script for compiling RTL and testbench files
#              Can be run standalone or as part of simulation
#
# Usage: vlog -sv -work work -do compile.do
#        Or: vsim -c -do compile.do
#
# Author:       Vyges Development Team
# Created:      2025
#=============================================================================

# Create work library if it doesn't exist
if {[file exists work]} {
    vdel -lib work -all
}
vlib work
vmap work work

# Compile RTL files (order matters - dependencies first)
echo "Compiling RTL files..."
vlog -sv -work work +incdir+../../rtl \
    ../../rtl/programmable_adc_apb_interface.sv \
    ../../rtl/programmable_adc_pga_stage.sv \
    ../../rtl/programmable_adc_sample_hold.sv \
    ../../rtl/programmable_adc_sar_controller.sv \
    ../../rtl/programmable_adc_dac_array.sv \
    ../../rtl/programmable_adc_comparator.sv \
    ../../rtl/programmable_adc.sv

# Compile testbench
echo "Compiling testbench..."
vlog -sv -work work \
    ../tb_programmable_adc.sv

# Check compilation status
if {[file exists work/_info]} then {
    echo "Compilation successful!"
} else {
    echo "ERROR: Compilation failed - work library not created!"
    exit 1
}
