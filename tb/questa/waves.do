#=============================================================================
# Questa Waveform Configuration Script
#=============================================================================
# Description: TCL script for configuring waveform viewer in Questa GUI
#              Adds all relevant signals to waveform window
#
# Usage: vsim -gui -do waves.do tb_programmable_adc
#
# Author:       Vyges Development Team
# Created:      2025
#=============================================================================

# Open waveform window
view wave

# Configure waveform display
configure wave -signalnamewidth 1
configure wave -timelineunits ns
configure wave -griddelta 10ns

# Add clock and reset signals
add wave -divider "Clock and Reset"
add wave -radix binary /tb_programmable_adc/PCLK
add wave -radix binary /tb_programmable_adc/PRESETn

# Add APB interface signals
add wave -divider "APB Interface"
add wave -radix hex /tb_programmable_adc/PADDR
add wave -radix hex /tb_programmable_adc/PWDATA
add wave -radix hex /tb_programmable_adc/PRDATA
add wave -radix binary /tb_programmable_adc/PSEL
add wave -radix binary /tb_programmable_adc/PENABLE
add wave -radix binary /tb_programmable_adc/PWRITE
add wave -radix binary /tb_programmable_adc/PREADY

# Add analog inputs
add wave -divider "Analog Inputs"
add wave -radix binary /tb_programmable_adc/VIN0P
add wave -radix binary /tb_programmable_adc/VIN0N
add wave -radix binary /tb_programmable_adc/VIN1P
add wave -radix binary /tb_programmable_adc/VIN1N
add wave -radix binary /tb_programmable_adc/VIN2P
add wave -radix binary /tb_programmable_adc/VIN2N
add wave -radix binary /tb_programmable_adc/VREF
add wave -radix binary /tb_programmable_adc/VCM

# Add power supply
add wave -divider "Power Supply"
add wave -radix binary /tb_programmable_adc/VDDA
add wave -radix binary /tb_programmable_adc/VSSA

# Add ADC outputs
add wave -divider "ADC Outputs"
add wave -radix binary /tb_programmable_adc/adc_irq
add wave -radix binary /tb_programmable_adc/busy_o
add wave -radix binary /tb_programmable_adc/valid_o
add wave -radix hex /tb_programmable_adc/data_o
add wave -radix unsigned /tb_programmable_adc/channel_o

# Add DUT internal signals (if accessible)
add wave -divider "DUT Internal Signals"
add wave -radix hex /tb_programmable_adc/dut/sar_data
add wave -radix binary /tb_programmable_adc/dut/sar_busy
add wave -radix binary /tb_programmable_adc/dut/sar_valid
add wave -radix binary /tb_programmable_adc/dut/start_conv
add wave -radix binary /tb_programmable_adc/dut/adc_enable
add wave -radix unsigned /tb_programmable_adc/dut/resolution
add wave -radix unsigned /tb_programmable_adc/dut/pga_gain
add wave -radix unsigned /tb_programmable_adc/dut/channel_sel

# Add APB interface internal signals
add wave -divider "APB Interface Internal"
add wave -radix hex /tb_programmable_adc/dut/apb_if/control_reg
add wave -radix hex /tb_programmable_adc/dut/apb_if/config_reg
add wave -radix binary /tb_programmable_adc/dut/apb_if/apb_state

# Add SAR controller state
add wave -divider "SAR Controller"
add wave -radix unsigned /tb_programmable_adc/dut/sar_ctrl/state
add wave -radix unsigned /tb_programmable_adc/dut/sar_ctrl/bit_counter
add wave -radix hex /tb_programmable_adc/dut/sar_ctrl/sar_register

# Run simulation
echo "Waveform window configured. Running simulation..."
run 100us

# Zoom to fit
wave zoom full
