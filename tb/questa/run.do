#=============================================================================
# Questa Simulation Run Script
#=============================================================================
# Description: TCL script for running Questa simulation in command-line mode
#              Compiles RTL and testbench, runs simulation, and generates logs
#
# Usage: vsim -c -do run.do tb_programmable_adc
#
# Author:       Vyges Development Team
# Created:      2025
#=============================================================================

# Set simulation time limit (in ns)
set SIM_TIME 100000

# Run simulation
echo "=========================================="
echo "Starting Questa Simulation"
echo "=========================================="
echo "Top Module: tb_programmable_adc"
echo "Simulation Time: ${SIM_TIME} ns"
echo ""

# Run simulation until $finish or time limit
run ${SIM_TIME}ns

# Check if simulation finished and display summary
if {[examine /tb_programmable_adc/test_count] != ""} then {
    set total_tests [examine -decimal /tb_programmable_adc/test_count]
    set pass_tests [examine -decimal /tb_programmable_adc/pass_count]
    set fail_tests [examine -decimal /tb_programmable_adc/fail_count]
    
    echo ""
    echo "=========================================="
    echo "Simulation Summary"
    echo "=========================================="
    echo "Total Tests: $total_tests"
    echo "Passed: $pass_tests"
    echo "Failed: $fail_tests"
    if {$total_tests > 0} then {
        set success_rate [expr ($pass_tests * 100.0) / $total_tests]
        echo "Success Rate: $success_rate%"
    }
    echo ""
}

# Finish simulation
echo "Simulation completed."
quit -f
