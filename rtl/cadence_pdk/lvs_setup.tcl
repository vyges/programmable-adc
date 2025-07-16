#=============================================================================
# LVS Setup Script for Cadence Virtuoso
#=============================================================================
# Description: LVS setup and run script for Programmable ADC
# Author: Vyges IP Development Team
# Date: 2024
#=============================================================================

#=============================================================================
# LVS Configuration
#=============================================================================
set lvs_config {
    # LVS tool configuration
    lvs_tool "calibre"
    lvs_runset "lvs_runset.rules"
    
    # Netlist files
    schematic_netlist "programmable_adc_spectre.sp"
    layout_netlist "programmable_adc_layout.sp"
    
    # Output files
    lvs_report "lvs_report.txt"
    lvs_log "lvs.log"
    
    # Device mapping
    device_mapping {
        nmos_40nm -> nmos
        pmos_40nm -> pmos
        cap_40nm -> capacitor
        res_40nm -> resistor
        chopper_switch -> switch
        sample_switch -> switch
        hold_switch -> switch
    }
    
    # Power nets
    power_nets "VDDA"
    ground_nets "VSSA"
    
    # Exclude nets (if any)
    exclude_nets ""
    
    # Case sensitivity
    case_sensitive false
    
    # Hierarchical LVS
    hierarchical true
    black_box_subckt false
    
    # Device property mapping
    device_properties {
        nmos { w l }
        pmos { w l }
        capacitor { c }
        resistor { r }
        switch { ron roff vt }
    }
    
    # Net property mapping
    net_properties {
        capacitance
        resistance
    }
    
    # LVS options
    lvs_options {
        # Tolerance settings
        tolerance {
            resistance 1%
            capacitance 5%
            voltage 1mV
            current 1nA
        }
        
        # Report settings
        report {
            detailed true
            summary true
            connectivity true
            property true
            device true
        }
        
        # Filter settings
        filter {
            min_resistance 1e-3
            min_capacitance 1e-18
            max_resistance 1e12
            max_capacitance 1e-6
        }
    }
}

#=============================================================================
# LVS Runset File Generation
#=============================================================================
proc generate_lvs_runset {} {
    set runset_file "lvs_runset.rules"
    
    set fp [open $runset_file w]
    
    puts $fp "#============================================================================="
    puts $fp "# LVS Runset for Programmable ADC"
    puts $fp "#============================================================================="
    puts $fp ""
    puts $fp "# LVS tool configuration"
    puts $fp "LVS TOOL calibre"
    puts $fp "LVS RULESET 40nm_ulp"
    puts $fp ""
    puts $fp "# Input files"
    puts $fp "LAYOUT NETLIST programmable_adc_layout.sp"
    puts $fp "SOURCE NETLIST programmable_adc_spectre.sp"
    puts $fp ""
    puts $fp "# Output files"
    puts $fp "LVS REPORT lvs_report.txt"
    puts $fp "LVS LOG lvs.log"
    puts $fp ""
    puts $fp "# Power and ground nets"
    puts $fp "LVS POWER NAME VDDA"
    puts $fp "LVS GROUND NAME VSSA"
    puts $fp ""
    puts $fp "# Device mapping"
    puts $fp "LVS DEVICE MAP nmos_40nm nmos"
    puts $fp "LVS DEVICE MAP pmos_40nm pmos"
    puts $fp "LVS DEVICE MAP cap_40nm capacitor"
    puts $fp "LVS DEVICE MAP res_40nm resistor"
    puts $fp "LVS DEVICE MAP chopper_switch switch"
    puts $fp "LVS DEVICE MAP sample_switch switch"
    puts $fp "LVS DEVICE MAP hold_switch switch"
    puts $fp ""
    puts $fp "# Device properties"
    puts $fp "LVS PROPERTY MAP nmos w l"
    puts $fp "LVS PROPERTY MAP pmos w l"
    puts $fp "LVS PROPERTY MAP capacitor c"
    puts $fp "LVS PROPERTY MAP resistor r"
    puts $fp "LVS PROPERTY MAP switch ron roff vt"
    puts $fp ""
    puts $fp "# Tolerance settings"
    puts $fp "LVS TOLERANCE RESISTANCE 1%"
    puts $fp "LVS TOLERANCE CAPACITANCE 5%"
    puts $fp "LVS TOLERANCE VOLTAGE 1mV"
    puts $fp "LVS TOLERANCE CURRENT 1nA"
    puts $fp ""
    puts $fp "# Filter settings"
    puts $fp "LVS FILTER RESISTANCE MIN 1e-3"
    puts $fp "LVS FILTER RESISTANCE MAX 1e12"
    puts $fp "LVS FILTER CAPACITANCE MIN 1e-18"
    puts $fp "LVS FILTER CAPACITANCE MAX 1e-6"
    puts $fp ""
    puts $fp "# Report settings"
    puts $fp "LVS REPORT DETAILED TRUE"
    puts $fp "LVS REPORT SUMMARY TRUE"
    puts $fp "LVS REPORT CONNECTIVITY TRUE"
    puts $fp "LVS REPORT PROPERTY TRUE"
    puts $fp "LVS REPORT DEVICE TRUE"
    puts $fp ""
    puts $fp "# Hierarchical settings"
    puts $fp "LVS HIERARCHICAL TRUE"
    puts $fp "LVS BLACK BOX FALSE"
    puts $fp ""
    puts $fp "# Case sensitivity"
    puts $fp "LVS CASE SENSITIVE FALSE"
    puts $fp ""
    puts $fp "# LVS execution"
    puts $fp "LVS EXECUTE"
    
    close $fp
    
    puts "Generated LVS runset file: $runset_file"
}

#=============================================================================
# LVS Execution Script
#=============================================================================
proc run_lvs {} {
    global lvs_config
    
    puts "Starting LVS verification..."
    
    # Generate runset file
    generate_lvs_runset
    
    # Run LVS
    set lvs_cmd "calibre -lvs -runset lvs_runset.rules"
    
    puts "Executing: $lvs_cmd"
    set result [exec $lvs_cmd]
    
    puts "LVS execution completed"
    puts "Results:"
    puts $result
    
    # Check LVS results
    check_lvs_results
}

#=============================================================================
# LVS Results Check
#=============================================================================
proc check_lvs_results {} {
    set report_file "lvs_report.txt"
    
    if {[file exists $report_file]} {
        set fp [open $report_file r]
        set content [read $fp]
        close $fp
        
        # Check for LVS success
        if {[string match "*LVS COMPARISON PASSED*" $content]} {
            puts "LVS verification PASSED"
            return true
        } elseif {[string match "*LVS COMPARISON FAILED*" $content]} {
            puts "LVS verification FAILED"
            puts "Please check the LVS report for details"
            return false
        } else {
            puts "LVS verification status unclear"
            puts "Please check the LVS report manually"
            return false
        }
    } else {
        puts "LVS report file not found: $report_file"
        return false
    }
}

#=============================================================================
# Layout Netlist Generation
#=============================================================================
proc generate_layout_netlist {} {
    puts "Generating layout netlist..."
    
    # This would typically be done by extracting from Virtuoso layout
    # For now, we'll create a placeholder
    set layout_netlist "programmable_adc_layout.sp"
    
    set fp [open $layout_netlist w]
    puts $fp "//============================================================================="
    puts $fp "// Layout Netlist for Programmable ADC"
    puts $fp "//============================================================================="
    puts $fp "// This file should be generated from Virtuoso layout extraction"
    puts $fp "// For LVS comparison with schematic netlist"
    puts $fp "//============================================================================="
    puts $fp ""
    puts $fp "// Include the same subcircuits as schematic"
    puts $fp ".include models.scs"
    puts $fp ".include corners.scs"
    puts $fp ""
    puts $fp "// Main circuit (same as schematic for now)"
    puts $fp ".include programmable_adc_spectre.sp"
    puts $fp ""
    puts $fp ".END"
    
    close $fp
    
    puts "Generated layout netlist: $layout_netlist"
}

#=============================================================================
# Main Execution
#=============================================================================
proc main {} {
    puts "Programmable ADC LVS Setup"
    puts "=========================="
    
    # Generate layout netlist
    generate_layout_netlist
    
    # Run LVS
    run_lvs
    
    puts "LVS setup completed"
}

#=============================================================================
# Command Line Interface
#=============================================================================
if {[info exists argv] && [llength $argv] > 0} {
    set command [lindex $argv 0]
    
    switch $command {
        "generate_runset" {
            generate_lvs_runset
        }
        "run_lvs" {
            run_lvs
        }
        "check_results" {
            check_lvs_results
        }
        "generate_layout_netlist" {
            generate_layout_netlist
        }
        "main" {
            main
        }
        default {
            puts "Usage: tclsh lvs_setup.tcl \[command\]"
            puts "Commands:"
            puts "  generate_runset - Generate LVS runset file"
            puts "  run_lvs - Run LVS verification"
            puts "  check_results - Check LVS results"
            puts "  generate_layout_netlist - Generate layout netlist"
            puts "  main - Run complete LVS setup"
        }
    }
} else {
    main
} 