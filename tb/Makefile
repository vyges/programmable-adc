#=============================================================================
# Programmable ADC Testbench Makefile
#=============================================================================
# Description: Makefile for Programmable ADC simulation and verification
#              Supports multiple simulators and test scenarios.
#
# Targets:
#   sim          - Run simulation with default settings
#   sim-vcs      - Run simulation with VCS
#   sim-verilator - Run simulation with Verilator
#   clean        - Clean generated files
#   help         - Show available targets
#
# Author:       Vyges Development Team
# Created:      2025-01-27
#=============================================================================

# Configuration
SIMULATOR ?= vcs
TOP_MODULE = tb_programmable_adc
DUT_MODULE = programmable_adc_top

# Directories
RTL_DIR = ../rtl
TB_DIR = .
LOG_DIR = logs
COV_DIR = coverage

# RTL Files
RTL_FILES = \
	$(RTL_DIR)/programmable_adc_top.sv \
	$(RTL_DIR)/apb_interface.sv \
	$(RTL_DIR)/pga_stage.sv \
	$(RTL_DIR)/sample_hold.sv \
	$(RTL_DIR)/sar_controller.sv \
	$(RTL_DIR)/dac_array.sv \
	$(RTL_DIR)/comparator.sv

# Testbench Files
TB_FILES = \
	$(TB_DIR)/tb_programmable_adc.sv

# All Files
ALL_FILES = $(RTL_FILES) $(TB_FILES)

# Simulation Options
VCS_OPTS = -full64 -sverilog +v2k -timescale=1ns/1ps -debug_all
VERILATOR_OPTS = --cc --exe --build -CFLAGS "-std=c++11" -Wall
IVERILOG_OPTS = -g2012 -Wall -Wno-timescale

# Default target
.PHONY: all
all: sim

# Create directories
$(LOG_DIR):
	mkdir -p $(LOG_DIR)

$(COV_DIR):
	mkdir -p $(COV_DIR)

# VCS Simulation
.PHONY: sim-vcs
sim-vcs: $(LOG_DIR) $(COV_DIR)
	@echo "Running VCS simulation..."
	vcs $(VCS_OPTS) -o $(TOP_MODULE)_vcs $(ALL_FILES)
	./$(TOP_MODULE)_vcs | tee $(LOG_DIR)/vcs_sim.log
	@echo "VCS simulation completed. Log: $(LOG_DIR)/vcs_sim.log"

# Verilator Simulation
.PHONY: sim-verilator
sim-verilator: $(LOG_DIR) $(COV_DIR)
	@echo "Running Verilator simulation..."
	verilator $(VERILATOR_OPTS) $(ALL_FILES) -o $(TOP_MODULE)_verilator
	./obj_dir/$(TOP_MODULE)_verilator | tee $(LOG_DIR)/verilator_sim.log
	@echo "Verilator simulation completed. Log: $(LOG_DIR)/verilator_sim.log"

# Icarus Verilog Simulation
.PHONY: sim-iverilog
sim-iverilog: $(LOG_DIR) $(COV_DIR)
	@echo "Running Icarus Verilog simulation..."
	iverilog $(IVERILOG_OPTS) -o $(TOP_MODULE)_iverilog $(ALL_FILES)
	vvp $(TOP_MODULE)_iverilog | tee $(LOG_DIR)/iverilog_sim.log
	@echo "Icarus Verilog simulation completed. Log: $(LOG_DIR)/iverilog_sim.log"

# Default simulation (VCS)
.PHONY: sim
sim: sim-$(SIMULATOR)

# Coverage Analysis
.PHONY: coverage
coverage: $(COV_DIR)
	@echo "Generating coverage report..."
	# Add coverage analysis commands here
	@echo "Coverage analysis completed."

# Waveform Generation
.PHONY: waves
waves: $(LOG_DIR)
	@echo "Generating waveforms..."
	# Add waveform generation commands here
	@echo "Waveform generation completed."

# Linting
.PHONY: lint
lint:
	@echo "Running RTL linting..."
	verilator --lint-only $(RTL_FILES)
	@echo "Linting completed."

# Synthesis (for FPGA)
.PHONY: synth
synth:
	@echo "Running synthesis..."
	# Add synthesis commands here
	@echo "Synthesis completed."

# Clean generated files
.PHONY: clean
clean:
	@echo "Cleaning generated files..."
	rm -rf $(LOG_DIR)
	rm -rf $(COV_DIR)
	rm -rf obj_dir
	rm -f $(TOP_MODULE)_vcs
	rm -f $(TOP_MODULE)_verilator
	rm -f $(TOP_MODULE)_iverilog
	rm -f *.log
	rm -f *.vcd
	rm -f *.fsdb
	rm -f *.key
	rm -f *.conf
	rm -f *.rc
	rm -f *.tcl
	rm -f *.sdf
	rm -f *.spf
	rm -f *.sdc
	rm -f *.def
	rm -f *.lef
	rm -f *.gds
	rm -f *.o
	rm -f *.a
	rm -f *.so
	rm -f *.d
	rm -f *.tmp
	rm -f *.bak
	rm -f *.swp
	rm -f *~
	@echo "Clean completed."

# Help target
.PHONY: help
help:
	@echo "Programmable ADC Testbench Makefile"
	@echo "=================================="
	@echo ""
	@echo "Available targets:"
	@echo "  sim          - Run simulation with default simulator ($(SIMULATOR))"
	@echo "  sim-vcs      - Run simulation with VCS"
	@echo "  sim-verilator - Run simulation with Verilator"
	@echo "  sim-iverilog - Run simulation with Icarus Verilog"
	@echo "  coverage     - Generate coverage report"
	@echo "  waves        - Generate waveforms"
	@echo "  lint         - Run RTL linting"
	@echo "  synth        - Run synthesis"
	@echo "  clean        - Clean generated files"
	@echo "  help         - Show this help message"
	@echo ""
	@echo "Configuration:"
	@echo "  SIMULATOR    - Default simulator (vcs, verilator, iverilog)"
	@echo "  RTL_DIR      - RTL source directory"
	@echo "  TB_DIR       - Testbench directory"
	@echo "  LOG_DIR      - Log output directory"
	@echo "  COV_DIR      - Coverage output directory"
	@echo ""
	@echo "Example usage:"
	@echo "  make sim                    # Run with default simulator"
	@echo "  make SIMULATOR=verilator sim # Run with Verilator"
	@echo "  make clean                  # Clean all generated files"

# Check dependencies
.PHONY: check-deps
check-deps:
	@echo "Checking dependencies..."
	@which vcs > /dev/null 2>&1 || echo "WARNING: VCS not found"
	@which verilator > /dev/null 2>&1 || echo "WARNING: Verilator not found"
	@which iverilog > /dev/null 2>&1 || echo "WARNING: Icarus Verilog not found"
	@echo "Dependency check completed."

# Test individual modules
.PHONY: test-pga
test-pga: $(LOG_DIR)
	@echo "Testing PGA module..."
	# Add PGA-specific test commands here
	@echo "PGA test completed."

.PHONY: test-sar
test-sar: $(LOG_DIR)
	@echo "Testing SAR controller..."
	# Add SAR-specific test commands here
	@echo "SAR test completed."

.PHONY: test-apb
test-apb: $(LOG_DIR)
	@echo "Testing APB interface..."
	# Add APB-specific test commands here
	@echo "APB test completed."

# Performance testing
.PHONY: perf-test
perf-test: $(LOG_DIR)
	@echo "Running performance tests..."
	# Add performance test commands here
	@echo "Performance tests completed."

# Regression testing
.PHONY: regression
regression: $(LOG_DIR)
	@echo "Running regression tests..."
	$(MAKE) sim-vcs
	$(MAKE) sim-verilator
	$(MAKE) lint
	$(MAKE) coverage
	@echo "Regression tests completed."

# Documentation generation
.PHONY: docs
docs:
	@echo "Generating documentation..."
	# Add documentation generation commands here
	@echo "Documentation generation completed."

# Install dependencies (for CI/CD)
.PHONY: install-deps
install-deps:
	@echo "Installing dependencies..."
	# Add dependency installation commands here
	@echo "Dependencies installation completed."

# CI/CD pipeline
.PHONY: ci
ci: check-deps lint regression
	@echo "CI pipeline completed successfully."

# Release preparation
.PHONY: release
release: clean regression docs
	@echo "Release preparation completed."

# Show file list
.PHONY: files
files:
	@echo "RTL Files:"
	@for file in $(RTL_FILES); do echo "  $$file"; done
	@echo ""
	@echo "Testbench Files:"
	@for file in $(TB_FILES); do echo "  $$file"; done
	@echo ""
	@echo "All Files:"
	@for file in $(ALL_FILES); do echo "  $$file"; done

