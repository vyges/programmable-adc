#=============================================================================
# Vyges Programmable ADC - Cadence PDK Makefile
#=============================================================================
# Description: Build and simulation automation for Cadence PDK flow
# Author: Vyges IP Development Team
# Date: 2025
#=============================================================================

#=============================================================================
# Configuration
#=============================================================================

# Project configuration
PROJECT_NAME = programmable_adc_cadence
TOP_MODULE = tb_cadence_circuit_blocks
RTL_DIR = .
TB_DIR = .

# Simulator configuration
SIMULATOR ?= vcs
VCS_OPTS = -full64 -sverilog -v2k -timescale=1ns/1ps
VERILATOR_OPTS = --cc --exe --build -CFLAGS "-std=c++11"
ICARUS_OPTS = -g2012 -Wall

# Cadence-specific options
CADENCE_OPTS = -ams -ams_discipline logic
SPECTRE_OPTS = -64 -format psfxl

#=============================================================================
# File lists
#=============================================================================

# RTL source files
RTL_FILES = \
	$(RTL_DIR)/pga_circuit_cadence.sv \
	$(RTL_DIR)/sar_dac_circuit_cadence.sv \
	$(RTL_DIR)/comparator_circuit_cadence.sv \
	$(RTL_DIR)/sample_hold_circuit_cadence.sv

# Testbench files
TB_FILES = \
	$(TB_DIR)/tb_cadence_circuit_blocks.sv

# All source files
ALL_FILES = $(RTL_FILES) $(TB_FILES)

#=============================================================================
# Targets
#=============================================================================

.PHONY: all clean sim vcs verilator icarus spectre hspice coverage lint help

# Default target
all: sim

#=============================================================================
# Simulation targets
#=============================================================================

# Generic simulation target
sim: $(SIMULATOR)

# VCS simulation
vcs: compile_vcs run_vcs

compile_vcs:
	@echo "Compiling with VCS..."
	vcs $(VCS_OPTS) $(CADENCE_OPTS) -o $(PROJECT_NAME)_vcs $(ALL_FILES)

run_vcs:
	@echo "Running VCS simulation..."
	./$(PROJECT_NAME)_vcs -gui &

# Verilator simulation
verilator: compile_verilator run_verilator

compile_verilator:
	@echo "Compiling with Verilator..."
	verilator $(VERILATOR_OPTS) $(ALL_FILES) -o $(PROJECT_NAME)_verilator

run_verilator:
	@echo "Running Verilator simulation..."
	./obj_dir/$(PROJECT_NAME)_verilator

# Icarus Verilog simulation
icarus: compile_icarus run_icarus

compile_icarus:
	@echo "Compiling with Icarus Verilog..."
	iverilog $(ICARUS_OPTS) -o $(PROJECT_NAME)_icarus $(ALL_FILES)

run_icarus:
	@echo "Running Icarus Verilog simulation..."
	vvp $(PROJECT_NAME)_icarus

#=============================================================================
# Cadence-specific simulation targets
#=============================================================================

# Spectre simulation
spectre: compile_spectre run_spectre

compile_spectre:
	@echo "Compiling with Spectre..."
	spectre $(SPECTRE_OPTS) -raw ./spectre_results $(PROJECT_NAME).sp

run_spectre:
	@echo "Running Spectre simulation..."
	spectre $(SPECTRE_OPTS) -raw ./spectre_results $(PROJECT_NAME).sp

# HSPICE simulation
hspice: compile_hspice run_hspice

compile_hspice:
	@echo "Compiling with HSPICE..."
	hspice -i $(PROJECT_NAME).sp -o $(PROJECT_NAME)_hspice

run_hspice:
	@echo "Running HSPICE simulation..."
	hspice -i $(PROJECT_NAME).sp -o $(PROJECT_NAME)_hspice

#=============================================================================
# Analysis targets
#=============================================================================

# Coverage analysis
coverage: coverage_vcs

coverage_vcs:
	@echo "Running coverage analysis with VCS..."
	vcs $(VCS_OPTS) $(CADENCE_OPTS) -cm line+cond+fsm+branch+tgl \
		-cm_dir ./coverage_results -o $(PROJECT_NAME)_cov $(ALL_FILES)
	./$(PROJECT_NAME)_cov -cm line+cond+fsm+branch+tgl -cm_dir ./coverage_results
	dve -full64 -cov -dir ./coverage_results &

# Linting
lint: lint_spyglass lint_verilator

lint_spyglass:
	@echo "Running SpyGlass linting..."
	sg_shell -tcl lint_script.tcl

lint_verilator:
	@echo "Running Verilator linting..."
	verilator --lint-only $(ALL_FILES)

#=============================================================================
# Test targets
#=============================================================================

# Individual circuit block tests
test_pga: compile_vcs
	@echo "Testing PGA circuit..."
	./$(PROJECT_NAME)_vcs +test_pga

test_dac: compile_vcs
	@echo "Testing SAR DAC circuit..."
	./$(PROJECT_NAME)_vcs +test_dac

test_comparator: compile_vcs
	@echo "Testing Comparator circuit..."
	./$(PROJECT_NAME)_vcs +test_comparator

test_sample_hold: compile_vcs
	@echo "Testing Sample & Hold circuit..."
	./$(PROJECT_NAME)_vcs +test_sample_hold

# Performance tests
test_performance: compile_vcs
	@echo "Running performance tests..."
	./$(PROJECT_NAME)_vcs +test_performance

# Integration tests
test_integration: compile_vcs
	@echo "Running integration tests..."
	./$(PROJECT_NAME)_vcs +test_integration

# All tests
test_all: test_pga test_dac test_comparator test_sample_hold test_performance test_integration

#=============================================================================
# Documentation targets
#=============================================================================

# Generate documentation
docs: docs_rtl docs_testbench

docs_rtl:
	@echo "Generating RTL documentation..."
	doxygen doxygen_config.cfg

docs_testbench:
	@echo "Generating testbench documentation..."
	verilator --lint-only --doc $(ALL_FILES)

#=============================================================================
# Utility targets
#=============================================================================

# Clean build artifacts
clean:
	@echo "Cleaning build artifacts..."
	rm -rf $(PROJECT_NAME)_vcs
	rm -rf $(PROJECT_NAME)_verilator
	rm -rf $(PROJECT_NAME)_icarus
	rm -rf $(PROJECT_NAME)_hspice
	rm -rf obj_dir
	rm -rf coverage_results
	rm -rf spectre_results
	rm -rf *.log
	rm -rf *.vcd
	rm -rf *.fsdb
	rm -rf *.trn
	rm -rf *.out
	rm -rf *.sp
	rm -rf *.lis
	rm -rf *.st0
	rm -rf *.ic0
	rm -rf *.sw0
	rm -rf *.tr0
	rm -rf *.ac0
	rm -rf *.swp
	rm -rf *.swo
	rm -rf *~

# Clean everything including generated files
distclean: clean
	@echo "Cleaning everything..."
	rm -rf docs
	rm -rf reports
	rm -rf waveforms
	rm -rf results

#=============================================================================
# CI/CD pipeline targets
#=============================================================================

# CI pipeline
ci: lint test_all coverage
	@echo "CI pipeline completed successfully"

# CD pipeline
cd: ci docs
	@echo "CD pipeline completed successfully"

#=============================================================================
# Help target
#=============================================================================

help:
	@echo "Cadence PDK Circuit Implementation Makefile"
	@echo "=========================================="
	@echo ""
	@echo "Available targets:"
	@echo "  all              - Run default simulation"
	@echo "  sim              - Run simulation with default simulator"
	@echo "  vcs              - Run VCS simulation"
	@echo "  verilator        - Run Verilator simulation"
	@echo "  icarus           - Run Icarus Verilog simulation"
	@echo "  spectre          - Run Spectre simulation"
	@echo "  hspice           - Run HSPICE simulation"
	@echo ""
	@echo "Testing targets:"
	@echo "  test_pga         - Test PGA circuit"
	@echo "  test_dac         - Test SAR DAC circuit"
	@echo "  test_comparator  - Test Comparator circuit"
	@echo "  test_sample_hold - Test Sample & Hold circuit"
	@echo "  test_performance - Run performance tests"
	@echo "  test_integration - Run integration tests"
	@echo "  test_all         - Run all tests"
	@echo ""
	@echo "Analysis targets:"
	@echo "  coverage         - Run coverage analysis"
	@echo "  lint             - Run linting"
	@echo ""
	@echo "Documentation targets:"
	@echo "  docs             - Generate documentation"
	@echo ""
	@echo "Utility targets:"
	@echo "  clean            - Clean build artifacts"
	@echo "  distclean        - Clean everything"
	@echo "  help             - Show this help"
	@echo ""
	@echo "CI/CD targets:"
	@echo "  ci               - Run CI pipeline"
	@echo "  cd               - Run CD pipeline"
	@echo ""
	@echo "Configuration:"
	@echo "  SIMULATOR        - Set simulator (vcs, verilator, icarus)"
	@echo "  VCS_OPTS         - VCS compilation options"
	@echo "  VERILATOR_OPTS   - Verilator compilation options"
	@echo "  ICARUS_OPTS      - Icarus Verilog compilation options"

#=============================================================================
# Dependencies
#=============================================================================

# Dependencies for simulation
$(PROJECT_NAME)_vcs: $(ALL_FILES)
$(PROJECT_NAME)_verilator: $(ALL_FILES)
$(PROJECT_NAME)_icarus: $(ALL_FILES)

#=============================================================================
# Environment setup
#=============================================================================

# Check for required tools
check_tools:
	@echo "Checking required tools..."
	@which vcs > /dev/null || echo "Warning: VCS not found"
	@which verilator > /dev/null || echo "Warning: Verilator not found"
	@which iverilog > /dev/null || echo "Warning: Icarus Verilog not found"
	@which spectre > /dev/null || echo "Warning: Spectre not found"
	@which hspice > /dev/null || echo "Warning: HSPICE not found"

# Setup environment
setup: check_tools
	@echo "Setting up environment..."
	mkdir -p coverage_results
	mkdir -p spectre_results
	mkdir -p waveforms
	mkdir -p reports
	mkdir -p docs

#=============================================================================
# Default target
#=============================================================================

.DEFAULT_GOAL := all 