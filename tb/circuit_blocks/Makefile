# Circuit Blocks Simulation Makefile
# Programmable ADC - Circuit Level Testing

# Simulator selection
SIMULATOR ?= vcs

# Directories
RTL_DIR = ../../rtl/circuit_blocks
TB_DIR = .
WORK_DIR = work

# Source files
RTL_FILES = $(RTL_DIR)/pga_circuit.sv \
            $(RTL_DIR)/sample_hold_circuit.sv \
            $(RTL_DIR)/sar_dac_circuit.sv \
            $(RTL_DIR)/comparator_circuit.sv

TB_FILES = $(TB_DIR)/tb_circuit_blocks.sv

# Default target
all: compile run

# Compile with VCS
compile-vcs:
	@echo "Compiling circuit blocks with VCS..."
	vcs -full64 -sverilog -debug_all \
		+define+SIMULATION \
		+define+VDDA=2.8 \
		+define+VDDD=1.1 \
		-o $(WORK_DIR)/simv \
		$(RTL_FILES) $(TB_FILES)

# Compile with Verilator
compile-verilator:
	@echo "Compiling circuit blocks with Verilator..."
	verilator --cc --exe --build \
		--trace \
		-DSIMULATION \
		-DVDDA=2.8 \
		-DVDDD=1.1 \
		$(RTL_FILES) $(TB_FILES) \
		-o $(WORK_DIR)/verilator_sim

# Compile with Icarus
compile-icarus:
	@echo "Compiling circuit blocks with Icarus..."
	iverilog -g2012 -D SIMULATION \
		-D VDDA=2.8 \
		-D VDDD=1.1 \
		-o $(WORK_DIR)/icarus_sim \
		$(RTL_FILES) $(TB_FILES)

# Run simulation
run-vcs:
	@echo "Running circuit blocks simulation with VCS..."
	$(WORK_DIR)/simv -gui &

run-verilator:
	@echo "Running circuit blocks simulation with Verilator..."
	$(WORK_DIR)/verilator_sim

run-icarus:
	@echo "Running circuit blocks simulation with Icarus..."
	vvp $(WORK_DIR)/icarus_sim

# Compile and run based on simulator
compile: compile-$(SIMULATOR)
run: run-$(SIMULATOR)

# Clean
clean:
	rm -rf $(WORK_DIR)
	rm -f *.vcd *.log *.key

# Help
help:
	@echo "Circuit Blocks Simulation Makefile"
	@echo "Usage: make [target] [SIMULATOR=simulator]"
	@echo ""
	@echo "Targets:"
	@echo "  all        - Compile and run simulation"
	@echo "  compile    - Compile design"
	@echo "  run        - Run simulation"
	@echo "  clean      - Clean build files"
	@echo "  help       - Show this help"
	@echo ""
	@echo "Simulators:"
	@echo "  vcs        - Synopsys VCS (default)"
	@echo "  verilator  - Verilator"
	@echo "  icarus     - Icarus Verilog"
	@echo ""
	@echo "Example: make SIMULATOR=verilator"

.PHONY: all compile run clean help 