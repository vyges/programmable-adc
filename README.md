[![Vyges IP](https://img.shields.io/badge/vyges-programmable--adc--ip-blue)](https://github.com/vyges/programmable-adc)
![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)
![Build](https://github.com/vyges/programmable-adc/actions/workflows/test.yml/badge.svg)
![SystemVerilog](https://img.shields.io/badge/SystemVerilog-2025-brightgreen)
![Cadence PDK](https://img.shields.io/badge/Cadence%20PDK-Supported-orange)

# Programmable ADC IP

A high-performance, programmable Analog-to-Digital Converter (ADC) IP core designed for mixed-signal SoC integration. Features include:

🔧 **Core Features:**
• Configurable resolution (12, 14, 16 bit)
• Programmable sampling rates (1-5 MSPS)
• Built-in PGA with gain control (1, 2, 3, 4)
• SAR DAC with calibration
• Advanced sample & hold circuit
• Real-time performance monitoring
• **Multi-PDK Support**: 40nm Ultra Low Power and Sky130 open-source PDK

🛠 **Design & Verification:**
• SystemVerilog RTL implementation
• **Multi-PDK Support**:
  - **40nm Ultra Low Power**: Cadence PDK (Spectre, Virtuoso, Calibre)
  - **Sky130**: Open-source PDK (Xschem, Magic, ngspice, Netgen)
• Analog schematic entry (Xschem for Sky130, Virtuoso for Cadence)
• Mixed-signal simulation (ngspice/Xyce for Sky130, Spectre/AMS Designer for Cadence)
• Layout design (Magic for Sky130, Virtuoso/IC Compiler for Cadence)
• DRC/LVS verification (Netgen for Sky130, Calibre for Cadence)
• Comprehensive testbench suite

📊 **Verification Tools:**
• UVM-compliant testbenches
• Coverage-driven verification
• Automated test harness reporting
• Multi-simulator support (VCS, Questa, Verilator)
• Open-source EDA tools (ngspice, Magic, Netgen)
• Mixed-signal simulation and verification

🎯 **Use Cases:**
• IoT sensor interfaces
• Audio processing systems
• Medical instrumentation
• Industrial control systems
• High-speed data acquisition

Built following Vyges IP development standards with automated documentation, verification flows, and integration examples.

## 🚀 Quickstart

1. **Clone the Repository:**
   ```bash
   git clone https://github.com/vyges/programmable-adc.git
   cd programmable-adc
   ```

2. **Setup Environment:**
   ```bash
   # Install Vyges CLI (if not already installed)
   pip install vyges-cli
   
   # Initialize project with Vyges
   vyges init --interactive
   ```

3. **Run Simulation:**
   ```bash
   # Run basic functional test
   vyges test --simulation
   
   # Run with Cadence PDK support
   vyges test --simulation --pdk cadence
   ```

4. **Generate Documentation:**
   ```bash
   # Generate test harness report
   python scripts/generate_test_harness_report.py vyges-metadata.json
   
   # View comprehensive documentation
   open Developer_Guide.md
   ```

5. **Next Steps:**
   - Review RTL implementation in `rtl/`
   - Explore testbenches in `tb/`
   - Check Cadence PDK integration in `rtl/cadence_pdk/`
   - Check Sky130 PDK integration in `analog/` (Xschem, Magic, ngspice)
   - See [Developer_Guide.md](Developer_Guide.md) for advanced usage

## 🔧 Project Structure

```
programmable-adc/
├── rtl/                                    # SystemVerilog RTL implementation
│   ├── programmable_adc.sv                # Main ADC top-level module
│   ├── programmable_adc_apb_interface.sv   # APB slave interface
│   ├── programmable_adc_pga_stage.sv      # Programmable Gain Amplifier
│   ├── programmable_adc_sar_controller.sv # SAR controller
│   ├── programmable_adc_dac_array.sv      # DAC array
│   ├── programmable_adc_comparator.sv     # High-speed comparator
│   └── programmable_adc_sample_hold.sv    # Sample & Hold circuit
├── analog/                 # Analog design files (Efabless flow)
│   ├── xschem/            # Schematic entry (Xschem)
│   ├── magic/             # Layout database (Magic)
│   ├── netlist/           # SPICE netlists
│   ├── gds/               # Final GDS layout
│   ├── lef/               # Abstract layout views
│   └── macros/            # Reusable analog components
├── simulation/             # Mixed-signal simulation
│   ├── configs/           # Simulation configurations
│   ├── results/           # Simulation results
│   └── waveforms/         # Waveform files
├── layout/                 # Layout verification
│   ├── constraints/       # Layout constraints
│   ├── lvs/              # Layout vs Schematic
│   └── drc/              # Design Rule Checks
├── tb/                     # Testbenches and verification
│   ├── sv_tb/             # SystemVerilog testbenches
│   ├── cocotb/            # Python-based verification
│   └── Makefile           # Test automation
├── flow/                   # EDA tool flows
│   ├── openlane/          # Open-source ASIC flow (Sky130)
│   └── synth_report.md    # Synthesis reports
├── analog/                 # Analog design files (Sky130 & Cadence)
│   ├── xschem/            # Schematic entry (Xschem for Sky130)
│   ├── magic/             # Layout database (Magic for Sky130)
│   ├── netlist/           # SPICE netlists (ngspice for Sky130)
│   ├── gds/               # Final GDS layout
│   ├── lef/               # Abstract layout views
│   └── macros/            # Reusable analog components
├── rtl/                    # SystemVerilog RTL implementation
│   ├── cadence_pdk/       # Cadence PDK-specific circuits
│   └── circuit_blocks/    # Generic circuit blocks
├── scripts/               # Automation scripts
│   ├── generate_test_harness_report.py
│   └── code_kpis.py
├── docs/                  # Documentation
├── integration/           # Integration examples
└── vyges-metadata.json   # Vyges metadata specification
```

## 🧪 Verification & Testing

### Supported Simulators
- **VCS** (Synopsys) - Primary commercial simulator
- **Questa** (Mentor/Siemens) - Advanced verification features
- **Verilator** - Open-source simulation
- **Spectre** (Cadence) - Analog simulation

### Test Coverage
- **Functional Tests**: Basic ADC operation and calibration
- **Performance Tests**: Speed, accuracy, and power measurements
- **Corner Tests**: Process, voltage, temperature variations
- **Integration Tests**: SoC-level integration scenarios

### PDK Support

**40nm Ultra Low Power (Cadence PDK)**:
- **Behavioral Models**: Realistic analog circuit modeling
- **Spectre Netlists**: Ready-to-simulate circuit descriptions
- **Virtuoso Schematics**: Layout-ready design files
- **Calibre LVS**: Layout vs. schematic verification
- **Supply Voltage**: 2.8V analog, 1.8V digital

**Sky130 Open-Source PDK**:
- **Xschem Schematics**: Open-source schematic capture
- **Magic Layout**: Open-source layout editor
- **ngspice Simulation**: Open-source circuit simulation
- **Netgen LVS**: Open-source layout vs. schematic verification
- **Supply Voltage**: 5.0V analog (high-voltage transistors), 1.8V digital
- **Technology**: 130nm SkyWater process

## 📚 Documentation

- **[Developer_Guide.md](Developer_Guide.md)** - Comprehensive development guide with AI-assisted workflows
- **[docs/architecture.md](docs/architecture.md)** - Detailed ADC architecture and design decisions
- **[docs/waveforms.md](docs/waveforms.md)** - Simulation waveforms and timing analysis
- **[rtl/cadence_pdk/README.md](rtl/cadence_pdk/README.md)** - Cadence PDK integration guide
- **[analog/README.md](analog/README.md)** - Sky130 PDK integration guide (Xschem, Magic, ngspice)
- **[vyges-metadata.json](vyges-metadata.json)** - Complete Vyges metadata specification

## 🛠️ Development Tools

This IP is designed to work with the complete Vyges ecosystem:

- **Vyges CLI** - Command-line interface for IP development and automation
- **Vyges Catalog** - IP catalog and discovery platform
- **Vyges IDE** - Integrated development environment with mixed-signal support
- **AI-assisted development** - Comprehensive AI context and guidance for analog design
- **Cadence Virtuoso** - Layout and schematic design integration
- **Spectre/Calibre** - Analog simulation and verification tools

## 📄 License

Apache-2.0 License - see [LICENSE](LICENSE) for details.

**Important**: The Apache-2.0 license applies to the **hardware IP content** (RTL, documentation, testbenches, etc.) that you create using this template. The template structure, build processes, tooling workflows, and AI context/processing engine are provided as-is for your use but are not themselves licensed under Apache-2.0.

For detailed licensing information, see [LICENSE_SCOPE.md](LICENSE_SCOPE.md).

## 🤝 Contributing

Contributions are welcome! Please see [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

## 📞 Support

- **Documentation**: [Developer_Guide.md](Developer_Guide.md)
- **Issues**: [GitHub Issues](https://github.com/vyges/programmable-adc/issues)
- **Discussions**: [GitHub Discussions](https://github.com/vyges/programmable-adc/discussions)
- **Cadence PDK Support**: [flow/cadence/README.md](flow/cadence/README.md)
