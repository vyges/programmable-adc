[![Vyges IP](https://img.shields.io/badge/vyges-programmable--adc--ip-blue)](https://github.com/vyges/programmable-adc)
![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)
![Build](https://github.com/vyges/programmable-adc/actions/workflows/test.yml/badge.svg)
![SystemVerilog](https://img.shields.io/badge/SystemVerilog-2025-brightgreen)
![Cadence PDK](https://img.shields.io/badge/Cadence%20PDK-Supported-orange)

# Programmable ADC IP

A high-performance, programmable Analog-to-Digital Converter (ADC) IP core designed for mixed-signal SoC integration. Features include:

🔧 **Core Features:**
• Configurable resolution (8-16 bit)
• Programmable sampling rates (1-100 MSPS)
• Built-in PGA with gain control
• SAR DAC with calibration
• Advanced sample & hold circuit
• Real-time performance monitoring

🛠 **Design & Verification:**
• SystemVerilog RTL implementation
• Analog schematic entry (Xschem)
• Mixed-signal simulation (ngspice/Xyce)
• Layout design (Magic/KLayout)
• DRC/LVS verification (Netgen)
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
   - Check Cadence PDK integration in `flow/cadence/`
   - See [Developer_Guide.md](Developer_Guide.md) for advanced usage

## 🔧 Project Structure

```
programmable-adc/
├── rtl/                    # SystemVerilog RTL implementation
│   ├── programmable_adc.sv # Main ADC module
│   ├── pga_model.sv        # Programmable Gain Amplifier
│   ├── sar_dac.sv          # SAR DAC with calibration
│   ├── comparator.sv       # High-speed comparator
│   └── sample_hold.sv      # Sample & Hold circuit
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
│   ├── cadence/           # Cadence PDK integration
│   ├── openlane/          # Open-source ASIC flow
│   └── vivado/            # FPGA synthesis flow
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

### Cadence PDK Integration
- **Behavioral Models**: Realistic analog circuit modeling
- **Spectre Netlists**: Ready-to-simulate circuit descriptions
- **Virtuoso Schematics**: Layout-ready design files
- **Calibre LVS**: Layout vs. schematic verification

## 📚 Documentation

- **[Developer_Guide.md](Developer_Guide.md)** - Comprehensive development guide with AI-assisted workflows
- **[docs/architecture.md](docs/architecture.md)** - Detailed ADC architecture and design decisions
- **[docs/waveforms.md](docs/waveforms.md)** - Simulation waveforms and timing analysis
- **[flow/cadence/README.md](flow/cadence/README.md)** - Cadence PDK integration guide
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
