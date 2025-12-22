# Analog Design Files - Sky130 PDK

This directory contains analog design files for the Sky130 open-source PDK implementation of the programmable ADC.

## Directory Structure

```
analog/
├── xschem/          # Xschem schematic files (.sch)
├── magic/           # Magic layout database files (.mag)
├── netlist/         # SPICE netlists (.sp, .cir)
├── gds/             # Final GDSII layout files (.gds)
├── lef/             # LEF abstract layout files (.lef)
└── macros/          # Reusable analog component libraries
```

## Sky130 PDK Configuration

### Technology Details
- **Process**: SkyWater 130nm
- **Analog Supply**: 5.0V (using high-voltage 5.0V transistors)
- **Digital Supply**: 1.8V (using standard 1.8V transistors)
- **Reference Voltage**: 5.0V
- **Common Mode**: 2.5V (VREF/2)

### Voltage Levels
- **Analog Input Range**: 0V to 5.0V (differential)
- **VDDA**: 5.0V ±5% (analog supply)
- **VDDD**: 1.8V ±5% (digital supply)
- **VREF**: 5.0V ±1% (reference voltage)
- **VCM**: 2.5V ±2% (common mode voltage)

## Tools and Workflow

### Schematic Entry: Xschem
- **Tool**: Xschem (open-source schematic editor)
- **Files**: `xschem/*.sch`
- **Purpose**: Create and edit analog circuit schematics
- **Components**: Use Sky130 device library (5.0V transistors for analog)

### Layout: Magic
- **Tool**: Magic (open-source layout editor)
- **Files**: `magic/*.mag`
- **Purpose**: Create physical layout from schematics
- **DRC**: Magic built-in DRC for Sky130
- **Export**: GDSII and LEF files

### Simulation: ngspice
- **Tool**: ngspice (open-source circuit simulator)
- **Files**: `netlist/*.sp`, `netlist/*.cir`
- **Purpose**: Transistor-level analog simulation
- **Models**: Sky130 device models (5.0V transistors)
- **Corners**: Process, voltage, temperature (PVT) corners

### LVS Verification: Netgen
- **Tool**: Netgen (open-source LVS tool)
- **Files**: `layout/lvs/`
- **Purpose**: Layout vs. Schematic verification
- **Input**: Magic layout (.mag) and Xschem netlist (.sp)

## Circuit Blocks

### PGA (Programmable Gain Amplifier)
- **Schematic**: `xschem/pga_circuit.sch`
- **Layout**: `magic/pga_circuit.mag`
- **Netlist**: `netlist/pga_circuit.sp`
- **Gains**: 1, 2, 3, 4 (programmable)
- **Supply**: 5.0V (analog)

### SAR DAC (Successive Approximation Register DAC)
- **Schematic**: `xschem/sar_dac_circuit.sch`
- **Layout**: `magic/sar_dac_circuit.mag`
- **Netlist**: `netlist/sar_dac_circuit.sp`
- **Resolution**: 12, 14, 16 bits (programmable)
- **Supply**: 5.0V (analog)

### Comparator
- **Schematic**: `xschem/comparator_circuit.sch`
- **Layout**: `magic/comparator_circuit.mag`
- **Netlist**: `netlist/comparator_circuit.sp`
- **Supply**: 5.0V (analog)

### Sample & Hold
- **Schematic**: `xschem/sample_hold_circuit.sch`
- **Layout**: `magic/sample_hold_circuit.mag`
- **Netlist**: `netlist/sample_hold_circuit.sp`
- **Supply**: 5.0V (analog)

## Workflow

### 1. Schematic Design (Xschem)
```bash
# Open Xschem
xschem xschem/pga_circuit.sch

# Edit schematic using Sky130 device library
# Use 5.0V high-voltage transistors for analog circuits
# Use 1.8V standard transistors for digital circuits
```

### 2. Generate Netlist
```bash
# Xschem can export SPICE netlist
# Or use manual netlist generation
```

### 3. Simulation (ngspice)
```bash
# Run simulation
ngspice netlist/pga_circuit.sp

# Or with corners
ngspice -b netlist/pga_circuit_corners.sp
```

### 4. Layout (Magic)
```bash
# Open Magic with Sky130 PDK
magic -d XR -T sky130A magic/pga_circuit.mag

# Create layout from schematic
# Use Sky130 DRC rules
```

### 5. LVS Verification (Netgen)
```bash
# Run LVS
netgen -batch lvs \
  layout/lvs/pga_circuit.sp \
  magic/pga_circuit.mag \
  sky130A
```

### 6. Export GDS/LEF
```bash
# From Magic, export GDS
gds write gds/pga_circuit.gds

# Export LEF
lef write lef/pga_circuit.lef
```

## Sky130 Device Library

### Transistor Types
- **5.0V High-Voltage**: For analog circuits (PGA, DAC, Comparator, S&H)
- **1.8V Standard**: For digital circuits (SAR controller, APB interface)

### Key Devices
- **NMOS/PMOS**: 5.0V and 1.8V variants
- **Resistors**: Poly, diffused, well
- **Capacitors**: MIM, MOS, PIP
- **Diodes**: Standard, ESD protection

## Integration with Digital RTL

The analog blocks (PGA, DAC, Comparator, S&H) are designed in Xschem/Magic, while the digital control (SAR controller, APB interface) is in SystemVerilog RTL.

**Mixed-Signal Integration**:
- Analog blocks: Xschem schematics → Magic layout
- Digital blocks: SystemVerilog RTL → OpenLane/OpenRoad (Sky130 digital flow)
- Interface: Analog-digital boundary at sample & hold and DAC outputs

## References

- **Sky130 PDK**: https://github.com/google/skywater-pdk
- **Xschem**: https://xschem.sourceforge.io/
- **Magic**: http://opencircuitdesign.com/magic/
- **ngspice**: http://ngspice.sourceforge.net/
- **Netgen**: http://opencircuitdesign.com/netgen/

## Notes

- **Power Domains**: Separate analog (5.0V) and digital (1.8V) power domains
- **Grounding**: Separate analog (VSSA) and digital (VSSD) grounds
- **Isolation**: Proper isolation between analog and digital domains
- **ESD Protection**: Include ESD protection on analog I/O pins
- **Noise**: Minimize digital noise coupling to analog circuits
