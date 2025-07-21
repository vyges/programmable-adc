# Analog Design Directory

This directory contains analog design files for the programmable ADC, following the Efabless open-source analog design flow recommendations.

## Directory Structure

```
analog/
├── xschem/          # Schematic entry and symbol files (Xschem)
├── magic/           # Layout database files (Magic)
├── netlist/         # SPICE netlists for simulation
├── gds/             # Final GDS layout files
├── lef/             # Abstract layout views (LEF)
└── macros/          # Reusable analog components (symbolic links)
```

## Tool Integration

### Schematic Entry (xschem/)
- **Purpose**: Create and edit analog circuit schematics
- **Tool**: Xschem (open-source schematic editor)
- **Files**: `.sch` (schematic), `.sym` (symbols)
- **Output**: SPICE netlists for simulation

### Layout Design (magic/)
- **Purpose**: Create physical layout of analog circuits
- **Tool**: Magic (open-source layout editor)
- **Files**: `.mag` (Magic database)
- **Features**: Device extraction, parasitic extraction, DRC checking

### Netlist Generation (netlist/)
- **Purpose**: SPICE netlists for circuit simulation
- **Sources**: Xschem schematics, Magic layout extraction
- **Tools**: ngspice, Xyce for simulation
- **Files**: `.sp` (SPICE netlists)

### Layout Files (gds/, lef/)
- **GDS**: Final layout for fabrication (Graphic Design System)
- **LEF**: Abstract layout views for digital integration
- **Tools**: Magic, KLayout for viewing and editing

### Reusable Components (macros/)
- **Purpose**: Symbolic links to reusable analog IP blocks
- **Structure**: Each macro should be its own repository
- **Examples**: Bandgap references, PLLs, DACs, comparators

## Workflow Integration

This analog design flow integrates with the existing digital flow:

1. **Digital RTL** (`../rtl/`) - Digital control logic
2. **Analog Circuits** (`analog/`) - Analog signal path
3. **Mixed-Signal Simulation** (`../simulation/`) - Combined verification
4. **Layout Verification** (`../layout/`) - DRC/LVS checks
5. **Integration** (`../integration/`) - System-level integration

## References

- [Efabless Analog Design Flow](http://opencircuitdesign.com/analog_flow/index.html)
- [Open Circuit Design Tools](http://opencircuitdesign.com/)
- [Open PDKs](https://github.com/google/skywater-pdk) 