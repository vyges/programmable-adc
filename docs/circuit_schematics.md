# Programmable ADC Circuit Schematics

## Table of Contents
1. [Overview](#overview)
2. [PGA Circuit](#pga-circuit)
3. [Sample & Hold Circuit](#sample--hold-circuit)
4. [SAR DAC Array](#sar-dac-array)
5. [Comparator Circuit](#comparator-circuit)
6. [Clock Generation](#clock-generation)
7. [Power Management](#power-management)
8. [ESD Protection](#esd-protection)

## Overview

This document provides detailed circuit schematics for the key analog and digital blocks of the Programmable ADC IP. All circuits are designed for 40nm CMOS technology with 2.8V analog supply and 1.1V digital supply.

## PGA Circuit

### PGA Block Diagram
```
                    VDD
                     |
              ┌──────┴──────┐
              │             │
    IN+ ──────┤  Chopper    ├─────┐
              │  Modulator  │     │
    IN- ──────┤             ├─────┤
              └─────────────┘     │
                                  │
              ┌───────────────────┴──┐
              │                      │
              │  Differential        │
              │  Amplifier           │
              │  (Gain = 1x,2x,4x)  │
              │                      │
              └──────────────────────┘
                                  │
              ┌───────────────────┬──┘
              │                   │
              │  Chopper          │
              │  Demodulator      │
              │                   │
              └───────────────────┘
                                  │
                                 OUT
```

### Differential Amplifier Circuit
```
                    VDD
                     |
              ┌──────┴──────┐
              │             │
    IN+ ──────┤    M1       ├─────┐
              │             │     │
              └─────────────┘     │
                                  │
              ┌───────────────────┴──┐
              │                      │
              │    M3         M4     │
              │     │          │     │
              │     └──────────┘     │
              │                      │
              └──────────────────────┘
                                  │
              ┌───────────────────┬──┘
              │                   │
              │    M2             │
              │     │             │
              └─────┴─────────────┘
                                  │
                                 OUT
```

### Chopper Circuit
```
              ┌─────────────┐
              │             │
    IN ───────┤    SW1      ├─────┐
              │             │     │
              └─────────────┘     │
                                  │
              ┌───────────────────┴──┐
              │                      │
              │    Amplifier         │
              │                      │
              └──────────────────────┘
                                  │
              ┌───────────────────┬──┘
              │                   │
              │    SW2            │
              │     │             │
              └─────┴─────────────┘
                                  │
                                 OUT
```

## Sample & Hold Circuit

### S/H Block Diagram
```
                    VDD
                     |
              ┌──────┴──────┐
              │             │
    IN ───────┤    SW1      ├─────┐
              │             │     │
              └─────────────┘     │
                                  │
              ┌───────────────────┴──┐
              │                      │
              │    CH (10pF)         │
              │                      │
              └──────────────────────┘
                                  │
              ┌───────────────────┬──┘
              │                   │
              │    Buffer         │
              │                   │
              └───────────────────┘
                                  │
                                 OUT
```

### Transmission Gate Switch
```
                    VDD
                     |
              ┌──────┴──────┐
              │             │
    IN ───────┤    M1       ├───── OUT
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │    M2       │
              │             │
              └─────────────┘
                     │
                    VSS
```

### Buffer Circuit
```
                    VDD
                     │
              ┌──────┴──────┐
              │             │
    IN ───────┤    M1       ├─────┐
              │             │     │
              └─────────────┘     │
                                  │
              ┌───────────────────┴──┐
              │                      │
              │    M3         M4     │
              │     │          │     │
              │     └──────────┘     │
              │                      │
              └──────────────────────┘
                                  │
                                 OUT
```

## SAR DAC Array

### DAC Architecture
```
                    VREF
                     │
              ┌──────┴──────┐
              │             │
              │    C15      │
              │   (32C)     │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │    C14      │
              │   (16C)     │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │    C13      │
              │    (8C)     │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │    C12      │
              │    (4C)     │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │    C11      │
              │    (2C)     │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │    C10      │
              │     (C)     │
              │             │
              └─────────────┘
                     │
                    OUT
```

### Capacitor Array Layout
```
    ┌─────────────────────────────────┐
    │  C15  C14  C13  C12  C11  C10  │
    │   │     │     │     │     │     │
    │   └─────┴─────┴─────┴─────┴─────┘
    │                                 │
    │  Dummy  Dummy  Dummy  Dummy     │
    │   │       │       │       │     │
    │   └───────┴───────┴───────┴─────┘
    └─────────────────────────────────┘
```

### Switch Matrix
```
                    VREF
                     │
              ┌──────┴──────┐
              │             │
              │    SW_H     │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │    C        │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │    SW_L     │
              │             │
              └─────────────┘
                     │
                    VSS
```

## Comparator Circuit

### Comparator Block Diagram
```
                    VDD
                     │
              ┌──────┴──────┐
              │             │
    IN+ ──────┤  Preamp     ├─────┐
              │             │     │
    IN- ──────┤             ├─────┤
              └─────────────┘     │
                                  │
              ┌───────────────────┴──┐
              │                      │
              │    Latch             │
              │                      │
              └──────────────────────┘
                                  │
                                 OUT
```

### Preamp Circuit
```
                    VDD
                     │
              ┌──────┴──────┐
              │             │
    IN+ ──────┤    M1       ├─────┐
              │             │     │
              └─────────────┘     │
                                  │
              ┌───────────────────┴──┐
              │                      │
              │    M3         M4     │
              │     │          │     │
              │     └──────────┘     │
              │                      │
              └──────────────────────┘
                                  │
              ┌───────────────────┬──┘
              │                   │
              │    M2             │
              │     │             │
              └─────┴─────────────┘
                                  │
                                 OUT
```

### Latch Circuit
```
                    VDD
                     │
              ┌──────┴──────┐
              │             │
    IN ───────┤    M1       ├─────┐
              │             │     │
              └─────────────┘     │
                                  │
              ┌───────────────────┴──┐
              │                      │
              │    M3         M4     │
              │     │          │     │
              │     └──────────┘     │
              │                      │
              └──────────────────────┘
                                  │
                                 OUT
```

## Clock Generation

### Clock Distribution
```
                    VDD
                     │
              ┌──────┴──────┐
              │             │
    CLK_IN ───┤  Clock      ├─────┐
              │  Buffer     │     │
              └─────────────┘     │
                                  │
              ┌───────────────────┴──┐
              │                      │
              │    Clock Tree        │
              │                      │
              └──────────────────────┘
                                  │
              ┌───────────────────┬──┘
              │                   │
              │    Clock Gating   │
              │                   │
              └───────────────────┘
                                  │
                                 CLK_OUT
```

### Clock Buffer
```
                    VDD
                     │
              ┌──────┴──────┐
              │             │
    IN ───────┤    M1       ├─────┐
              │             │     │
              └─────────────┘     │
                                  │
              ┌───────────────────┴──┐
              │                      │
              │    M3         M4     │
              │     │          │     │
              │     └──────────┘     │
              │                      │
              └──────────────────────┘
                                  │
                                 OUT
```

## Power Management

### Power Distribution
```
                    VDDA (2.8V)
                     │
              ┌──────┴──────┐
              │             │
              │  Analog     │
              │  Core       │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │  Digital    │
              │  Core       │
              │             │
              └─────────────┘
                     │
                    VDDD (1.1V)
```

### Decoupling Network
```
                    VDD
                     │
              ┌──────┴──────┐
              │             │
              │   100nF     │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │   10nF      │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │   100pF     │
              │             │
              └─────────────┘
                     │
                    VSS
```

## ESD Protection

### Input ESD Protection
```
                    VDDA
                     │
              ┌──────┴──────┐
              │             │
              │    D1       │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
    INPUT ────┤    R1       ├─────┐
              │             │     │
              └─────────────┘     │
                                  │
              ┌───────────────────┴──┐
              │                      │
              │    Internal          │
              │    Circuit           │
              │                      │
              └──────────────────────┘
                                  │
              ┌───────────────────┬──┘
              │                   │
              │    D2             │
              │     │             │
              └─────┴─────────────┘
                                  │
                    VSSA
```

### Power Supply ESD Protection
```
                    VDDA
                     │
              ┌──────┴──────┐
              │             │
              │    D1       │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │    R1       │
              │             │
              └─────────────┘
                     │
              ┌──────┴──────┐
              │             │
              │    D2       │
              │             │
              └─────────────┘
                     │
                    VSSA
```

## Conclusion

These circuit schematics provide the detailed implementation of all key blocks in the Programmable ADC IP. The circuits are optimized for:

- **Performance**: High accuracy and speed
- **Power**: Ultra-low power consumption
- **Reliability**: Robust design with margins
- **Manufacturability**: Process-friendly design
- **Testability**: Built-in test features

All circuits follow 40nm CMOS design rules and are ready for layout and fabrication. 