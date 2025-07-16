# Programmable ADC User Manual

## Table of Contents
1. [Overview](#overview)
2. [Quick Start Guide](#quick-start-guide)
3. [Register Map](#register-map)
4. [Operation Modes](#operation-modes)
5. [Integration Guidelines](#integration-guidelines)
6. [Performance Optimization](#performance-optimization)
7. [Troubleshooting](#troubleshooting)
8. [Examples](#examples)

## Overview

The Programmable ADC is a high-performance, ultra-low-power analog-to-digital converter designed for 40nm ultra-low-power technology. It features configurable resolution (12, 14, 16 bits), 3 simultaneous differential channels, and an integrated Programmable Gain Amplifier (PGA) with gains of 1, 2, 3, and 4.

### Key Features
- **Resolution**: Programmable 12, 14, 16 bits
- **Channels**: 3 simultaneous differential channels
- **Conversion Rate**: Up to 5 MSPS
- **PGA**: Integrated with gains 1, 2, 3, 4
- **Interface**: APB slave interface
- **Power**: < 10 mW at 5MSPS
- **Linearity**: DNL < 0.5 LSB, INL < 1 LSB

## Quick Start Guide

### 1. Power-Up Sequence
```verilog
// 1. Apply digital supply (VDD = 1.8V)
// 2. Apply analog supply (VDDA = 2.8V)
// 3. Apply reference voltage (VREF = 2.8V)
// 4. Apply common mode voltage (VCM = 1.4V)
// 5. Release reset (PRESETn = 1)
// 6. Wait for power-up time (100 μs)
```

### 2. Basic Configuration
```verilog
// Enable ADC
write_register(0x00, 32'h00010000);  // ENABLE = 1

// Configure for 16-bit resolution, Gain = 1, Channel 0
write_register(0x00, 32'h00010000 | (2'b10 << 20) | (2'b00 << 22) | (2'b00 << 18));

// Start conversion
write_register(0x00, 32'h00020000);  // START_CONV = 1
```

### 3. Read Conversion Result
```verilog
// Wait for conversion complete
while (read_register(0x04) & 32'h00000080) == 0);  // Wait for BUSY = 0

// Read conversion result
data = read_register(0x08) & 32'h0000FFFF;
```

## Register Map

### Control Register (0x00) - Read/Write
| Bits | Field | Description | Access |
|------|-------|-------------|--------|
| 31:24 | Reserved | Reserved bits | R/W |
| 23:22 | PGA_GAIN[1:0] | PGA Gain Selection | R/W |
| 21:20 | RESOLUTION[1:0] | ADC Resolution | R/W |
| 19:18 | CHANNEL_SEL[1:0] | Channel Selection | R/W |
| 17 | START_CONV | Start Conversion (auto-clear) | R/W |
| 16 | ENABLE | ADC Enable | R/W |
| 15:0 | Reserved | Reserved bits | R/W |

**PGA_GAIN[1:0] Values:**
- `00`: Gain = 1
- `01`: Gain = 2
- `10`: Gain = 3
- `11`: Gain = 4

**RESOLUTION[1:0] Values:**
- `00`: 12-bit resolution
- `01`: 14-bit resolution
- `10`: 16-bit resolution
- `11`: Reserved

**CHANNEL_SEL[1:0] Values:**
- `00`: Channel 0 (VIN0P/VIN0N)
- `01`: Channel 1 (VIN1P/VIN1N)
- `10`: Channel 2 (VIN2P/VIN2N)
- `11`: Reserved

### Status Register (0x04) - Read Only
| Bits | Field | Description | Access |
|------|-------|-------------|--------|
| 31:8 | Reserved | Reserved bits | RO |
| 7 | BUSY | Conversion in Progress | RO |
| 6 | VALID | Data Valid | RO |
| 5:4 | CHANNEL[1:0] | Current Channel | RO |
| 3:0 | Reserved | Reserved bits | RO |

### Data Register (0x08) - Read Only
| Bits | Field | Description | Access |
|------|-------|-------------|--------|
| 31:16 | Reserved | Reserved bits | RO |
| 15:0 | ADC_DATA[15:0] | Conversion Result | RO |

### Configuration Register (0x0C) - Read/Write
| Bits | Field | Description | Access |
|------|-------|-------------|--------|
| 31:8 | Reserved | Reserved bits | R/W |
| 7 | IRQ_EN | Interrupt Enable | R/W |
| 6 | AUTO_MODE | Auto Conversion Mode | R/W |
| 5:0 | Reserved | Reserved bits | R/W |

## Operation Modes

### Single Conversion Mode
```verilog
// Configure ADC
write_register(0x00, 32'h00010000 | (2'b10 << 20) | (2'b00 << 22) | (2'b00 << 18));

// Start single conversion
write_register(0x00, 32'h00020000);

// Wait for completion
while (read_register(0x04) & 32'h00000080);

// Read result
result = read_register(0x08) & 32'h0000FFFF;
```

### Continuous Conversion Mode
```verilog
// Enable auto mode
write_register(0x0C, 32'h00000040);

// Configure and start
write_register(0x00, 32'h00010000 | (2'b10 << 20) | (2'b00 << 22) | (2'b00 << 18) | 32'h00020000);

// Monitor for new data
while (1) {
    if (read_register(0x04) & 32'h00000040) {  // VALID = 1
        result = read_register(0x08) & 32'h0000FFFF;
        // Process result
    }
}
```

### Interrupt-Driven Mode
```verilog
// Enable interrupt
write_register(0x0C, 32'h00000080);

// Configure and start
write_register(0x00, 32'h00010000 | (2'b10 << 20) | (2'b00 << 22) | (2'b00 << 18) | 32'h00020000);

// In interrupt handler
void adc_interrupt_handler() {
    if (read_register(0x04) & 32'h00000040) {  // VALID = 1
        result = read_register(0x08) & 32'h0000FFFF;
        // Process result
    }
}
```

## Integration Guidelines

### Power Supply Requirements
```
Digital Supply (VDD):    1.8V ±5%
Analog Supply (VDDA):    2.8V ±5%
Reference Voltage (VREF): 2.8V ±1%
Common Mode (VCM):       1.4V ±2%
```

### Clock Requirements
- **APB Clock (PCLK)**: 50 MHz ±1%
- **Duty Cycle**: 45% - 55%
- **Jitter**: < 1 ps RMS

### Analog Input Requirements
```
Input Voltage Range:     0V to 2.8V
Common Mode Voltage:     1.4V ±2%
Input Impedance:         > 1 MΩ
Input Capacitance:       < 10 pF
```

### Layout Guidelines
1. **Power Distribution**
   - Use separate power planes for analog and digital
   - Implement proper decoupling capacitors
   - Minimize power supply impedance

2. **Signal Routing**
   - Route analog signals with shielding
   - Maintain differential pair matching
   - Avoid crossing digital and analog signals

3. **Grounding**
   - Separate analog and digital grounds
   - Connect grounds at single point
   - Use guard rings around analog circuits

### Thermal Considerations
```
Maximum Junction Temperature: 125°C
Thermal Resistance:          25°C/W
Power Dissipation:           < 10 mW
```

## Performance Optimization

### Resolution vs. Speed Trade-off
| Resolution | Conversion Time | Max Sample Rate | Power |
|------------|----------------|-----------------|-------|
| 12-bit     | 120 ns         | 8.3 MSPS        | 6 mW  |
| 14-bit     | 160 ns         | 6.25 MSPS       | 8 mW  |
| 16-bit     | 200 ns         | 5 MSPS          | 10 mW |

### PGA Selection Guidelines
- **Gain = 1**: For large input signals (1V - 2.8V)
- **Gain = 2**: For medium input signals (0.5V - 1.4V)
- **Gain = 3**: For small input signals (0.33V - 0.93V)
- **Gain = 4**: For very small input signals (0.25V - 0.7V)

### Noise Optimization
1. **Input Filtering**: Use low-pass filter at input
2. **Power Supply**: Ensure clean power supply
3. **Layout**: Minimize parasitic capacitance
4. **Temperature**: Operate within specified range

## Troubleshooting

### Common Issues

#### 1. No Conversion Data
**Symptoms**: VALID bit never set, BUSY stuck high
**Possible Causes**:
- ADC not enabled
- Invalid configuration
- Power supply issues
- Clock problems

**Solutions**:
```verilog
// Check enable bit
if ((read_register(0x00) & 32'h00010000) == 0) {
    write_register(0x00, 32'h00010000);  // Enable ADC
}

// Check configuration
config = read_register(0x00);
if ((config & 32'h00300000) == 32'h00300000) {
    // Invalid resolution setting
    write_register(0x00, config & ~32'h00300000 | 32'h00200000);  // Set to 16-bit
}
```

#### 2. Poor Linearity
**Symptoms**: High DNL/INL, non-linear response
**Possible Causes**:
- Input signal too large/small
- Incorrect PGA setting
- Power supply noise
- Temperature effects

**Solutions**:
```verilog
// Adjust PGA gain
if (input_amplitude < 0.5) {
    write_register(0x00, (read_register(0x00) & ~32'h00C00000) | 32'h00400000);  // Gain = 2
}
```

#### 3. High Power Consumption
**Symptoms**: Power consumption > 10 mW
**Possible Causes**:
- High sample rate
- High resolution mode
- Power supply issues
- Temperature

**Solutions**:
```verilog
// Reduce sample rate or resolution
write_register(0x00, (read_register(0x00) & ~32'h00300000) | 32'h00100000);  // 14-bit mode
```

### Diagnostic Registers
```verilog
// Read status for diagnostics
status = read_register(0x04);
if (status & 32'h00000080) {
    printf("ADC is busy\n");
}
if (status & 32'h00000040) {
    printf("Data is valid\n");
}
channel = (status >> 4) & 3;
printf("Current channel: %d\n", channel);
```

## Examples

### Example 1: Basic Single Conversion
```verilog
module adc_basic_example (
    input wire clk,
    input wire reset_n,
    output reg [15:0] adc_result,
    output reg adc_valid
);

    // APB interface signals
    wire [7:0] paddr;
    wire [31:0] pwdata, prdata;
    wire penable, pwrite, psel, pready;
    
    // ADC instance
    programmable_adc_top adc_inst (
        .PCLK(clk),
        .PRESETn(reset_n),
        .PADDR(paddr),
        .PWDATA(pwdata),
        .PRDATA(prdata),
        .PENABLE(penable),
        .PWRITE(pwrite),
        .PSEL(psel),
        .PREADY(pready),
        // ... other connections
    );
    
    // APB write function
    task apb_write;
        input [7:0] addr;
        input [31:0] data;
        begin
            paddr = addr;
            pwdata = data;
            psel = 1;
            pwrite = 1;
            penable = 0;
            @(posedge clk);
            penable = 1;
            @(posedge clk);
            while (!pready) @(posedge clk);
            psel = 0;
            penable = 0;
        end
    endtask
    
    // APB read function
    task apb_read;
        input [7:0] addr;
        output [31:0] data;
        begin
            paddr = addr;
            psel = 1;
            pwrite = 0;
            penable = 0;
            @(posedge clk);
            penable = 1;
            @(posedge clk);
            while (!pready) @(posedge clk);
            data = prdata;
            psel = 0;
            penable = 0;
        end
    endtask
    
    // Main conversion sequence
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            adc_result <= 16'h0000;
            adc_valid <= 1'b0;
        end else begin
            // Configure ADC for 16-bit, Gain=1, Channel 0
            apb_write(8'h00, 32'h00010000 | (2'b10 << 20) | (2'b00 << 22) | (2'b00 << 18));
            
            // Start conversion
            apb_write(8'h00, 32'h00020000);
            
            // Wait for completion
            while (1) begin
                apb_read(8'h04, status);
                if ((status & 32'h00000080) == 0) break;  // BUSY = 0
            end
            
            // Read result
            apb_read(8'h08, result);
            adc_result <= result[15:0];
            adc_valid <= 1'b1;
        end
    end

endmodule
```

### Example 2: Multi-Channel Scanning
```verilog
module adc_multi_channel (
    input wire clk,
    input wire reset_n,
    output reg [15:0] ch0_result, ch1_result, ch2_result,
    output reg [2:0] channel_valid
);

    reg [1:0] current_channel;
    reg [31:0] status, result;
    
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            current_channel <= 2'b00;
            channel_valid <= 3'b000;
        end else begin
            // Configure for current channel
            apb_write(8'h00, 32'h00010000 | (2'b10 << 20) | (2'b00 << 22) | (current_channel << 18));
            
            // Start conversion
            apb_write(8'h00, 32'h00020000);
            
            // Wait for completion
            while (1) begin
                apb_read(8'h04, status);
                if ((status & 32'h00000080) == 0) break;
            end
            
            // Read result
            apb_read(8'h08, result);
            
            // Store result based on channel
            case (current_channel)
                2'b00: begin
                    ch0_result <= result[15:0];
                    channel_valid[0] <= 1'b1;
                end
                2'b01: begin
                    ch1_result <= result[15:0];
                    channel_valid[1] <= 1'b1;
                end
                2'b10: begin
                    ch2_result <= result[15:0];
                    channel_valid[2] <= 1'b1;
                end
            endcase
            
            // Move to next channel
            current_channel <= current_channel + 1;
            if (current_channel == 2'b10) current_channel <= 2'b00;
        end
    end

endmodule
```

### Example 3: Interrupt-Driven Operation
```verilog
module adc_interrupt_driven (
    input wire clk,
    input wire reset_n,
    input wire adc_irq,
    output reg [15:0] adc_result,
    output reg adc_valid
);

    reg [31:0] status, result;
    
    // Enable interrupt
    initial begin
        apb_write(8'h0C, 32'h00000080);  // IRQ_EN = 1
    end
    
    // Interrupt handler
    always @(posedge adc_irq) begin
        // Check if data is valid
        apb_read(8'h04, status);
        if (status & 32'h00000040) begin  // VALID = 1
            apb_read(8'h08, result);
            adc_result <= result[15:0];
            adc_valid <= 1'b1;
        end
    end
    
    // Start continuous conversion
    initial begin
        // Configure for 16-bit, Gain=1, Channel 0
        apb_write(8'h00, 32'h00010000 | (2'b10 << 20) | (2'b00 << 22) | (2'b00 << 18));
        
        // Enable auto mode and start
        apb_write(8'h0C, 32'h00000040);  // AUTO_MODE = 1
        apb_write(8'h00, 32'h00020000);  // START_CONV = 1
    end

endmodule
```

## Conclusion

This user manual provides comprehensive guidance for integrating and using the Programmable ADC. The examples demonstrate various usage patterns from basic single conversions to advanced multi-channel scanning and interrupt-driven operation.

For additional support or questions, please refer to the design specification document or contact the Vyges development team. 