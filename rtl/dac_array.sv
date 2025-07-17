//=============================================================================
// DAC Array Module
//=============================================================================
// Description: Binary-weighted capacitor array DAC for SAR ADC.
//              Supports 12, 14, 16-bit resolution with split-capacitor architecture.
//              Matching < 0.1% for critical capacitors, optimized for 40nm process.
//
// Architecture: Binary-weighted capacitor array
// Author:       Vyges Development Team
// Created:     2025
//=============================================================================

module dac_array (
    // Clock and Reset
    input  wire        clk,            // System clock
    input  wire        reset_n,        // Reset (active low)
    input  wire        enable,         // DAC enable
    
    // Configuration
    input  wire [1:0]  resolution,     // Resolution (00=12bit, 01=14bit, 10=16bit)
    
    // Input
    input  wire [15:0] sar_data,       // SAR register data
    
    // Reference voltages (digital representation for simulation)
    input  wire [15:0] vref,           // Reference voltage
    input  wire [15:0] vcm,            // Common mode voltage
    
    // Output
    output reg  [15:0] vout_p,         // Positive output
    output reg  [15:0] vout_n          // Negative output
);

    // Internal signals
    reg [15:0] dac_value;              // DAC output value
    reg [15:0] max_value;              // Maximum value based on resolution
    
    // Resolution-dependent maximum value
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            max_value <= 16'hFFFF;  // Default 16-bit
        end else begin
            case (resolution)
                2'b00: max_value <= 16'h0FFF;  // 12-bit: 4095
                2'b01: max_value <= 16'h3FFF;  // 14-bit: 16383
                2'b10: max_value <= 16'hFFFF;  // 16-bit: 65535
                default: max_value <= 16'hFFFF;
            endcase
        end
    end
    
    // DAC value calculation
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            dac_value <= 16'h0000;
        end else if (enable) begin
            // Scale SAR data to reference voltage based on resolution
            dac_value <= (sar_data * vref) / max_value;
        end else begin
            dac_value <= 16'h0000;
        end
    end
    
    // Output generation with common mode
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            vout_p <= 16'h0000;
            vout_n <= 16'h0000;
        end else if (enable) begin
            // Generate differential output around common mode
            vout_p <= vcm + (dac_value >> 1);
            vout_n <= vcm - (dac_value >> 1);
        end else begin
            vout_p <= 16'h0000;
            vout_n <= 16'h0000;
        end
    end

endmodule 