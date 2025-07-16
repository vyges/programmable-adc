//=============================================================================
// Programmable Gain Amplifier (PGA) Module
//=============================================================================
// Description: Programmable Gain Amplifier with configurable gains of 1, 2, 3, 4.
//              Uses switched capacitor architecture with op-amp for high precision.
//              Bandwidth > 2 MHz, noise < 3 mV RMS, power < 2 mW.
//
// Gains: 1, 2, 3, 4 (software configurable)
// Architecture: Switched capacitor with op-amp
// Author:       Vyges Development Team
// Created:      2025-01-27
//=============================================================================

module pga_stage (
    // Clock and Reset
    input  wire        clk,            // System clock
    input  wire        reset_n,        // Reset (active low)
    input  wire        enable,         // PGA enable
    
    // Configuration
    input  wire [1:0]  gain,           // Gain selection (00=1, 01=2, 10=3, 11=4)
    
    // Analog Inputs (digital representation for simulation)
    input  wire [15:0] vin_p,          // Positive input
    input  wire [15:0] vin_n,          // Negative input
    
    // Analog Outputs (digital representation for simulation)
    output reg  [15:0] vout_p,         // Positive output
    output reg  [15:0] vout_n          // Negative output
);

    // Internal signals
    reg [15:0] vin_diff;               // Differential input
    reg [15:0] vout_diff;              // Differential output
    reg [15:0] gain_multiplier;        // Gain multiplier value
    
    // Calculate differential input
    always @(*) begin
        vin_diff = vin_p - vin_n;
    end
    
    // Gain multiplier selection
    always @(*) begin
        case (gain)
            2'b00: gain_multiplier = 16'h0001;  // Gain = 1
            2'b01: gain_multiplier = 16'h0002;  // Gain = 2
            2'b10: gain_multiplier = 16'h0003;  // Gain = 3
            2'b11: gain_multiplier = 16'h0004;  // Gain = 4
            default: gain_multiplier = 16'h0001;
        endcase
    end
    
    // Gain multiplication (simplified for simulation)
    always @(*) begin
        vout_diff = vin_diff * gain_multiplier;
    end
    
    // Output generation with common mode restoration
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            vout_p <= 16'h0000;
            vout_n <= 16'h0000;
        end else if (enable) begin
            // Restore common mode (simplified - in real implementation this would be VCM)
            vout_p <= 16'h8000 + (vout_diff >> 1);
            vout_n <= 16'h8000 - (vout_diff >> 1);
        end else begin
            vout_p <= 16'h0000;
            vout_n <= 16'h0000;
        end
    end

endmodule 