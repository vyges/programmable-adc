//=============================================================================
// Comparator Module
//=============================================================================
// Description: Dynamic latch comparator for SAR ADC.
//              Resolution < 1 mV, speed < 10 ns decision time, power < 1 mW.
//
// Architecture: Dynamic latch comparator
// Author:       Vyges Development Team
// Created:     2025
//=============================================================================

module comparator (
    // Clock and Reset
    input  wire        clk,            // System clock
    input  wire        reset_n,        // Reset (active low)
    input  wire        enable,         // Comparator enable
    
    // Analog Inputs (digital representation for simulation)
    input  wire [15:0] vin_p,          // Positive input
    input  wire [15:0] vin_n,          // Negative input
    
    // Reference Inputs (digital representation for simulation)
    input  wire [15:0] vref_p,         // Positive reference
    input  wire [15:0] vref_n,         // Negative reference
    
    // Output
    output reg         vout            // Comparator output
);

    // Internal signals
    reg [15:0] diff_input;             // Differential input
    reg [15:0] diff_ref;               // Differential reference
    reg        comp_result;            // Comparison result
    
    // Calculate differential signals
    always @(*) begin
        diff_input = vin_p - vin_n;
        diff_ref = vref_p - vref_n;
    end
    
    // Comparison logic
    always @(*) begin
        if (diff_input > diff_ref) begin
            comp_result = 1'b1;  // Input > Reference
        end else begin
            comp_result = 1'b0;  // Input <= Reference
        end
    end
    
    // Output generation with clocked latch behavior
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            vout <= 1'b0;
        end else if (enable) begin
            vout <= comp_result;
        end else begin
            vout <= 1'b0;
        end
    end

endmodule 