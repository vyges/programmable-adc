//=============================================================================
// Programmable ADC Top-Level Module
//=============================================================================
// Description: High-performance, ultra-low-power programmable ADC with 
//              configurable resolution (12, 14, 16 bits), 3 simultaneous 
//              differential channels, and integrated PGA (gains 1,2,3,4).
//              Achieves 5MSPS conversion rate with excellent linearity.
//
// Architecture: Successive Approximation Register (SAR)
// Technology:   40nm Ultra Low Power
// Author:       Vyges Development Team
// Created:     2025
//=============================================================================

module programmable_adc_top (
    // Clock and Reset
    input  wire        PCLK,           // APB clock (50 MHz)
    input  wire        PRESETn,        // APB reset (active low)
    
    // APB Interface
    input  wire [7:0]  PADDR,          // APB address bus
    input  wire [31:0] PWDATA,         // APB write data
    output wire [31:0] PRDATA,         // APB read data
    input  wire        PENABLE,        // APB enable signal
    input  wire        PWRITE,         // APB write enable
    input  wire        PSEL,           // APB select signal
    output wire        PREADY,         // APB ready signal
    
    // Analog Interfaces
    input  wire        VIN0P,          // Channel 0 positive input
    input  wire        VIN0N,          // Channel 0 negative input
    input  wire        VIN1P,          // Channel 1 positive input
    input  wire        VIN1N,          // Channel 1 negative input
    input  wire        VIN2P,          // Channel 2 positive input
    input  wire        VIN2N,          // Channel 2 negative input
    input  wire        VREF,           // Reference voltage (2.8V)
    input  wire        VCM,            // Common mode voltage (1.4V)
    
    // Power Supply
    input  wire        VDDA,           // Analog supply (2.8V)
    input  wire        VSSA,           // Analog ground
    
    // Status and Control Outputs
    output wire        adc_irq,        // ADC interrupt output
    output wire        busy_o,         // Conversion busy indicator
    output wire        valid_o,        // Data valid indicator
    output wire [15:0] data_o,         // ADC conversion result
    output wire [1:0]  channel_o       // Current channel number
);

    // Internal signals
    wire [1:0]  pga_gain;
    wire [1:0]  resolution;
    wire [1:0]  channel_sel;
    wire        start_conv;
    wire        adc_enable;
    wire        irq_enable;
    wire        auto_mode;
    
    wire [15:0] pga_out_p, pga_out_n;
    wire [15:0] sh_out_p, sh_out_n;
    wire [15:0] dac_out_p, dac_out_n;
    wire        comp_out;
    wire [15:0] sar_data;
    wire        sar_busy;
    wire        sar_valid;
    
    // APB Interface Instance
    apb_interface apb_if (
        .PCLK(PCLK),
        .PRESETn(PRESETn),
        .PADDR(PADDR),
        .PWDATA(PWDATA),
        .PRDATA(PRDATA),
        .PENABLE(PENABLE),
        .PWRITE(PWRITE),
        .PSEL(PSEL),
        .PREADY(PREADY),
        .pga_gain(pga_gain),
        .resolution(resolution),
        .channel_sel(channel_sel),
        .start_conv(start_conv),
        .adc_enable(adc_enable),
        .irq_enable(irq_enable),
        .auto_mode(auto_mode),
        .adc_data(sar_data),
        .busy(sar_busy),
        .valid(sar_valid)
    );
    
    // Channel Multiplexer
    wire [15:0] ch0_in_p, ch0_in_n;
    wire [15:0] ch1_in_p, ch1_in_n;
    wire [15:0] ch2_in_p, ch2_in_n;
    wire [15:0] selected_in_p, selected_in_n;
    
    // Convert analog inputs to digital representation (for simulation)
    assign ch0_in_p = (VIN0P > VCM) ? 16'h8000 : 16'h0000;
    assign ch0_in_n = (VIN0N > VCM) ? 16'h8000 : 16'h0000;
    assign ch1_in_p = (VIN1P > VCM) ? 16'h8000 : 16'h0000;
    assign ch1_in_n = (VIN1N > VCM) ? 16'h8000 : 16'h0000;
    assign ch2_in_p = (VIN2P > VCM) ? 16'h8000 : 16'h0000;
    assign ch2_in_n = (VIN2N > VCM) ? 16'h8000 : 16'h0000;
    
    // Channel selection multiplexer
    assign selected_in_p = (channel_sel == 2'b00) ? ch0_in_p :
                          (channel_sel == 2'b01) ? ch1_in_p :
                          (channel_sel == 2'b10) ? ch2_in_p : 16'h0000;
    
    assign selected_in_n = (channel_sel == 2'b00) ? ch0_in_n :
                          (channel_sel == 2'b01) ? ch1_in_n :
                          (channel_sel == 2'b10) ? ch2_in_n : 16'h0000;
    
    // PGA Stage
    pga_stage pga_inst (
        .clk(PCLK),
        .reset_n(PRESETn),
        .enable(adc_enable),
        .gain(pga_gain),
        .vin_p(selected_in_p),
        .vin_n(selected_in_n),
        .vout_p(pga_out_p),
        .vout_n(pga_out_n)
    );
    
    // Sample & Hold
    sample_hold sh_inst (
        .clk(PCLK),
        .reset_n(PRESETn),
        .enable(adc_enable),
        .sample_en(start_conv),
        .vin_p(pga_out_p),
        .vin_n(pga_out_n),
        .vout_p(sh_out_p),
        .vout_n(sh_out_n)
    );
    
    // SAR Controller
    sar_controller sar_ctrl (
        .clk(PCLK),
        .reset_n(PRESETn),
        .enable(adc_enable),
        .start_conv(start_conv),
        .resolution(resolution),
        .auto_mode(auto_mode),
        .vin_p(sh_out_p),
        .vin_n(sh_out_n),
        .dac_out_p(dac_out_p),
        .dac_out_n(dac_out_n),
        .comp_out(comp_out),
        .data_out(sar_data),
        .busy(sar_busy),
        .valid(sar_valid)
    );
    
    // DAC Array
    dac_array dac_inst (
        .clk(PCLK),
        .reset_n(PRESETn),
        .enable(adc_enable),
        .resolution(resolution),
        .sar_data(sar_data),
        .vref(VREF),
        .vcm(VCM),
        .vout_p(dac_out_p),
        .vout_n(dac_out_n)
    );
    
    // Comparator
    comparator comp_inst (
        .clk(PCLK),
        .reset_n(PRESETn),
        .enable(adc_enable),
        .vin_p(sh_out_p),
        .vin_n(sh_out_n),
        .vref_p(dac_out_p),
        .vref_n(dac_out_n),
        .vout(comp_out)
    );
    
    // Output assignments
    assign busy_o = sar_busy;
    assign valid_o = sar_valid;
    assign data_o = sar_data;
    assign channel_o = channel_sel;
    
    // Interrupt generation
    assign adc_irq = irq_enable && sar_valid;

endmodule 