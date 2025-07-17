//=============================================================================
// APB Slave Interface Module
//=============================================================================
// Description: APB slave interface for Programmable ADC with register map
//              and control signal generation.
//
// Register Map:
//   0x00: Control Register (R/W)
//   0x04: Status Register (RO)
//   0x08: Data Register (RO)
//   0x0C: Configuration Register (R/W)
//
// Author:       Vyges Development Team
// Created:     2025
//=============================================================================

module apb_interface (
    // APB Interface
    input  wire        PCLK,           // APB clock
    input  wire        PRESETn,        // APB reset (active low)
    input  wire [7:0]  PADDR,          // APB address bus
    input  wire [31:0] PWDATA,         // APB write data
    output reg  [31:0] PRDATA,         // APB read data
    input  wire        PENABLE,        // APB enable signal
    input  wire        PWRITE,         // APB write enable
    input  wire        PSEL,           // APB select signal
    output reg         PREADY,         // APB ready signal
    
    // ADC Control Signals
    output reg  [1:0]  pga_gain,       // PGA gain selection
    output reg  [1:0]  resolution,     // ADC resolution
    output reg  [1:0]  channel_sel,    // Channel selection
    output reg         start_conv,     // Start conversion
    output reg         adc_enable,     // ADC enable
    output reg         irq_enable,     // Interrupt enable
    output reg         auto_mode,      // Auto conversion mode
    
    // ADC Status Signals
    input  wire [15:0] adc_data,       // ADC conversion result
    input  wire        busy,           // Conversion busy
    input  wire        valid           // Data valid
);

    // Register definitions
    reg [31:0] control_reg;    // 0x00: Control Register
    reg [31:0] status_reg;     // 0x04: Status Register
    reg [31:0] data_reg;       // 0x08: Data Register
    reg [31:0] config_reg;     // 0x0C: Configuration Register
    
    // APB state machine
    reg [1:0] apb_state;
    localparam IDLE = 2'b00;
    localparam SETUP = 2'b01;
    localparam ACCESS = 2'b10;
    
    // APB state machine
    always @(posedge PCLK or negedge PRESETn) begin
        if (!PRESETn) begin
            apb_state <= IDLE;
            PREADY <= 1'b0;
        end else begin
            case (apb_state)
                IDLE: begin
                    if (PSEL && !PENABLE) begin
                        apb_state <= SETUP;
                        PREADY <= 1'b0;
                    end
                end
                
                SETUP: begin
                    if (PSEL && PENABLE) begin
                        apb_state <= ACCESS;
                        PREADY <= 1'b0;
                    end else begin
                        apb_state <= IDLE;
                        PREADY <= 1'b0;
                    end
                end
                
                ACCESS: begin
                    apb_state <= IDLE;
                    PREADY <= 1'b1;
                end
                
                default: begin
                    apb_state <= IDLE;
                    PREADY <= 1'b0;
                end
            endcase
        end
    end
    
    // Register read/write logic
    always @(posedge PCLK or negedge PRESETn) begin
        if (!PRESETn) begin
            control_reg <= 32'h0;
            config_reg <= 32'h0;
            PRDATA <= 32'h0;
        end else begin
            if (PSEL && PENABLE && PREADY) begin
                if (PWRITE) begin
                    // Write operation
                    case (PADDR)
                        8'h00: control_reg <= PWDATA;
                        8'h0C: config_reg <= PWDATA;
                        // Other addresses are read-only
                    endcase
                end else begin
                    // Read operation
                    case (PADDR)
                        8'h00: PRDATA <= control_reg;
                        8'h04: PRDATA <= {24'h0, busy, valid, channel_sel, 4'h0};
                        8'h08: PRDATA <= {16'h0, adc_data};
                        8'h0C: PRDATA <= config_reg;
                        default: PRDATA <= 32'h0;
                    endcase
                end
            end
        end
    end
    
    // Control signal generation from control register
    always @(posedge PCLK or negedge PRESETn) begin
        if (!PRESETn) begin
            pga_gain <= 2'b00;      // Gain = 1
            resolution <= 2'b10;    // 16-bit
            channel_sel <= 2'b00;   // Channel 0
            start_conv <= 1'b0;
            adc_enable <= 1'b0;
        end else begin
            pga_gain <= control_reg[23:22];
            resolution <= control_reg[21:20];
            channel_sel <= control_reg[19:18];
            start_conv <= control_reg[17];
            adc_enable <= control_reg[16];
        end
    end
    
    // Configuration signal generation from config register
    always @(posedge PCLK or negedge PRESETn) begin
        if (!PRESETn) begin
            irq_enable <= 1'b0;
            auto_mode <= 1'b0;
        end else begin
            irq_enable <= config_reg[7];
            auto_mode <= config_reg[6];
        end
    end
    
    // Auto-clear start_conv signal after one clock cycle
    always @(posedge PCLK or negedge PRESETn) begin
        if (!PRESETn) begin
            start_conv <= 1'b0;
        end else begin
            if (start_conv) begin
                start_conv <= 1'b0;
            end
        end
    end

endmodule 