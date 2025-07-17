//=============================================================================
// Programmable ADC - PGA Circuit Implementation
//=============================================================================
// Description: Programmable Gain Amplifier with chopper stabilization
//              Supports gains of 1x, 2x, 4x with high CMRR and PSRR
// Author: Vyges IP Development Team
// Date: 2025
//=============================================================================

module pga_circuit #(
    parameter real VDDA = 2.8,
    parameter real VDDD = 1.1,
    parameter real VCM = 1.4,  // Common mode voltage (VDDA/2)
    parameter real IBIAS = 100e-6,  // Bias current in amperes
    parameter real CLOAD = 10e-12,  // Load capacitance in farads
    parameter real RLOAD = 100e3    // Load resistance in ohms
)(
    // Clock and control
    input  logic        clk_i,           // Clock input
    input  logic        reset_n_i,       // Active low reset
    input  logic        chopper_clk_i,   // Chopper clock (1MHz)
    input  logic        enable_i,        // Enable signal
    
    // Gain control
    input  logic [1:0]  gain_sel_i,      // Gain selection: 00=1x, 01=2x, 10=4x
    
    // Analog inputs
    input  real         vin_p_i,         // Positive input voltage
    input  real         vin_n_i,         // Negative input voltage
    input  real         vcm_i,           // Common mode input
    
    // Analog outputs
    output real         vout_p_o,        // Positive output voltage
    output real         vout_n_o,        // Negative output voltage
    
    // Status and control
    output logic        ready_o,         // Ready signal
    output logic        overload_o,      // Overload detection
    output real         offset_o,        // Offset voltage
    output real         gain_error_o     // Gain error
);

    //=============================================================================
    // Internal signals and parameters
    //=============================================================================
    
    // Chopper control signals
    logic chopper_phase1, chopper_phase2;
    logic chopper_phase1_d, chopper_phase2_d;
    
    // Input chopper signals
    real vin_p_chopped, vin_n_chopped;
    real vin_p_chopped_d, vin_n_chopped_d;
    
    // Amplifier signals
    real vdiff_in, vdiff_out;
    real vcm_in, vcm_out;
    real vout_p_amp, vout_n_amp;
    
    // Output chopper signals
    real vout_p_chopped, vout_n_chopped;
    
    // Gain control signals
    real gain_factor;
    logic [1:0] gain_sel_sync;
    
    // Bias and reference signals
    real vbias_n, vbias_p;
    real vref_p, vref_n;
    
    // Error signals
    real offset_error, gain_error;
    real cmrr_error, psrr_error;
    
    //=============================================================================
    // Chopper clock generation and synchronization
    //=============================================================================
    
    // Chopper phase generation
    always_ff @(posedge chopper_clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            chopper_phase1 <= 1'b0;
            chopper_phase2 <= 1'b1;
        end else begin
            chopper_phase1 <= ~chopper_phase1;
            chopper_phase2 <= ~chopper_phase2;
        end
    end
    
    // Synchronize chopper phases to main clock
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            chopper_phase1_d <= 1'b0;
            chopper_phase2_d <= 1'b1;
        end else begin
            chopper_phase1_d <= chopper_phase1;
            chopper_phase2_d <= chopper_phase2;
        end
    end
    
    //=============================================================================
    // Input chopper implementation
    //=============================================================================
    
    // Input chopper switches (transmission gates)
    always_comb begin
        if (chopper_phase1_d) begin
            vin_p_chopped = vin_p_i;
            vin_n_chopped = vin_n_i;
        end else begin
            vin_p_chopped = vin_n_i;
            vin_n_chopped = vin_p_i;
        end
    end
    
    // Add chopper switch imperfections
    always_comb begin
        // Charge injection and clock feedthrough effects
        real charge_injection = 0.1e-12;  // 0.1pC
        real clock_feedthrough = 1e-3;    // 1mV
        
        vin_p_chopped_d = vin_p_chopped + 
                         (chopper_phase1_d ? charge_injection : -charge_injection) +
                         (chopper_phase1_d ? clock_feedthrough : -clock_feedthrough);
        
        vin_n_chopped_d = vin_n_chopped + 
                         (chopper_phase1_d ? -charge_injection : charge_injection) +
                         (chopper_phase1_d ? -clock_feedthrough : clock_feedthrough);
    end
    
    //=============================================================================
    // Differential amplifier implementation
    //=============================================================================
    
    // Calculate differential input
    always_comb begin
        vdiff_in = vin_p_chopped_d - vin_n_chopped_d;
        vcm_in = (vin_p_chopped_d + vin_n_chopped_d) / 2.0;
    end
    
    // Differential amplifier with gain control
    always_comb begin
        // Gain factor calculation
        case (gain_sel_sync)
            2'b00: gain_factor = 1.0;    // 1x gain
            2'b01: gain_factor = 2.0;    // 2x gain
            2'b10: gain_factor = 4.0;    // 4x gain
            default: gain_factor = 1.0;
        endcase
        
        // Amplifier transfer function
        // DC gain: A0 = gm * ro = 2.5mS * 100kΩ = 250
        real A0 = 250.0;
        real f3db = 10e6 / gain_factor;  // Bandwidth scales with gain
        
        // Add amplifier imperfections
        offset_error = 0.5e-3;  // 0.5mV offset
        gain_error = 0.001;     // 0.1% gain error
        cmrr_error = 1e-3;      // CMRR error
        psrr_error = 1e-3;      // PSRR error
        
        // Amplifier output calculation
        vdiff_out = (vdiff_in + offset_error) * A0 * gain_factor * (1.0 + gain_error) +
                   (vcm_in - VCM) * cmrr_error +
                   (VDDA - 2.8) * psrr_error;
        
        // Limit output swing
        if (vdiff_out > VDDA - 0.2) vdiff_out = VDDA - 0.2;
        if (vdiff_out < 0.2) vdiff_out = 0.2;
        
        // Convert to differential outputs
        vout_p_amp = VCM + vdiff_out / 2.0;
        vout_n_amp = VCM - vdiff_out / 2.0;
    end
    
    //=============================================================================
    // Output chopper implementation
    //=============================================================================
    
    // Output chopper switches
    always_comb begin
        if (chopper_phase2_d) begin
            vout_p_chopped = vout_p_amp;
            vout_n_chopped = vout_n_amp;
        end else begin
            vout_p_chopped = vout_n_amp;
            vout_n_chopped = vout_p_amp;
        end
    end
    
    //=============================================================================
    // Output buffer and load
    //=============================================================================
    
    // Output buffer with load
    always_comb begin
        // Buffer transfer function (unity gain with finite bandwidth)
        real buffer_bw = 50e6;  // 50MHz buffer bandwidth
        real buffer_delay = 10e-9;  // 10ns delay
        
        // Add buffer imperfections
        real buffer_offset = 0.1e-3;  // 0.1mV buffer offset
        
        vout_p_o = vout_p_chopped + buffer_offset;
        vout_n_o = vout_n_chopped + buffer_offset;
        
        // Load effects
        vout_p_o = vout_p_o * RLOAD / (RLOAD + 1.0);  // Output resistance effect
        vout_n_o = vout_n_o * RLOAD / (RLOAD + 1.0);
    end
    
    //=============================================================================
    // Control and status logic
    //=============================================================================
    
    // Gain selection synchronization
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            gain_sel_sync <= 2'b00;
        end else begin
            gain_sel_sync <= gain_sel_i;
        end
    end
    
    // Ready signal generation
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            ready_o <= 1'b0;
        end else begin
            ready_o <= enable_i;
        end
    end
    
    // Overload detection
    always_comb begin
        overload_o = (abs(vdiff_in) > 1.0) ||  // Input overload
                    (abs(vdiff_out) > VDDA - 0.2);  // Output overload
    end
    
    // Status outputs
    always_comb begin
        offset_o = offset_error;
        gain_error_o = gain_error;
    end
    
    //=============================================================================
    // Power consumption calculation
    //=============================================================================
    
    // Static power calculation
    real static_power;
    always_comb begin
        static_power = IBIAS * VDDA;  // Static power from bias current
    end
    
    // Dynamic power calculation
    real dynamic_power;
    always_comb begin
        real switching_freq = 1e6;  // 1MHz chopper frequency
        real switching_cap = 1e-12;  // 1pF switching capacitance
        dynamic_power = 0.5 * switching_cap * VDDA * VDDA * switching_freq;
    end
    
    //=============================================================================
    // Assertions and coverage
    //=============================================================================
    
    // Input range assertion
    property input_range_check;
        @(posedge clk_i) disable iff (!reset_n_i)
        (vin_p_i >= 0) && (vin_p_i <= VDDA) &&
        (vin_n_i >= 0) && (vin_n_i <= VDDA);
    endproperty
    
    assert property (input_range_check)
    else $error("PGA input voltage out of range");
    
    // Output range assertion
    property output_range_check;
        @(posedge clk_i) disable iff (!reset_n_i)
        (vout_p_o >= 0) && (vout_p_o <= VDDA) &&
        (vout_n_o >= 0) && (vout_n_o <= VDDA);
    endproperty
    
    assert property (output_range_check)
    else $error("PGA output voltage out of range");
    
    // Gain selection coverage
    covergroup gain_coverage @(posedge clk_i);
        gain_sel_cp: coverpoint gain_sel_i {
            bins gain_1x = {2'b00};
            bins gain_2x = {2'b01};
            bins gain_4x = {2'b10};
            bins invalid = {2'b11};
        }
    endgroup
    
    gain_coverage gain_cov = new();
    
endmodule 