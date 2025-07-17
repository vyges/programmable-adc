//=============================================================================
// Programmable ADC - PGA Circuit Implementation (Cadence PDK)
//=============================================================================
// Description: Programmable Gain Amplifier optimized for Cadence PDK
//              Uses behavioral models and specifications from /docs
// Author: Vyges IP Development Team
// Date: 2025
//=============================================================================

`include "disciplines.vams"

module pga_circuit_cadence #(
    parameter real VDDA = 2.8,
    parameter real VDDD = 1.1,
    parameter real VCM = 1.4,
    parameter real IBIAS = 100e-6,
    parameter real CLOAD = 10e-12,
    parameter real RLOAD = 100e3,
    parameter real TEMP = 27.0
)(
    // Clock and control
    input  logic        clk_i,
    input  logic        reset_n_i,
    input  logic        chopper_clk_i,
    input  logic        enable_i,
    
    // Gain control
    input  logic [1:0]  gain_sel_i,
    
    // Analog inputs (electrical discipline)
    input  electrical   vin_p_i,
    input  electrical   vin_n_i,
    input  electrical   vcm_i,
    
    // Analog outputs (electrical discipline)
    output electrical   vout_p_o,
    output electrical   vout_n_o,
    
    // Status and control
    output logic        ready_o,
    output logic        overload_o,
    output real         offset_o,
    output real         gain_error_o
);

    //=============================================================================
    // Cadence PDK specific parameters
    //=============================================================================
    
    // Process parameters from Cadence PDK
    parameter real VTN = 0.45;      // NMOS threshold voltage
    parameter real VTP = -0.45;     // PMOS threshold voltage
    parameter real KP_N = 200e-6;   // NMOS transconductance parameter
    parameter real KP_P = 80e-6;    // PMOS transconductance parameter
    parameter real LAMBDA_N = 0.1;  // NMOS channel length modulation
    parameter real LAMBDA_P = 0.1;  // PMOS channel length modulation
    
    // Device sizing from component specifications
    parameter real W1 = 100e-6;     // Input pair width (100μm)
    parameter real L1 = 0.4e-6;     // Input pair length (0.4μm)
    parameter real W3 = 50e-6;      // Load width (50μm)
    parameter real L3 = 0.4e-6;     // Load length (0.4μm)
    parameter real W5 = 20e-6;      // Current source width (20μm)
    parameter real L5 = 0.4e-6;     // Current source length (0.4μm)
    
    //=============================================================================
    // Internal signals and parameters
    //=============================================================================
    
    // Chopper control signals
    logic chopper_phase1, chopper_phase2;
    logic chopper_phase1_d, chopper_phase2_d;
    
    // Input chopper signals
    electrical vin_p_chopped, vin_n_chopped;
    electrical vin_p_chopped_d, vin_n_chopped_d;
    
    // Amplifier signals
    electrical vdiff_in, vdiff_out;
    electrical vcm_in, vcm_out;
    electrical vout_p_amp, vout_n_amp;
    
    // Output chopper signals
    electrical vout_p_chopped, vout_n_chopped;
    
    // Gain control signals
    real gain_factor;
    logic [1:0] gain_sel_sync;
    
    // Bias and reference signals
    electrical vbias_n, vbias_p;
    electrical vref_p, vref_n;
    
    // Error signals
    real offset_error, gain_error;
    real cmrr_error, psrr_error;
    
    // Power supply signals
    electrical vdda, vssa;
    
    //=============================================================================
    // Power supply connections
    //=============================================================================
    
    assign vdda = VDDA;
    assign vssa = 0.0;
    
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
    // Input chopper implementation (Cadence behavioral)
    //=============================================================================
    
    // Input chopper switches using Cadence behavioral models
    analog begin
        // Chopper switch model with realistic imperfections
        real charge_injection = 0.1e-12;  // 0.1pC from specs
        real clock_feedthrough = 1e-3;    // 1mV from specs
        real switch_on_resistance = 100.0; // 100Ω from specs
        
        if (chopper_phase1_d) begin
            // Switch ON - transmission gate behavior
            V(vin_p_chopped) <+ V(vin_p_i) + 
                              (chopper_phase1_d ? charge_injection : -charge_injection) +
                              (chopper_phase1_d ? clock_feedthrough : -clock_feedthrough);
            V(vin_n_chopped) <+ V(vin_n_i) + 
                              (chopper_phase1_d ? -charge_injection : charge_injection) +
                              (chopper_phase1_d ? -clock_feedthrough : clock_feedthrough);
        end else begin
            // Switch OFF - high impedance
            V(vin_p_chopped) <+ V(vin_p_chopped_d);
            V(vin_n_chopped) <+ V(vin_n_chopped_d);
        end
        
        // Add switch noise (thermal noise)
        real kT = 4.0e-21;  // kT at room temperature
        real switch_noise = $sqrt(kT / (1e-12 * switch_on_resistance)) * $random();
        V(vin_p_chopped_d) <+ V(vin_p_chopped) + switch_noise;
        V(vin_n_chopped_d) <+ V(vin_n_chopped) - switch_noise;
    end
    
    //=============================================================================
    // Differential amplifier implementation (Cadence behavioral)
    //=============================================================================
    
    // Calculate differential input
    analog begin
        V(vdiff_in) <+ V(vin_p_chopped_d) - V(vin_n_chopped_d);
        V(vcm_in) <+ (V(vin_p_chopped_d) + V(vin_n_chopped_d)) / 2.0;
    end
    
    // Differential amplifier with Cadence behavioral model
    analog begin
        // Gain factor calculation
        case (gain_sel_sync)
            2'b00: gain_factor = 1.0;    // 1x gain
            2'b01: gain_factor = 2.0;    // 2x gain
            2'b10: gain_factor = 4.0;    // 4x gain
            default: gain_factor = 1.0;
        endcase
        
        // Amplifier transfer function using Cadence behavioral model
        // DC gain: A0 = gm * ro = 2.5mS * 100kΩ = 250
        real A0 = 250.0;
        real f3db = 10e6 / gain_factor;  // Bandwidth scales with gain
        
        // Add amplifier imperfections from component specs
        offset_error = 0.5e-3;  // 0.5mV offset
        gain_error = 0.001;     // 0.1% gain error
        cmrr_error = 1e-3;      // CMRR error
        psrr_error = 1e-3;      // PSRR error
        
        // Amplifier output calculation with Cadence behavioral model
        real vdiff_input = V(vdiff_in) + offset_error;
        real vcm_input = V(vcm_in) - VCM;
        real vdd_variation = V(vdda) - 2.8;
        
        V(vdiff_out) <+ vdiff_input * A0 * gain_factor * (1.0 + gain_error) +
                       vcm_input * cmrr_error +
                       vdd_variation * psrr_error;
        
        // Limit output swing
        if (V(vdiff_out) > VDDA - 0.2) V(vdiff_out) <+ VDDA - 0.2;
        if (V(vdiff_out) < 0.2) V(vdiff_out) <+ 0.2;
        
        // Convert to differential outputs
        V(vout_p_amp) <+ VCM + V(vdiff_out) / 2.0;
        V(vout_n_amp) <+ VCM - V(vdiff_out) / 2.0;
    end
    
    //=============================================================================
    // Output chopper implementation (Cadence behavioral)
    //=============================================================================
    
    // Output chopper switches
    analog begin
        if (chopper_phase2_d) begin
            V(vout_p_chopped) <+ V(vout_p_amp);
            V(vout_n_chopped) <+ V(vout_n_amp);
        end else begin
            V(vout_p_chopped) <+ V(vout_n_amp);
            V(vout_n_chopped) <+ V(vout_p_amp);
        end
    end
    
    //=============================================================================
    // Output buffer and load (Cadence behavioral)
    //=============================================================================
    
    // Output buffer with load
    analog begin
        // Buffer transfer function (unity gain with finite bandwidth)
        real buffer_bw = 50e6;  // 50MHz buffer bandwidth
        real buffer_delay = 10e-9;  // 10ns delay
        
        // Add buffer imperfections from component specs
        real buffer_offset = 0.1e-3;  // 0.1mV buffer offset
        real buffer_noise_density = 5e-9; // 5nV/√Hz
        
        // Buffer noise calculation
        real noise_bandwidth = buffer_bw / 1.57;  // Effective noise bandwidth
        real buffer_noise_rms = buffer_noise_density * $sqrt(noise_bandwidth);
        real buffer_noise = buffer_noise_rms * $random();
        
        // Buffer output calculation
        V(vout_p_o) <+ V(vout_p_chopped) + buffer_offset + buffer_noise;
        V(vout_n_o) <+ V(vout_n_chopped) + buffer_offset - buffer_noise;
        
        // Load effects
        real output_resistance = 1.0;  // 1Ω output resistance
        V(vout_p_o) <+ V(vout_p_o) * RLOAD / (RLOAD + output_resistance);
        V(vout_n_o) <+ V(vout_n_o) * RLOAD / (RLOAD + output_resistance);
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
        overload_o = (abs(V(vdiff_in)) > 1.0) ||  // Input overload
                    (abs(V(vdiff_out)) > VDDA - 0.2);  // Output overload
    end
    
    // Status outputs
    always_comb begin
        offset_o = offset_error;
        gain_error_o = gain_error;
    end
    
    //=============================================================================
    // Power consumption calculation (Cadence behavioral)
    //=============================================================================
    
    // Static power calculation
    analog begin
        real static_power;
        static_power = IBIAS * V(vdda);
        
        // Dynamic power calculation
        real switching_freq = 1e6;  // 1MHz chopper frequency
        real switching_cap = 1e-12;  // 1pF switching capacitance
        real dynamic_power = 0.5 * switching_cap * V(vdda) * V(vdda) * switching_freq;
        
        // Total power monitoring
        real total_power = static_power + dynamic_power;
    end
    
    //=============================================================================
    // Cadence-specific assertions and coverage
    //=============================================================================
    
    // Input range assertion
    property input_range_check;
        @(posedge clk_i) disable iff (!reset_n_i)
        (V(vin_p_i) >= 0) && (V(vin_p_i) <= VDDA) &&
        (V(vin_n_i) >= 0) && (V(vin_n_i) <= VDDA);
    endproperty
    
    assert property (input_range_check)
    else $error("PGA input voltage out of range");
    
    // Output range assertion
    property output_range_check;
        @(posedge clk_i) disable iff (!reset_n_i)
        (V(vout_p_o) >= 0) && (V(vout_p_o) <= VDDA) &&
        (V(vout_n_o) >= 0) && (V(vout_n_o) <= VDDA);
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
    
    //=============================================================================
    // Cadence-specific performance monitoring
    //=============================================================================
    
    // Performance monitoring using Cadence behavioral models
    always @(posedge clk_i) begin
        if (ready_o) begin
            // Monitor gain accuracy
            real actual_gain = V(vdiff_out) / V(vdiff_in);
            real gain_error_monitor = abs(actual_gain - gain_factor) / gain_factor;
            
            if (gain_error_monitor > 0.01) begin
                $warning("PGA gain error: %f%%", gain_error_monitor * 100.0);
            end
            
            // Monitor offset
            if (abs(offset_error) > 1e-3) begin
                $warning("PGA offset: %f V", offset_error);
            end
        end
    end
    
endmodule 