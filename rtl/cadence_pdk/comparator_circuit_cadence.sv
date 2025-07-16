//=============================================================================
// Programmable ADC - Comparator Circuit Implementation (Cadence PDK)
//=============================================================================
// Description: High-speed comparator optimized for Cadence PDK
//              Uses behavioral models and specifications from /docs
// Author: Vyges IP Development Team
// Date: 2024
//=============================================================================

`include "disciplines.vams"

module comparator_circuit_cadence #(
    parameter real VDDA = 2.8,
    parameter real VDDD = 1.1,
    parameter real VCM = 1.4,
    parameter real IBIAS = 30e-6,
    parameter real PREAMP_GAIN = 60.0,
    parameter real PREAMP_BW = 10e6,
    parameter real LATCH_TIME = 8e-9,
    parameter real HYSTERESIS_MAX = 10e-3,
    parameter real TEMP = 27.0
)(
    // Clock and control
    input  logic        clk_i,
    input  logic        reset_n_i,
    input  logic        enable_i,
    
    // Comparator control
    input  logic        latch_enable_i,
    input  logic        reset_latch_i,
    input  logic [3:0]  hysteresis_i,
    
    // Calibration control
    input  logic        cal_enable_i,
    input  logic [7:0]  cal_offset_i,
    input  logic        cal_valid_i,
    
    // Analog inputs (electrical discipline)
    input  electrical   vin_p_i,
    input  electrical   vin_n_i,
    input  electrical   vcm_i,
    
    // Digital outputs
    output logic        comp_out_o,
    output logic        comp_out_valid_o,
    output logic        metastable_o,
    
    // Status and monitoring
    output logic        ready_o,
    output real         offset_o,
    output real         hysteresis_o,
    output real         noise_o,
    output real         delay_o
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
    parameter real W1 = 80e-6;      // Preamp input width (80μm)
    parameter real L1 = 0.4e-6;     // Preamp input length (0.4μm)
    parameter real W3 = 40e-6;      // Preamp load width (40μm)
    parameter real L3 = 0.4e-6;     // Preamp load length (0.4μm)
    parameter real W5 = 30e-6;      // Latch width (30μm)
    parameter real L5 = 0.4e-6;     // Latch length (0.4μm)
    
    //=============================================================================
    // Internal signals and parameters
    //=============================================================================
    
    // Preamp signals (electrical discipline)
    electrical vdiff_in, vdiff_preamp;
    electrical vcm_in, vcm_preamp;
    electrical preamp_out_p, preamp_out_n;
    electrical preamp_offset, preamp_noise;
    
    // Latch signals
    electrical latch_in_p, latch_in_n;
    electrical latch_out_p, latch_out_n;
    electrical latch_regeneration, latch_metastable;
    
    // Calibration signals
    real cal_offset_voltage, cal_hysteresis_voltage;
    logic [7:0] cal_offset_sync, cal_hysteresis_sync;
    
    // Timing signals
    real propagation_delay, regeneration_time;
    logic latch_done, metastable_detected;
    
    // Performance monitoring
    real input_noise, decision_noise;
    real offset_error, hysteresis_error;
    
    // Control signals
    logic latch_phase, reset_phase;
    logic latch_phase_d, reset_phase_d;
    
    // Power supply signals
    electrical vdda, vssa;
    
    //=============================================================================
    // Power supply connections
    //=============================================================================
    
    assign vdda = VDDA;
    assign vssa = 0.0;
    
    //=============================================================================
    // Control logic implementation
    //=============================================================================
    
    // Latch control generation
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            latch_phase <= 1'b0;
            reset_phase <= 1'b1;
        end else begin
            latch_phase <= latch_enable_i && !reset_latch_i;
            reset_phase <= reset_latch_i && !latch_enable_i;
        end
    end
    
    // Synchronize control signals
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            latch_phase_d <= 1'b0;
            reset_phase_d <= 1'b1;
        end else begin
            latch_phase_d <= latch_phase;
            reset_phase_d <= reset_phase;
        end
    end
    
    //=============================================================================
    // Preamp implementation (Cadence behavioral)
    //=============================================================================
    
    // Input differential calculation
    analog begin
        V(vdiff_in) <+ V(vin_p_i) - V(vin_n_i);
        V(vcm_in) <+ (V(vin_p_i) + V(vin_n_i)) / 2.0;
    end
    
    // Preamp transfer function using Cadence behavioral model
    analog begin
        // Preamp specifications from component specs
        real preamp_gm = 2.0e-3;      // 2mS transconductance
        real preamp_ro = 150e3;       // 150kΩ output resistance
        real preamp_cap = 1e-12;      // 1pF load capacitance
        
        // Preamp imperfections from component specs
        real preamp_offset_value = 0.8e-3;       // 0.8mV offset
        real preamp_noise_density = 10e-9;       // 10nV/√Hz
        
        // Preamp noise calculation
        real noise_bandwidth = PREAMP_BW / 1.57;  // Effective noise bandwidth
        real preamp_noise_rms = preamp_noise_density * $sqrt(noise_bandwidth);
        real preamp_noise_value = preamp_noise_rms * $random();
        
        // Preamp gain calculation using Cadence behavioral model
        real dc_gain = preamp_gm * preamp_ro;
        real ac_gain = dc_gain / (1.0 + (2.0 * $pi * PREAMP_BW * preamp_cap * preamp_ro));
        
        // Preamp output calculation with Cadence behavioral model
        real preamp_input = V(vdiff_in) + preamp_offset_value + preamp_noise_value;
        V(vdiff_preamp) <+ preamp_input * ac_gain;
        
        // Common mode output
        V(vcm_preamp) <+ V(vcm_in);
        
        // Differential outputs
        V(preamp_out_p) <+ V(vcm_preamp) + V(vdiff_preamp) / 2.0;
        V(preamp_out_n) <+ V(vcm_preamp) - V(vdiff_preamp) / 2.0;
        
        // Limit output swing
        if (V(preamp_out_p) > VDDA - 0.2) V(preamp_out_p) <+ VDDA - 0.2;
        if (V(preamp_out_p) < 0.2) V(preamp_out_p) <+ 0.2;
        if (V(preamp_out_n) > VDDA - 0.2) V(preamp_out_n) <+ VDDA - 0.2;
        if (V(preamp_out_n) < 0.2) V(preamp_out_n) <+ 0.2;
        
        // Store values for monitoring
        V(preamp_offset) <+ preamp_offset_value;
        V(preamp_noise) <+ preamp_noise_value;
    end
    
    //=============================================================================
    // Calibration implementation
    //=============================================================================
    
    // Calibration code synchronization
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            cal_offset_sync <= 8'h00;
            cal_hysteresis_sync <= 8'h00;
        end else if (cal_valid_i) begin
            cal_offset_sync <= cal_offset_i;
            cal_hysteresis_sync <= {4'h0, hysteresis_i};
        end
    end
    
    // Calibration voltage calculation
    always_comb begin
        if (cal_enable_i) begin
            // Offset calibration (8-bit resolution, ±10mV range)
            cal_offset_voltage = (cal_offset_sync - 8'h80) * 20e-3 / 256.0;
            
            // Hysteresis calibration (4-bit resolution, 0-10mV range)
            cal_hysteresis_voltage = cal_hysteresis_sync[3:0] * HYSTERESIS_MAX / 16.0;
        end else begin
            cal_offset_voltage = 0.0;
            cal_hysteresis_voltage = 0.0;
        end
    end
    
    //=============================================================================
    // Latch implementation (Cadence behavioral)
    //=============================================================================
    
    // Latch input with calibration
    analog begin
        V(latch_in_p) <+ V(preamp_out_p) + cal_offset_voltage + cal_hysteresis_voltage;
        V(latch_in_n) <+ V(preamp_out_n) + cal_offset_voltage - cal_hysteresis_voltage;
    end
    
    // Latch transfer function using Cadence behavioral model
    analog begin
        if (reset_phase_d) begin
            // Reset phase - latch outputs at common mode
            V(latch_out_p) <+ VCM;
            V(latch_out_n) <+ VCM;
            V(latch_regeneration) <+ 0.0;
            V(latch_metastable) <+ 0.0;
        end else if (latch_phase_d) begin
            // Latch phase - regeneration using Cadence behavioral model
            real input_diff = V(latch_in_p) - V(latch_in_n);
            real regeneration_gain = 10.0;  // Regeneration gain
            real time_step = 1.0 / 100e6;   // 10ns time step
            
            // Regeneration equation: dV/dt = gain * V
            V(latch_regeneration) <+ V(latch_regeneration) + 
                                   regeneration_gain * input_diff * time_step;
            
            // Latch outputs with Cadence behavioral model
            if (V(latch_regeneration) > 0.1) begin
                V(latch_out_p) <+ VDDA - 0.1;
                V(latch_out_n) <+ 0.1;
            end else if (V(latch_regeneration) < -0.1) begin
                V(latch_out_p) <+ 0.1;
                V(latch_out_n) <+ VDDA - 0.1;
            end else begin
                // Metastable region
                V(latch_out_p) <+ VCM + V(latch_regeneration) / 2.0;
                V(latch_out_n) <+ VCM - V(latch_regeneration) / 2.0;
                V(latch_metastable) <+ 1.0;
            end
        end
    end
    
    //=============================================================================
    // Output logic
    //=============================================================================
    
    // Digital output generation
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            comp_out_o <= 1'b0;
            comp_out_valid_o <= 1'b0;
            metastable_o <= 1'b0;
        end else begin
            if (latch_phase_d) begin
                // Decision logic
                if (V(latch_regeneration) > 0.1) begin
                    comp_out_o <= 1'b1;
                    comp_out_valid_o <= 1'b1;
                    metastable_o <= 1'b0;
                end else if (V(latch_regeneration) < -0.1) begin
                    comp_out_o <= 1'b0;
                    comp_out_valid_o <= 1'b1;
                    metastable_o <= 1'b0;
                end else begin
                    // Metastable - maintain previous output
                    comp_out_valid_o <= 1'b0;
                    metastable_o <= 1'b1;
                end
            end else begin
                comp_out_valid_o <= 1'b0;
                metastable_o <= 1'b0;
            end
        end
    end
    
    //=============================================================================
    // Timing calculation (Cadence behavioral)
    //=============================================================================
    
    // Propagation delay calculation
    analog begin
        // Preamp delay
        real preamp_delay = 1.0 / (2.0 * $pi * PREAMP_BW);
        
        // Latch delay
        real latch_delay = LATCH_TIME;
        
        // Total propagation delay
        propagation_delay = preamp_delay + latch_delay;
        
        // Regeneration time
        regeneration_time = V(latch_regeneration);
    end
    
    // Latch completion detection
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            latch_done <= 1'b0;
            metastable_detected <= 1'b0;
        end else begin
            if (latch_phase_d) begin
                if (abs(V(latch_regeneration)) > 0.1) begin
                    latch_done <= 1'b1;
                    metastable_detected <= 1'b0;
                end else begin
                    latch_done <= 1'b0;
                    metastable_detected <= 1'b1;
                end
            end else begin
                latch_done <= 1'b0;
                metastable_detected <= 1'b0;
            end
        end
    end
    
    //=============================================================================
    // Performance monitoring (Cadence behavioral)
    //=============================================================================
    
    // Noise calculation
    analog begin
        // Input referred noise
        input_noise = V(preamp_noise);
        
        // Decision noise
        real decision_threshold = 0.1;  // 100mV decision threshold
        decision_noise = input_noise / PREAMP_GAIN;
    end
    
    // Offset and hysteresis monitoring
    analog begin
        offset_error = V(preamp_offset) - cal_offset_voltage;
        hysteresis_error = cal_hysteresis_voltage - (hysteresis_i * HYSTERESIS_MAX / 16.0);
    end
    
    //=============================================================================
    // Status outputs
    //=============================================================================
    
    // Ready signal generation
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            ready_o <= 1'b0;
        end else begin
            ready_o <= enable_i && !latch_phase_d;
        end
    end
    
    // Status output assignment
    always_comb begin
        offset_o = offset_error;
        hysteresis_o = cal_hysteresis_voltage;
        noise_o = input_noise;
        delay_o = propagation_delay;
    end
    
    //=============================================================================
    // Power consumption calculation (Cadence behavioral)
    //=============================================================================
    
    // Static power calculation
    analog begin
        real static_power = IBIAS * V(vdda);  // Static power from bias current
        
        // Dynamic power calculation
        real switching_freq = 5e6;    // 5MHz switching frequency
        real switching_cap = 0.1e-12; // 0.1pF switching capacitance
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
    else $error("Comparator input voltage out of range");
    
    // Output range assertion
    property output_range_check;
        @(posedge clk_i) disable iff (!reset_n_i)
        (V(latch_out_p) >= 0) && (V(latch_out_p) <= VDDA) &&
        (V(latch_out_n) >= 0) && (V(latch_out_n) <= VDDA);
    endproperty
    
    assert property (output_range_check)
    else $error("Comparator output voltage out of range");
    
    // Hysteresis coverage
    covergroup hysteresis_coverage @(posedge clk_i);
        hysteresis_cp: coverpoint hysteresis_i {
            bins hyst_0 = {4'h0};
            bins hyst_low = {[4'h1:4'h3]};
            bins hyst_mid = {[4'h4:4'hB]};
            bins hyst_high = {[4'hC:4'hE]};
            bins hyst_max = {4'hF};
        }
    endgroup
    
    hysteresis_coverage hyst_cov = new();
    
    //=============================================================================
    // Cadence-specific performance monitoring
    //=============================================================================
    
    // Offset monitoring
    always @(posedge clk_i) begin
        if (latch_done) begin
            if (abs(offset_error) > 1e-3) begin
                $warning("Comparator offset error: %f V", offset_error);
            end
        end
    end
    
    // Metastability monitoring
    always @(posedge clk_i) begin
        if (metastable_detected) begin
            $warning("Comparator metastability detected");
        end
    end
    
    // Noise monitoring
    always @(posedge clk_i) begin
        if (latch_done) begin
            if (abs(input_noise) > 50e-6) begin
                $warning("Comparator noise: %f V", input_noise);
            end
        end
    end
    
endmodule 