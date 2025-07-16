//=============================================================================
// Programmable ADC - Comparator Circuit Implementation
//=============================================================================
// Description: High-speed comparator with preamp and latch
//              Includes offset calibration and hysteresis control
// Author: Vyges IP Development Team
// Date: 2024
//=============================================================================

module comparator_circuit #(
    parameter real VDDA = 2.8,           // Analog supply voltage
    parameter real VDDD = 1.1,           // Digital supply voltage
    parameter real VCM = 1.4,            // Common mode voltage
    parameter real IBIAS = 30e-6,        // Bias current (30μA)
    parameter real PREAMP_GAIN = 60.0,   // Preamp gain (60dB)
    parameter real PREAMP_BW = 10e6,     // Preamp bandwidth (10MHz)
    parameter real LATCH_TIME = 8e-9,    // Latch regeneration time (8ns)
    parameter real HYSTERESIS_MAX = 10e-3 // Maximum hysteresis (10mV)
)(
    // Clock and control
    input  logic        clk_i,           // Clock input
    input  logic        reset_n_i,       // Active low reset
    input  logic        enable_i,        // Enable signal
    
    // Comparator control
    input  logic        latch_enable_i,  // Latch enable
    input  logic        reset_latch_i,   // Reset latch
    input  logic [3:0]  hysteresis_i,    // Hysteresis control (4-bit)
    
    // Calibration control
    input  logic        cal_enable_i,    // Calibration enable
    input  logic [7:0]  cal_offset_i,    // Offset calibration code
    input  logic        cal_valid_i,     // Calibration valid
    
    // Analog inputs
    input  real         vin_p_i,         // Positive input
    input  real         vin_n_i,         // Negative input
    input  real         vcm_i,           // Common mode input
    
    // Digital outputs
    output logic        comp_out_o,      // Comparator output
    output logic        comp_out_valid_o, // Output valid
    output logic        metastable_o,    // Metastability flag
    
    // Status and monitoring
    output logic        ready_o,         // Ready signal
    output real         offset_o,        // Offset voltage
    output real         hysteresis_o,    // Hysteresis voltage
    output real         noise_o,         // Input referred noise
    output real         delay_o          // Propagation delay
);

    //=============================================================================
    // Internal signals and parameters
    //=============================================================================
    
    // Preamp signals
    real vdiff_in, vdiff_preamp;
    real vcm_in, vcm_preamp;
    real preamp_out_p, preamp_out_n;
    real preamp_offset, preamp_noise;
    
    // Latch signals
    real latch_in_p, latch_in_n;
    real latch_out_p, latch_out_n;
    real latch_regeneration, latch_metastable;
    
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
    // Preamp implementation
    //=============================================================================
    
    // Input differential calculation
    always_comb begin
        vdiff_in = vin_p_i - vin_n_i;
        vcm_in = (vin_p_i + vin_n_i) / 2.0;
    end
    
    // Preamp transfer function
    always_comb begin
        // Preamp specifications
        real preamp_gm = 2.0e-3;      // 2mS transconductance
        real preamp_ro = 150e3;       // 150kΩ output resistance
        real preamp_cap = 1e-12;      // 1pF load capacitance
        
        // Preamp imperfections
        preamp_offset = 0.8e-3;       // 0.8mV offset
        real preamp_noise_density = 10e-9; // 10nV/√Hz
        
        // Preamp noise calculation
        real noise_bandwidth = PREAMP_BW / 1.57;  // Effective noise bandwidth
        preamp_noise = preamp_noise_density * $sqrt(noise_bandwidth) * $random();
        
        // Preamp gain calculation
        real dc_gain = preamp_gm * preamp_ro;
        real ac_gain = dc_gain / (1.0 + (2.0 * $pi * PREAMP_BW * preamp_cap * preamp_ro));
        
        // Preamp output calculation
        real preamp_input = vdiff_in + preamp_offset + preamp_noise;
        vdiff_preamp = preamp_input * ac_gain;
        
        // Common mode output
        vcm_preamp = vcm_in;
        
        // Differential outputs
        preamp_out_p = vcm_preamp + vdiff_preamp / 2.0;
        preamp_out_n = vcm_preamp - vdiff_preamp / 2.0;
        
        // Limit output swing
        if (preamp_out_p > VDDA - 0.2) preamp_out_p = VDDA - 0.2;
        if (preamp_out_p < 0.2) preamp_out_p = 0.2;
        if (preamp_out_n > VDDA - 0.2) preamp_out_n = VDDA - 0.2;
        if (preamp_out_n < 0.2) preamp_out_n = 0.2;
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
    // Latch implementation
    //=============================================================================
    
    // Latch input with calibration
    always_comb begin
        latch_in_p = preamp_out_p + cal_offset_voltage + cal_hysteresis_voltage;
        latch_in_n = preamp_out_n + cal_offset_voltage - cal_hysteresis_voltage;
    end
    
    // Latch transfer function
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            latch_out_p <= VCM;
            latch_out_n <= VCM;
            latch_regeneration <= 0.0;
            latch_metastable <= 0.0;
        end else begin
            if (reset_phase_d) begin
                // Reset phase - latch outputs at common mode
                latch_out_p <= VCM;
                latch_out_n <= VCM;
                latch_regeneration <= 0.0;
                latch_metastable <= 0.0;
            end else if (latch_phase_d) begin
                // Latch phase - regeneration
                real input_diff = latch_in_p - latch_in_n;
                real regeneration_gain = 10.0;  // Regeneration gain
                real time_step = 1.0 / 100e6;   // 10ns time step
                
                // Regeneration equation: dV/dt = gain * V
                latch_regeneration <= latch_regeneration + 
                                    regeneration_gain * input_diff * time_step;
                
                // Latch outputs
                if (latch_regeneration > 0.1) begin
                    latch_out_p <= VDDA - 0.1;
                    latch_out_n <= 0.1;
                end else if (latch_regeneration < -0.1) begin
                    latch_out_p <= 0.1;
                    latch_out_n <= VDDA - 0.1;
                end else begin
                    // Metastable region
                    latch_out_p <= VCM + latch_regeneration / 2.0;
                    latch_out_n <= VCM - latch_regeneration / 2.0;
                    latch_metastable <= 1.0;
                end
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
                if (latch_regeneration > 0.1) begin
                    comp_out_o <= 1'b1;
                    comp_out_valid_o <= 1'b1;
                    metastable_o <= 1'b0;
                end else if (latch_regeneration < -0.1) begin
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
    // Timing calculation
    //=============================================================================
    
    // Propagation delay calculation
    always_comb begin
        // Preamp delay
        real preamp_delay = 1.0 / (2.0 * $pi * PREAMP_BW);
        
        // Latch delay
        real latch_delay = LATCH_TIME;
        
        // Total propagation delay
        propagation_delay = preamp_delay + latch_delay;
        
        // Regeneration time
        regeneration_time = latch_regeneration;
    end
    
    // Latch completion detection
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            latch_done <= 1'b0;
            metastable_detected <= 1'b0;
        end else begin
            if (latch_phase_d) begin
                if (abs(latch_regeneration) > 0.1) begin
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
    // Performance monitoring
    //=============================================================================
    
    // Noise calculation
    always_comb begin
        // Input referred noise
        input_noise = preamp_noise;
        
        // Decision noise
        real decision_threshold = 0.1;  // 100mV decision threshold
        decision_noise = input_noise / PREAMP_GAIN;
    end
    
    // Offset and hysteresis monitoring
    always_comb begin
        offset_error = preamp_offset - cal_offset_voltage;
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
        real switching_freq = 5e6;    // 5MHz switching frequency
        real switching_cap = 0.1e-12; // 0.1pF switching capacitance
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
    else $error("Comparator input voltage out of range");
    
    // Output range assertion
    property output_range_check;
        @(posedge clk_i) disable iff (!reset_n_i)
        (latch_out_p >= 0) && (latch_out_p <= VDDA) &&
        (latch_out_n >= 0) && (latch_out_n <= VDDA);
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
    // Performance monitoring
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