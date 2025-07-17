//=============================================================================
// Programmable ADC - Sample & Hold Circuit Implementation (Cadence PDK)
//=============================================================================
// Description: Sample & Hold circuit optimized for Cadence PDK
//              Uses behavioral models and specifications from /docs
// Author: Vyges IP Development Team
// Date: 2025
//=============================================================================

`include "disciplines.vams"

module sample_hold_circuit_cadence #(
    parameter real VDDA = 2.8,
    parameter real VDDD = 1.1,
    parameter real VCM = 1.4,
    parameter real CHOLD = 10e-12,
    parameter real CSAMPLE = 2e-12,
    parameter real SWITCH_RON = 50.0,
    parameter real SWITCH_ROFF = 1e12,
    parameter real TEMP = 27.0
)(
    // Clock and control
    input  logic        clk_i,
    input  logic        reset_n_i,
    input  logic        enable_i,
    
    // Sample & Hold control
    input  logic        sample_enable_i,
    input  logic        hold_enable_i,
    input  logic        reset_hold_i,
    
    // Analog inputs (electrical discipline)
    input  electrical   vin_p_i,
    input  electrical   vin_n_i,
    input  electrical   vcm_i,
    
    // Analog outputs (electrical discipline)
    output electrical   vout_p_o,
    output electrical   vout_n_o,
    output electrical   vout_cm_o,
    
    // Status and monitoring
    output logic        ready_o,
    output logic        sample_done_o,
    output logic        hold_valid_o,
    output real         settling_time_o,
    output real         droop_rate_o,
    output real         charge_injection_o,
    output real         clock_feedthrough_o
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
    
    // Switch parameters from component specifications
    parameter real W_SWITCH = 20e-6;   // Switch width (20μm)
    parameter real L_SWITCH = 0.4e-6;  // Switch length (0.4μm)
    parameter real C_SWITCH = 0.1e-15; // Switch capacitance (0.1fF)
    
    //=============================================================================
    // Internal signals and parameters
    //=============================================================================
    
    // Sample & Hold signals (electrical discipline)
    electrical vin_p_sampled, vin_n_sampled;
    electrical vin_p_held, vin_n_held;
    electrical vdiff_in, vdiff_out;
    electrical vcm_in, vcm_out;
    
    // Switch control signals
    logic sample_switch_on, hold_switch_on;
    logic sample_switch_on_d, hold_switch_on_d;
    
    // Capacitor signals
    electrical hold_cap_p, hold_cap_n;
    electrical sample_cap_p, sample_cap_n;
    
    // Switch imperfections
    electrical charge_injection_p, charge_injection_n;
    electrical clock_feedthrough_p, clock_feedthrough_n;
    electrical switch_noise_p, switch_noise_n;
    
    // Timing signals
    real settling_time, droop_time;
    logic settling_done, droop_detected;
    
    // Performance monitoring
    real charge_injection_error, clock_feedthrough_error;
    real droop_rate, leakage_current;
    
    // Control signals
    logic sample_phase, hold_phase;
    logic sample_phase_d, hold_phase_d;
    
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
    
    // Sample & Hold control generation
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            sample_phase <= 1'b0;
            hold_phase <= 1'b1;
        end else begin
            sample_phase <= sample_enable_i && !reset_hold_i;
            hold_phase <= hold_enable_i && !reset_hold_i;
        end
    end
    
    // Synchronize control signals
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            sample_phase_d <= 1'b0;
            hold_phase_d <= 1'b1;
        end else begin
            sample_phase_d <= sample_phase;
            hold_phase_d <= hold_phase;
        end
    end
    
    // Switch control logic
    always_comb begin
        sample_switch_on = sample_phase_d && enable_i;
        hold_switch_on = hold_phase_d && enable_i;
    end
    
    // Synchronize switch signals
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            sample_switch_on_d <= 1'b0;
            hold_switch_on_d <= 1'b0;
        end else begin
            sample_switch_on_d <= sample_switch_on;
            hold_switch_on_d <= hold_switch_on;
        end
    end
    
    //=============================================================================
    // Input sampling implementation (Cadence behavioral)
    //=============================================================================
    
    // Input differential calculation
    analog begin
        V(vdiff_in) <+ V(vin_p_i) - V(vin_n_i);
        V(vcm_in) <+ (V(vin_p_i) + V(vin_n_i)) / 2.0;
    end
    
    // Sample switch implementation using Cadence behavioral models
    analog begin
        // Switch specifications from component specs
        real switch_charge_injection = 0.05e-12;  // 0.05pC charge injection
        real switch_clock_feedthrough = 0.5e-3;   // 0.5mV clock feedthrough
        real switch_noise_density = 2e-9;         // 2nV/√Hz switch noise
        
        // Switch noise calculation
        real noise_bandwidth = 1e6;  // 1MHz noise bandwidth
        real switch_noise_rms = switch_noise_density * $sqrt(noise_bandwidth);
        real switch_noise_value = switch_noise_rms * $random();
        
        if (sample_switch_on_d) begin
            // Sample switch ON - transmission gate behavior
            real switch_resistance = SWITCH_RON;
            
            // Charge injection modeling
            real charge_injection_value = switch_charge_injection * (sample_switch_on_d ? 1.0 : -1.0);
            V(charge_injection_p) <+ charge_injection_value / CSAMPLE;
            V(charge_injection_n) <+ -charge_injection_value / CSAMPLE;
            
            // Clock feedthrough modeling
            real clock_feedthrough_value = switch_clock_feedthrough * (sample_switch_on_d ? 1.0 : -1.0);
            V(clock_feedthrough_p) <+ clock_feedthrough_value;
            V(clock_feedthrough_n) <+ -clock_feedthrough_value;
            
            // Switch noise
            V(switch_noise_p) <+ switch_noise_value;
            V(switch_noise_n) <+ -switch_noise_value;
            
            // Sampled voltage with Cadence behavioral model
            V(vin_p_sampled) <+ V(vin_p_i) + V(charge_injection_p) + 
                              V(clock_feedthrough_p) + V(switch_noise_p);
            V(vin_n_sampled) <+ V(vin_n_i) + V(charge_injection_n) + 
                              V(clock_feedthrough_n) + V(switch_noise_n);
        end else begin
            // Sample switch OFF - high impedance
            V(vin_p_sampled) <+ V(vin_p_sampled);
            V(vin_n_sampled) <+ V(vin_n_sampled);
            
            // Reset imperfections
            V(charge_injection_p) <+ 0.0;
            V(charge_injection_n) <+ 0.0;
            V(clock_feedthrough_p) <+ 0.0;
            V(clock_feedthrough_n) <+ 0.0;
            V(switch_noise_p) <+ 0.0;
            V(switch_noise_n) <+ 0.0;
        end
    end
    
    //=============================================================================
    // Hold capacitor implementation (Cadence behavioral)
    //=============================================================================
    
    // Hold capacitor using Cadence behavioral models
    analog begin
        // Hold capacitor specifications from component specs
        real hold_cap_value = CHOLD;
        real sample_cap_value = CSAMPLE;
        real leakage_resistance = 1e12;  // 1TΩ leakage resistance
        real dielectric_absorption = 0.001;  // 0.1% dielectric absorption
        
        // Hold capacitor behavioral model
        I(hold_cap_p) <+ ddt(hold_cap_value * V(hold_cap_p));
        I(hold_cap_n) <+ ddt(hold_cap_value * V(hold_cap_n));
        
        // Sample capacitor behavioral model
        I(sample_cap_p) <+ ddt(sample_cap_value * V(sample_cap_p));
        I(sample_cap_n) <+ ddt(sample_cap_value * V(sample_cap_n));
        
        // Leakage current modeling
        real leakage_current_p = V(hold_cap_p) / leakage_resistance;
        real leakage_current_n = V(hold_cap_n) / leakage_resistance;
        
        I(hold_cap_p) <+ leakage_current_p;
        I(hold_cap_n) <+ leakage_current_n;
        
        // Dielectric absorption modeling
        real dielectric_current_p = dielectric_absorption * ddt(V(hold_cap_p));
        real dielectric_current_n = dielectric_absorption * ddt(V(hold_cap_n));
        
        I(hold_cap_p) <+ dielectric_current_p;
        I(hold_cap_n) <+ dielectric_current_n;
    end
    
    //=============================================================================
    // Hold switch implementation (Cadence behavioral)
    //=============================================================================
    
    // Hold switch using Cadence behavioral models
    analog begin
        if (hold_switch_on_d) begin
            // Hold switch ON - connect capacitors
            V(hold_cap_p) <+ V(vin_p_sampled);
            V(hold_cap_n) <+ V(vin_n_sampled);
            
            // Sample capacitors track input
            V(sample_cap_p) <+ V(vin_p_sampled);
            V(sample_cap_n) <+ V(vin_n_sampled);
        end else begin
            // Hold switch OFF - capacitors hold voltage
            V(hold_cap_p) <+ V(hold_cap_p);
            V(hold_cap_n) <+ V(hold_cap_n);
            
            // Sample capacitors disconnected
            V(sample_cap_p) <+ V(sample_cap_p);
            V(sample_cap_n) <+ V(sample_cap_n);
        end
    end
    
    //=============================================================================
    // Output generation (Cadence behavioral)
    //=============================================================================
    
    // Output voltage calculation using Cadence behavioral models
    analog begin
        // Output buffer specifications from component specs
        real buffer_gain = 1.0;      // Unity gain buffer
        real buffer_bw = 50e6;       // 50MHz buffer bandwidth
        real buffer_offset = 0.1e-3; // 0.1mV buffer offset
        real buffer_noise_density = 3e-9; // 3nV/√Hz buffer noise
        
        // Buffer noise calculation
        real buffer_noise_bandwidth = buffer_bw / 1.57;
        real buffer_noise_rms = buffer_noise_density * $sqrt(buffer_noise_bandwidth);
        real buffer_noise_value = buffer_noise_rms * $random();
        
        // Held voltage calculation
        V(vin_p_held) <+ V(hold_cap_p);
        V(vin_n_held) <+ V(hold_cap_n);
        
        // Differential output calculation
        V(vdiff_out) <+ V(vin_p_held) - V(vin_n_held);
        V(vcm_out) <+ (V(vin_p_held) + V(vin_n_held)) / 2.0;
        
        // Buffer output with Cadence behavioral model
        V(vout_p_o) <+ V(vcm_out) + V(vdiff_out) / 2.0 + buffer_offset + buffer_noise_value;
        V(vout_n_o) <+ V(vcm_out) - V(vdiff_out) / 2.0 + buffer_offset - buffer_noise_value;
        V(vout_cm_o) <+ V(vcm_out) + buffer_offset;
        
        // Limit output swing
        if (V(vout_p_o) > VDDA - 0.2) V(vout_p_o) <+ VDDA - 0.2;
        if (V(vout_p_o) < 0.2) V(vout_p_o) <+ 0.2;
        if (V(vout_n_o) > VDDA - 0.2) V(vout_n_o) <+ VDDA - 0.2;
        if (V(vout_n_o) < 0.2) V(vout_n_o) <+ 0.2;
    end
    
    //=============================================================================
    // Timing calculation (Cadence behavioral)
    //=============================================================================
    
    // Settling time calculation
    analog begin
        // Settling time from component specs
        real switch_resistance = SWITCH_RON;
        real total_cap = CHOLD + CSAMPLE;
        real tau = switch_resistance * total_cap;
        settling_time = 5.0 * tau;  // 5 time constants for settling
    end
    
    // Droop rate calculation
    analog begin
        // Droop rate from component specs
        real leakage_resistance = 1e12;  // 1TΩ leakage resistance
        real total_cap = CHOLD + CSAMPLE;
        droop_rate = 1.0 / (leakage_resistance * total_cap);
    end
    
    //=============================================================================
    // Performance monitoring (Cadence behavioral)
    //=============================================================================
    
    // Charge injection monitoring
    analog begin
        charge_injection_error = V(charge_injection_p) - V(charge_injection_n);
    end
    
    // Clock feedthrough monitoring
    analog begin
        clock_feedthrough_error = V(clock_feedthrough_p) - V(clock_feedthrough_n);
    end
    
    // Leakage current monitoring
    analog begin
        leakage_current = (V(hold_cap_p) + V(hold_cap_n)) / (2.0 * 1e12);
    end
    
    //=============================================================================
    // Timing and control logic
    //=============================================================================
    
    // Settling detection
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            settling_done <= 1'b0;
            droop_detected <= 1'b0;
            droop_time <= 0.0;
        end else begin
            if (sample_switch_on_d) begin
                settling_done <= 1'b0;
                droop_detected <= 1'b0;
                droop_time <= 0.0;
            end else begin
                droop_time <= droop_time + 10e-9;  // 10ns increment
                
                if (droop_time >= settling_time) begin
                    settling_done <= 1'b1;
                end
                
                if (droop_time >= 1e-3) begin  // 1ms droop detection
                    droop_detected <= 1'b1;
                end
            end
        end
    end
    
    // Status signal generation
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            ready_o <= 1'b0;
            sample_done_o <= 1'b0;
            hold_valid_o <= 1'b0;
        end else begin
            ready_o <= enable_i && !sample_switch_on_d;
            sample_done_o <= settling_done;
            hold_valid_o <= hold_phase_d && settling_done;
        end
    end
    
    //=============================================================================
    // Output assignment
    //=============================================================================
    
    // Performance output assignment
    always_comb begin
        settling_time_o = settling_time;
        droop_rate_o = droop_rate;
        charge_injection_o = charge_injection_error;
        clock_feedthrough_o = clock_feedthrough_error;
    end
    
    //=============================================================================
    // Power consumption calculation (Cadence behavioral)
    //=============================================================================
    
    // Static power calculation
    analog begin
        real leakage_power = leakage_current * V(vdda);
        
        // Dynamic power calculation
        real switching_freq = 5e6;    // 5MHz switching frequency
        real switching_cap = C_SWITCH; // Switch capacitance
        real dynamic_power = 0.5 * switching_cap * V(vdda) * V(vdda) * switching_freq;
        
        // Total power monitoring
        real total_power = leakage_power + dynamic_power;
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
    else $error("Sample & Hold input voltage out of range");
    
    // Output range assertion
    property output_range_check;
        @(posedge clk_i) disable iff (!reset_n_i)
        (V(vout_p_o) >= 0) && (V(vout_p_o) <= VDDA) &&
        (V(vout_n_o) >= 0) && (V(vout_n_o) <= VDDA);
    endproperty
    
    assert property (output_range_check)
    else $error("Sample & Hold output voltage out of range");
    
    // Sample & Hold coverage
    covergroup sample_hold_coverage @(posedge clk_i);
        sample_cp: coverpoint sample_enable_i {
            bins sample_on = {1'b1};
            bins sample_off = {1'b0};
        }
        hold_cp: coverpoint hold_enable_i {
            bins hold_on = {1'b1};
            bins hold_off = {1'b0};
        }
    endgroup
    
    sample_hold_coverage sh_cov = new();
    
    //=============================================================================
    // Cadence-specific performance monitoring
    //=============================================================================
    
    // Charge injection monitoring
    always @(posedge clk_i) begin
        if (settling_done) begin
            if (abs(charge_injection_error) > 1e-3) begin
                $warning("Sample & Hold charge injection: %f V", charge_injection_error);
            end
        end
    end
    
    // Clock feedthrough monitoring
    always @(posedge clk_i) begin
        if (settling_done) begin
            if (abs(clock_feedthrough_error) > 1e-3) begin
                $warning("Sample & Hold clock feedthrough: %f V", clock_feedthrough_error);
            end
        end
    end
    
    // Droop monitoring
    always @(posedge clk_i) begin
        if (droop_detected) begin
            $warning("Sample & Hold droop detected: %f V/s", droop_rate);
        end
    end
    
endmodule 