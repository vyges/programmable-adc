//=============================================================================
// Programmable ADC - Sample & Hold Circuit Implementation
//=============================================================================
// Description: Sample & Hold circuit with transmission gate switches
//              High-speed sampling with low droop and high accuracy
// Author: Vyges IP Development Team
// Date: 2024
//=============================================================================

module sample_hold_circuit #(
    parameter real VDDA = 2.8,
    parameter real VDDD = 1.1,
    parameter real CHOLD = 10e-12,  // Hold capacitor (10pF)
    parameter real RSWITCH = 100.0,  // Switch on-resistance (100Ω)
    parameter real CLEAKAGE = 1e-15, // Leakage current (1fA)
    parameter real CLOAD = 5e-12     // Load capacitance (5pF)
)(
    // Clock and control
    input  logic        clk_i,           // Clock input
    input  logic        reset_n_i,       // Active low reset
    input  logic        sample_i,        // Sample enable
    input  logic        hold_i,          // Hold enable
    
    // Analog inputs
    input  real         vin_i,           // Input voltage
    input  real         vcm_i,           // Common mode voltage
    
    // Analog outputs
    output real         vout_o,          // Output voltage
    output real         vout_cm_o,       // Output common mode
    
    // Status and control
    output logic        ready_o,         // Ready signal
    output logic        sample_done_o,   // Sample complete
    output real         droop_rate_o,    // Voltage droop rate
    output real         settling_time_o  // Settling time
);

    //=============================================================================
    // Internal signals and parameters
    //=============================================================================
    
    // Control signals
    logic sample_phase, hold_phase;
    logic sample_phase_d, hold_phase_d;
    
    // Switch control signals
    logic switch_on, switch_off;
    logic switch_on_d, switch_off_d;
    
    // Capacitor voltage
    real vcap, vcap_prev;
    real vcap_droop, vcap_settling;
    
    // Switch signals
    real vswitch_in, vswitch_out;
    real vswitch_drop, vswitch_noise;
    
    // Buffer signals
    real vbuffer_in, vbuffer_out;
    real vbuffer_offset, vbuffer_noise;
    
    // Timing signals
    real sample_time, hold_time;
    real settling_time, droop_time;
    
    // Error signals
    real charge_injection, clock_feedthrough;
    real switch_offset, buffer_offset;
    
    //=============================================================================
    // Control logic implementation
    //=============================================================================
    
    // Sample and hold phase generation
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            sample_phase <= 1'b0;
            hold_phase <= 1'b1;
        end else begin
            sample_phase <= sample_i && !hold_i;
            hold_phase <= hold_i && !sample_i;
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
        switch_on = sample_phase_d;
        switch_off = hold_phase_d;
    end
    
    // Synchronize switch signals
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            switch_on_d <= 1'b0;
            switch_off_d <= 1'b1;
        end else begin
            switch_on_d <= switch_on;
            switch_off_d <= switch_off;
        end
    end
    
    //=============================================================================
    // Transmission gate switch implementation
    //=============================================================================
    
    // Switch transfer function
    always_comb begin
        if (switch_on_d) begin
            // Switch is ON - transmission gate behavior
            real switch_conductance = 1.0 / RSWITCH;
            real switch_cap = 0.1e-12;  // 0.1pF switch capacitance
            
            // Switch voltage drop
            vswitch_drop = vin_i * (switch_conductance / (switch_conductance + 1.0/RSWITCH));
            
            // Switch noise (thermal noise)
            real kT = 4.0e-21;  // kT at room temperature
            real switch_noise_power = kT / (switch_cap * RSWITCH);
            vswitch_noise = $sqrt(switch_noise_power) * $random();
            
            // Charge injection and clock feedthrough
            charge_injection = 0.1e-12;  // 0.1pC charge injection
            clock_feedthrough = 1e-3;    // 1mV clock feedthrough
            
            vswitch_out = vswitch_drop + vswitch_noise + 
                         (switch_on_d ? charge_injection : -charge_injection) +
                         (switch_on_d ? clock_feedthrough : -clock_feedthrough);
        end else begin
            // Switch is OFF - high impedance
            vswitch_out = vcap;  // Hold previous value
            vswitch_drop = 0.0;
            vswitch_noise = 0.0;
            charge_injection = 0.0;
            clock_feedthrough = 0.0;
        end
    end
    
    //=============================================================================
    // Hold capacitor implementation
    //=============================================================================
    
    // Capacitor voltage update
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            vcap <= vcm_i;
            vcap_prev <= vcm_i;
        end else begin
            vcap_prev <= vcap;
            
            if (switch_on_d) begin
                // Sampling phase - charge capacitor
                real time_step = 1.0 / 100e6;  // 10ns time step
                real tau = RSWITCH * CHOLD;     // RC time constant
                real alpha = 1.0 - $exp(-time_step / tau);
                
                vcap <= vcap + alpha * (vswitch_out - vcap);
            end else begin
                // Hold phase - capacitor holds voltage with droop
                real droop_rate = CLEAKAGE / CHOLD;  // V/s droop rate
                real time_step = 1.0 / 100e6;        // 10ns time step
                
                vcap <= vcap - droop_rate * time_step;
            end
        end
    end
    
    // Capacitor settling and droop calculation
    always_comb begin
        // Settling time calculation (to 0.1%)
        real settling_threshold = 0.001;  // 0.1%
        real tau_settling = RSWITCH * CHOLD;
        settling_time = -tau_settling * $ln(settling_threshold);
        
        // Droop rate calculation
        real droop_rate = CLEAKAGE / CHOLD;
        droop_time = 1.0 / droop_rate;
        
        vcap_settling = vcap;
        vcap_droop = vcap_prev - vcap;
    end
    
    //=============================================================================
    // Output buffer implementation
    //=============================================================================
    
    // Buffer input
    always_comb begin
        vbuffer_in = vcap;
    end
    
    // Buffer transfer function
    always_comb begin
        // Buffer specifications
        real buffer_gain = 1.0;      // Unity gain buffer
        real buffer_bw = 50e6;       // 50MHz bandwidth
        real buffer_offset = 0.1e-3; // 0.1mV offset
        real buffer_noise_density = 5e-9; // 5nV/√Hz
        
        // Buffer noise calculation
        real noise_bandwidth = buffer_bw / 1.57;  // Effective noise bandwidth
        real buffer_noise_rms = buffer_noise_density * $sqrt(noise_bandwidth);
        vbuffer_noise = buffer_noise_rms * $random();
        
        // Buffer output calculation
        vbuffer_out = vbuffer_in * buffer_gain + buffer_offset + vbuffer_noise;
        
        // Load effects
        real output_resistance = 1.0;  // 1Ω output resistance
        vout_o = vbuffer_out * (1.0 - output_resistance / (output_resistance + 1e6));
        vout_cm_o = vcm_i;
    end
    
    //=============================================================================
    // Timing and status logic
    //=============================================================================
    
    // Sample timing
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            sample_time <= 0.0;
            hold_time <= 0.0;
        end else begin
            if (sample_phase_d) begin
                sample_time <= sample_time + 10e-9;  // 10ns increment
            end else begin
                sample_time <= 0.0;
            end
            
            if (hold_phase_d) begin
                hold_time <= hold_time + 10e-9;  // 10ns increment
            end else begin
                hold_time <= 0.0;
            end
        end
    end
    
    // Ready signal generation
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            ready_o <= 1'b0;
        end else begin
            ready_o <= 1'b1;  // Always ready after reset
        end
    end
    
    // Sample complete detection
    always_comb begin
        sample_done_o = (sample_time >= settling_time) && sample_phase_d;
    end
    
    // Status outputs
    always_comb begin
        droop_rate_o = CLEAKAGE / CHOLD;
        settling_time_o = settling_time;
    end
    
    //=============================================================================
    // Power consumption calculation
    //=============================================================================
    
    // Static power calculation
    real static_power;
    always_comb begin
        real buffer_current = 20e-6;  // 20μA buffer current
        static_power = buffer_current * VDDA;
    end
    
    // Dynamic power calculation
    real dynamic_power;
    always_comb begin
        real switching_freq = 5e6;    // 5MHz switching frequency
        real switching_cap = CHOLD + CLOAD;  // Total switching capacitance
        dynamic_power = 0.5 * switching_cap * VDDA * VDDA * switching_freq;
    end
    
    //=============================================================================
    // Assertions and coverage
    //=============================================================================
    
    // Input range assertion
    property input_range_check;
        @(posedge clk_i) disable iff (!reset_n_i)
        (vin_i >= 0) && (vin_i <= VDDA);
    endproperty
    
    assert property (input_range_check)
    else $error("S/H input voltage out of range");
    
    // Output range assertion
    property output_range_check;
        @(posedge clk_i) disable iff (!reset_n_i)
        (vout_o >= 0) && (vout_o <= VDDA);
    endproperty
    
    assert property (output_range_check)
    else $error("S/H output voltage out of range");
    
    // Sample/hold phase coverage
    covergroup sample_hold_coverage @(posedge clk_i);
        phase_cp: coverpoint {sample_phase_d, hold_phase_d} {
            bins sample = {2'b10};
            bins hold = {2'b01};
            bins idle = {2'b00};
            bins invalid = {2'b11};
        }
    endgroup
    
    sample_hold_coverage sh_cov = new();
    
    //=============================================================================
    // Performance monitoring
    //=============================================================================
    
    // Settling accuracy monitoring
    always @(posedge clk_i) begin
        if (sample_phase_d && sample_done_o) begin
            real settling_error = abs(vcap - vin_i);
            if (settling_error > 1e-3) begin
                $warning("S/H settling error: %f V", settling_error);
            end
        end
    end
    
    // Droop monitoring
    always @(posedge clk_i) begin
        if (hold_phase_d) begin
            real droop_error = abs(vcap_droop);
            if (droop_error > 1e-3) begin
                $warning("S/H droop error: %f V", droop_error);
            end
        end
    end
    
endmodule 