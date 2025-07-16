//=============================================================================
// Programmable ADC - Cadence PDK Circuit Blocks Testbench
//=============================================================================
// Description: Comprehensive testbench for Cadence PDK circuit blocks
//              Uses behavioral models and specifications from /docs
// Author: Vyges IP Development Team
// Date: 2024
//=============================================================================

`include "disciplines.vams"
`timescale 1ns/1ps

module tb_cadence_circuit_blocks;

    //=============================================================================
    // Test parameters
    //=============================================================================
    
    // Clock parameters
    parameter real CLK_PERIOD = 200.0;  // 5MHz clock
    parameter real CHOPPER_PERIOD = 1000.0;  // 1MHz chopper clock
    
    // Test duration
    parameter real SIM_TIME = 100e-6;  // 100μs simulation time
    
    //=============================================================================
    // Test signals
    //=============================================================================
    
    // Clock and control signals
    logic clk, chopper_clk;
    logic reset_n, enable;
    
    // Test control signals
    logic test_start, test_done;
    int test_count, error_count;
    
    //=============================================================================
    // PGA test signals
    //=============================================================================
    
    // PGA control
    logic [1:0] pga_gain_sel;
    logic pga_enable;
    
    // PGA analog signals (electrical discipline)
    electrical pga_vin_p, pga_vin_n, pga_vcm;
    electrical pga_vout_p, pga_vout_n;
    
    // PGA status
    logic pga_ready, pga_overload;
    real pga_offset, pga_gain_error;
    
    //=============================================================================
    // SAR DAC test signals
    //=============================================================================
    
    // DAC control
    logic [1:0] dac_resolution;
    logic [15:0] dac_code;
    logic dac_valid, reset_dac;
    logic cal_enable;
    logic [7:0] cal_code;
    logic cal_valid;
    
    // DAC analog signals (electrical discipline)
    electrical dac_out_p, dac_out_n, dac_cm;
    
    // DAC status
    logic dac_ready, dac_busy;
    real dac_dnl, dac_inl, dac_temp_drift, dac_voltage_drift;
    
    //=============================================================================
    // Comparator test signals
    //=============================================================================
    
    // Comparator control
    logic comp_latch_enable, comp_reset_latch;
    logic [3:0] comp_hysteresis;
    logic comp_cal_enable;
    logic [7:0] comp_cal_offset;
    logic comp_cal_valid;
    
    // Comparator analog signals (electrical discipline)
    electrical comp_vin_p, comp_vin_n, comp_vcm;
    
    // Comparator outputs
    logic comp_out, comp_out_valid, comp_metastable;
    
    // Comparator status
    logic comp_ready;
    real comp_offset, comp_hysteresis_val, comp_noise, comp_delay;
    
    //=============================================================================
    // Sample & Hold test signals
    //=============================================================================
    
    // S&H control
    logic sh_sample_enable, sh_hold_enable, sh_reset_hold;
    
    // S&H analog signals (electrical discipline)
    electrical sh_vin_p, sh_vin_n, sh_vcm;
    electrical sh_vout_p, sh_vout_n, sh_vout_cm;
    
    // S&H status
    logic sh_ready, sh_sample_done, sh_hold_valid;
    real sh_settling_time, sh_droop_rate, sh_charge_injection, sh_clock_feedthrough;
    
    //=============================================================================
    // Test stimulus signals
    //=============================================================================
    
    // Test input signals
    electrical test_signal_p, test_signal_n;
    electrical test_signal_cm;
    
    // Test reference signals
    electrical vref_p, vref_n, vref_cm;
    
    //=============================================================================
    // Module instantiations
    //=============================================================================
    
    // PGA circuit instantiation
    pga_circuit_cadence #(
        .VDDA(2.8),
        .VDDD(1.1),
        .VCM(1.4),
        .IBIAS(100e-6),
        .CLOAD(10e-12),
        .RLOAD(100e3),
        .TEMP(27.0)
    ) pga_inst (
        .clk_i(clk),
        .reset_n_i(reset_n),
        .chopper_clk_i(chopper_clk),
        .enable_i(pga_enable),
        .gain_sel_i(pga_gain_sel),
        .vin_p_i(pga_vin_p),
        .vin_n_i(pga_vin_n),
        .vcm_i(pga_vcm),
        .vout_p_o(pga_vout_p),
        .vout_n_o(pga_vout_n),
        .ready_o(pga_ready),
        .overload_o(pga_overload),
        .offset_o(pga_offset),
        .gain_error_o(pga_gain_error)
    );
    
    // SAR DAC circuit instantiation
    sar_dac_circuit_cadence #(
        .RESOLUTION(16),
        .VDDA(2.8),
        .VDDD(1.1),
        .VREF(2.8),
        .CUNIT(1e-15),
        .CMISMATCH(0.001),
        .TEMP_COEF(20e-6),
        .VOLT_COEF(50e-6),
        .TEMP(27.0)
    ) dac_inst (
        .clk_i(clk),
        .reset_n_i(reset_n),
        .enable_i(enable),
        .resolution_i(dac_resolution),
        .dac_code_i(dac_code),
        .dac_valid_i(dac_valid),
        .reset_dac_i(reset_dac),
        .cal_enable_i(cal_enable),
        .cal_code_i(cal_code),
        .cal_valid_i(cal_valid),
        .dac_out_p_o(dac_out_p),
        .dac_out_n_o(dac_out_n),
        .dac_cm_o(dac_cm),
        .ready_o(dac_ready),
        .busy_o(dac_busy),
        .dnl_o(dac_dnl),
        .inl_o(dac_inl),
        .temp_drift_o(dac_temp_drift),
        .voltage_drift_o(dac_voltage_drift)
    );
    
    // Comparator circuit instantiation
    comparator_circuit_cadence #(
        .VDDA(2.8),
        .VDDD(1.1),
        .VCM(1.4),
        .IBIAS(30e-6),
        .PREAMP_GAIN(60.0),
        .PREAMP_BW(10e6),
        .LATCH_TIME(8e-9),
        .HYSTERESIS_MAX(10e-3),
        .TEMP(27.0)
    ) comp_inst (
        .clk_i(clk),
        .reset_n_i(reset_n),
        .enable_i(enable),
        .latch_enable_i(comp_latch_enable),
        .reset_latch_i(comp_reset_latch),
        .hysteresis_i(comp_hysteresis),
        .cal_enable_i(comp_cal_enable),
        .cal_offset_i(comp_cal_offset),
        .cal_valid_i(comp_cal_valid),
        .vin_p_i(comp_vin_p),
        .vin_n_i(comp_vin_n),
        .vcm_i(comp_vcm),
        .comp_out_o(comp_out),
        .comp_out_valid_o(comp_out_valid),
        .metastable_o(comp_metastable),
        .ready_o(comp_ready),
        .offset_o(comp_offset),
        .hysteresis_o(comp_hysteresis_val),
        .noise_o(comp_noise),
        .delay_o(comp_delay)
    );
    
    // Sample & Hold circuit instantiation
    sample_hold_circuit_cadence #(
        .VDDA(2.8),
        .VDDD(1.1),
        .VCM(1.4),
        .CHOLD(10e-12),
        .CSAMPLE(2e-12),
        .SWITCH_RON(50.0),
        .SWITCH_ROFF(1e12),
        .TEMP(27.0)
    ) sh_inst (
        .clk_i(clk),
        .reset_n_i(reset_n),
        .enable_i(enable),
        .sample_enable_i(sh_sample_enable),
        .hold_enable_i(sh_hold_enable),
        .reset_hold_i(sh_reset_hold),
        .vin_p_i(sh_vin_p),
        .vin_n_i(sh_vin_n),
        .vcm_i(sh_vcm),
        .vout_p_o(sh_vout_p),
        .vout_n_o(sh_vout_n),
        .vout_cm_o(sh_vout_cm),
        .ready_o(sh_ready),
        .sample_done_o(sh_sample_done),
        .hold_valid_o(sh_hold_valid),
        .settling_time_o(sh_settling_time),
        .droop_rate_o(sh_droop_rate),
        .charge_injection_o(sh_charge_injection),
        .clock_feedthrough_o(sh_clock_feedthrough)
    );
    
    //=============================================================================
    // Clock generation
    //=============================================================================
    
    // Main clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // Chopper clock generation
    initial begin
        chopper_clk = 0;
        forever #(CHOPPER_PERIOD/2) chopper_clk = ~chopper_clk;
    end
    
    //=============================================================================
    // Test stimulus generation
    //=============================================================================
    
    // Test signal generation using Cadence behavioral models
    analog begin
        // Test signal specifications
        real signal_freq = 100e3;  // 100kHz test signal
        real signal_amplitude = 0.5;  // 0.5V amplitude
        real signal_offset = 1.4;  // 1.4V offset (VCM)
        
        // Generate sinusoidal test signal
        real signal_value = signal_amplitude * $sin(2.0 * $pi * signal_freq * $abstime) + signal_offset;
        
        // Differential test signal
        V(test_signal_p) <+ signal_value + 0.1;  // 100mV differential
        V(test_signal_n) <+ signal_value - 0.1;
        V(test_signal_cm) <+ signal_value;
        
        // Reference signals
        V(vref_p) <+ 2.8;  // VDDA
        V(vref_n) <+ 0.0;  // VSSA
        V(vref_cm) <+ 1.4; // VCM
    end
    
    //=============================================================================
    // Signal connections
    //=============================================================================
    
    // Connect test signals to circuit blocks
    assign pga_vin_p = test_signal_p;
    assign pga_vin_n = test_signal_n;
    assign pga_vcm = test_signal_cm;
    
    assign dac_out_p = dac_out_p;
    assign dac_out_n = dac_out_n;
    assign dac_cm = dac_cm;
    
    assign comp_vin_p = pga_vout_p;
    assign comp_vin_n = pga_vout_n;
    assign comp_vcm = pga_vcm;
    
    assign sh_vin_p = test_signal_p;
    assign sh_vin_n = test_signal_n;
    assign sh_vcm = test_signal_cm;
    
    //=============================================================================
    // Test sequence
    //=============================================================================
    
    // Main test sequence
    initial begin
        // Initialize test environment
        $display("=== Cadence PDK Circuit Blocks Testbench ===");
        $display("Simulation time: %0t", $time);
        
        // Initialize signals
        reset_n = 0;
        enable = 0;
        test_start = 0;
        test_count = 0;
        error_count = 0;
        
        // Initialize circuit control signals
        pga_enable = 0;
        pga_gain_sel = 2'b00;
        
        dac_resolution = 2'b10;  // 16-bit
        dac_code = 16'h0000;
        dac_valid = 0;
        reset_dac = 0;
        cal_enable = 0;
        cal_code = 8'h00;
        cal_valid = 0;
        
        comp_latch_enable = 0;
        comp_reset_latch = 1;
        comp_hysteresis = 4'h0;
        comp_cal_enable = 0;
        comp_cal_offset = 8'h80;
        comp_cal_valid = 0;
        
        sh_sample_enable = 0;
        sh_hold_enable = 1;
        sh_reset_hold = 0;
        
        // Wait for initial setup
        #(CLK_PERIOD * 10);
        
        // Release reset
        reset_n = 1;
        enable = 1;
        
        // Wait for circuits to stabilize
        #(CLK_PERIOD * 20);
        
        // Start test sequence
        test_start = 1;
        
        // Run test scenarios
        run_pga_tests();
        run_dac_tests();
        run_comparator_tests();
        run_sample_hold_tests();
        run_integration_tests();
        
        // Test completion
        test_done = 1;
        
        // Display test results
        display_test_results();
        
        // End simulation
        #(CLK_PERIOD * 10);
        $finish;
    end
    
    //=============================================================================
    // Test scenarios
    //=============================================================================
    
    // PGA test scenarios
    task run_pga_tests();
        $display("Running PGA tests...");
        
        // Test 1: Basic functionality
        test_count++;
        pga_enable = 1;
        pga_gain_sel = 2'b00;  // 1x gain
        #(CLK_PERIOD * 100);
        
        if (!pga_ready) begin
            $error("PGA not ready after enable");
            error_count++;
        end
        
        // Test 2: Gain settings
        pga_gain_sel = 2'b01;  // 2x gain
        #(CLK_PERIOD * 50);
        
        pga_gain_sel = 2'b10;  // 4x gain
        #(CLK_PERIOD * 50);
        
        // Test 3: Overload detection
        // This would require input signal modification
        #(CLK_PERIOD * 50);
        
        $display("PGA tests completed");
    endtask
    
    // DAC test scenarios
    task run_dac_tests();
        $display("Running DAC tests...");
        
        // Test 1: Basic DAC functionality
        test_count++;
        dac_valid = 1;
        dac_code = 16'h8000;  // Midscale
        #(CLK_PERIOD * 10);
        dac_valid = 0;
        
        #(CLK_PERIOD * 50);
        
        if (!dac_ready) begin
            $error("DAC not ready after conversion");
            error_count++;
        end
        
        // Test 2: Resolution settings
        dac_resolution = 2'b00;  // 12-bit
        dac_valid = 1;
        dac_code = 16'h0800;  // Midscale for 12-bit
        #(CLK_PERIOD * 10);
        dac_valid = 0;
        
        #(CLK_PERIOD * 50);
        
        dac_resolution = 2'b01;  // 14-bit
        dac_valid = 1;
        dac_code = 16'h2000;  // Midscale for 14-bit
        #(CLK_PERIOD * 10);
        dac_valid = 0;
        
        #(CLK_PERIOD * 50);
        
        // Test 3: Calibration
        cal_enable = 1;
        cal_code = 8'h80;  // Midscale calibration
        cal_valid = 1;
        #(CLK_PERIOD * 10);
        cal_valid = 0;
        
        #(CLK_PERIOD * 50);
        
        $display("DAC tests completed");
    endtask
    
    // Comparator test scenarios
    task run_comparator_tests();
        $display("Running Comparator tests...");
        
        // Test 1: Basic comparison
        test_count++;
        comp_reset_latch = 0;
        comp_latch_enable = 1;
        #(CLK_PERIOD * 10);
        
        if (!comp_ready) begin
            $error("Comparator not ready");
            error_count++;
        end
        
        // Test 2: Hysteresis settings
        comp_hysteresis = 4'h5;  // Medium hysteresis
        #(CLK_PERIOD * 20);
        
        comp_hysteresis = 4'hF;  // Maximum hysteresis
        #(CLK_PERIOD * 20);
        
        // Test 3: Calibration
        comp_cal_enable = 1;
        comp_cal_offset = 8'h90;  // Positive offset
        comp_cal_valid = 1;
        #(CLK_PERIOD * 10);
        comp_cal_valid = 0;
        
        #(CLK_PERIOD * 50);
        
        $display("Comparator tests completed");
    endtask
    
    // Sample & Hold test scenarios
    task run_sample_hold_tests();
        $display("Running Sample & Hold tests...");
        
        // Test 1: Sample mode
        test_count++;
        sh_sample_enable = 1;
        sh_hold_enable = 0;
        #(CLK_PERIOD * 50);
        
        if (!sh_ready) begin
            $error("Sample & Hold not ready");
            error_count++;
        end
        
        // Test 2: Hold mode
        sh_sample_enable = 0;
        sh_hold_enable = 1;
        #(CLK_PERIOD * 100);
        
        if (!sh_hold_valid) begin
            $error("Sample & Hold hold not valid");
            error_count++;
        end
        
        // Test 3: Reset
        sh_reset_hold = 1;
        #(CLK_PERIOD * 10);
        sh_reset_hold = 0;
        
        #(CLK_PERIOD * 50);
        
        $display("Sample & Hold tests completed");
    endtask
    
    // Integration test scenarios
    task run_integration_tests();
        $display("Running Integration tests...");
        
        // Test 1: Full signal chain
        test_count++;
        
        // Enable all circuits
        pga_enable = 1;
        pga_gain_sel = 2'b01;  // 2x gain
        
        dac_valid = 1;
        dac_code = 16'h4000;  // Quarter scale
        #(CLK_PERIOD * 10);
        dac_valid = 0;
        
        comp_latch_enable = 1;
        comp_reset_latch = 0;
        
        sh_sample_enable = 1;
        sh_hold_enable = 0;
        
        #(CLK_PERIOD * 200);
        
        // Check all circuits are ready
        if (!pga_ready || !dac_ready || !comp_ready || !sh_ready) begin
            $error("Integration test: circuits not ready");
            error_count++;
        end
        
        $display("Integration tests completed");
    endtask
    
    //=============================================================================
    // Performance monitoring
    //=============================================================================
    
    // Monitor circuit performance
    always @(posedge clk) begin
        if (test_start && !test_done) begin
            // Monitor PGA performance
            if (pga_ready && abs(pga_offset) > 1e-3) begin
                $warning("PGA offset: %f V", pga_offset);
            end
            
            if (pga_ready && abs(pga_gain_error) > 0.01) begin
                $warning("PGA gain error: %f%%", pga_gain_error * 100.0);
            end
            
            // Monitor DAC performance
            if (dac_ready && abs(dac_dnl) > 0.5) begin
                $warning("DAC DNL: %f LSB", dac_dnl);
            end
            
            if (dac_ready && abs(dac_inl) > 1.0) begin
                $warning("DAC INL: %f LSB", dac_inl);
            end
            
            // Monitor Comparator performance
            if (comp_ready && abs(comp_offset) > 1e-3) begin
                $warning("Comparator offset: %f V", comp_offset);
            end
            
            if (comp_metastable) begin
                $warning("Comparator metastability detected");
            end
            
            // Monitor Sample & Hold performance
            if (sh_ready && abs(sh_charge_injection) > 1e-3) begin
                $warning("S&H charge injection: %f V", sh_charge_injection);
            end
            
            if (sh_ready && abs(sh_clock_feedthrough) > 1e-3) begin
                $warning("S&H clock feedthrough: %f V", sh_clock_feedthrough);
            end
        end
    end
    
    //=============================================================================
    // Results display
    //=============================================================================
    
    task display_test_results();
        $display("=== Test Results ===");
        $display("Total tests: %0d", test_count);
        $display("Errors: %0d", error_count);
        $display("Success rate: %0.1f%%", (test_count - error_count) * 100.0 / test_count);
        
        if (error_count == 0) begin
            $display("All tests PASSED!");
        end else begin
            $display("Some tests FAILED!");
        end
        
        $display("=== Performance Summary ===");
        $display("PGA - Offset: %f V, Gain Error: %f%%", pga_offset, pga_gain_error * 100.0);
        $display("DAC - DNL: %f LSB, INL: %f LSB", dac_dnl, dac_inl);
        $display("Comparator - Offset: %f V, Noise: %f V", comp_offset, comp_noise);
        $display("S&H - Settling Time: %f s, Droop Rate: %f V/s", sh_settling_time, sh_droop_rate);
    endtask
    
    //=============================================================================
    // Waveform dumping
    //=============================================================================
    
    // Dump waveforms for analysis
    initial begin
        $dumpfile("tb_cadence_circuit_blocks.vcd");
        $dumpvars(0, tb_cadence_circuit_blocks);
    end
    
    //=============================================================================
    // Simulation timeout
    //=============================================================================
    
    // Simulation timeout
    initial begin
        #(SIM_TIME);
        $display("Simulation timeout reached");
        $finish;
    end
    
endmodule 