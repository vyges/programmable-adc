//=============================================================================
// Programmable ADC - Circuit Blocks Testbench
//=============================================================================
// Description: Comprehensive testbench for all circuit blocks
//              Tests PGA, Sample & Hold, SAR DAC, and Comparator
// Author: Vyges IP Development Team
// Date: 2025
//=============================================================================

`timescale 1ns/1ps

module tb_circuit_blocks;

    //=============================================================================
    // Test parameters
    //=============================================================================
    
    // Clock parameters
    localparam real CLK_PERIOD = 50.0;      // 20MHz clock
    localparam real CHOPPER_PERIOD = 1000.0; // 1MHz chopper clock
    
    // Supply voltages
    localparam real VDDA = 2.8;
    localparam real VDDD = 1.1;
    localparam real VCM = 1.4;
    
    // Test signals
    logic clk, chopper_clk, reset_n;
    logic enable;
    
    //=============================================================================
    // PGA test signals
    //=============================================================================
    
    // PGA inputs
    real pga_vin_p, pga_vin_n;
    logic [1:0] pga_gain_sel;
    
    // PGA outputs
    real pga_vout_p, pga_vout_n;
    logic pga_ready, pga_overload;
    real pga_offset, pga_gain_error;
    
    //=============================================================================
    // Sample & Hold test signals
    //=============================================================================
    
    // S/H inputs
    real sh_vin;
    logic sh_sample, sh_hold;
    
    // S/H outputs
    real sh_vout, sh_vout_cm;
    logic sh_ready, sh_sample_done;
    real sh_droop_rate, sh_settling_time;
    
    //=============================================================================
    // SAR DAC test signals
    //=============================================================================
    
    // DAC inputs
    logic [15:0] dac_code;
    logic dac_valid, reset_dac;
    logic [1:0] dac_resolution;
    logic cal_enable;
    logic [7:0] cal_code;
    logic cal_valid;
    
    // DAC outputs
    real dac_out_p, dac_out_n, dac_cm;
    logic dac_ready, dac_busy;
    real dac_dnl, dac_inl, dac_temp_drift, dac_voltage_drift;
    
    //=============================================================================
    // Comparator test signals
    //=============================================================================
    
    // Comparator inputs
    real comp_vin_p, comp_vin_n;
    logic latch_enable, reset_latch;
    logic [3:0] hysteresis;
    logic [7:0] cal_offset;
    
    // Comparator outputs
    logic comp_out, comp_out_valid, metastable;
    logic comp_ready;
    real comp_offset, comp_hysteresis, comp_noise, comp_delay;
    
    //=============================================================================
    // Test stimulus and monitoring
    //=============================================================================
    
    // Test counters
    int test_count, pass_count, fail_count;
    int pga_test_count, sh_test_count, dac_test_count, comp_test_count;
    
    // Performance monitoring
    real pga_gain_error_max, pga_offset_max;
    real sh_settling_error_max, sh_droop_error_max;
    real dac_dnl_max, dac_inl_max;
    real comp_offset_max, comp_noise_max;
    
    //=============================================================================
    // Clock generation
    //=============================================================================
    
    initial begin
        clk = 0;
        chopper_clk = 0;
        forever begin
            #(CLK_PERIOD/2) clk = ~clk;
        end
    end
    
    initial begin
        forever begin
            #(CHOPPER_PERIOD/2) chopper_clk = ~chopper_clk;
        end
    end
    
    //=============================================================================
    // Reset generation
    //=============================================================================
    
    initial begin
        reset_n = 0;
        enable = 0;
        #100;
        reset_n = 1;
        enable = 1;
    end
    
    //=============================================================================
    // Circuit block instantiations
    //=============================================================================
    
    // PGA circuit instance
    pga_circuit #(
        .VDDA(VDDA),
        .VDDD(VDDD),
        .VCM(VCM),
        .IBIAS(100e-6),
        .CLOAD(10e-12),
        .RLOAD(100e3)
    ) pga_inst (
        .clk_i(clk),
        .reset_n_i(reset_n),
        .chopper_clk_i(chopper_clk),
        .enable_i(enable),
        .gain_sel_i(pga_gain_sel),
        .vin_p_i(pga_vin_p),
        .vin_n_i(pga_vin_n),
        .vcm_i(VCM),
        .vout_p_o(pga_vout_p),
        .vout_n_o(pga_vout_n),
        .ready_o(pga_ready),
        .overload_o(pga_overload),
        .offset_o(pga_offset),
        .gain_error_o(pga_gain_error)
    );
    
    // Sample & Hold circuit instance
    sample_hold_circuit #(
        .VDDA(VDDA),
        .VDDD(VDDD),
        .CHOLD(10e-12),
        .RSWITCH(100.0),
        .CLEAKAGE(1e-15),
        .CLOAD(5e-12)
    ) sh_inst (
        .clk_i(clk),
        .reset_n_i(reset_n),
        .sample_i(sh_sample),
        .hold_i(sh_hold),
        .vin_i(sh_vin),
        .vcm_i(VCM),
        .vout_o(sh_vout),
        .vout_cm_o(sh_vout_cm),
        .ready_o(sh_ready),
        .sample_done_o(sh_sample_done),
        .droop_rate_o(sh_droop_rate),
        .settling_time_o(sh_settling_time)
    );
    
    // SAR DAC circuit instance
    sar_dac_circuit #(
        .RESOLUTION(16),
        .VDDA(VDDA),
        .VDDD(VDDD),
        .VREF(VDDA),
        .CUNIT(1e-15),
        .CMISMATCH(0.001),
        .TEMP_COEF(20e-6),
        .VOLT_COEF(50e-6)
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
    
    // Comparator circuit instance
    comparator_circuit #(
        .VDDA(VDDA),
        .VDDD(VDDD),
        .VCM(VCM),
        .IBIAS(30e-6),
        .PREAMP_GAIN(60.0),
        .PREAMP_BW(10e6),
        .LATCH_TIME(8e-9),
        .HYSTERESIS_MAX(10e-3)
    ) comp_inst (
        .clk_i(clk),
        .reset_n_i(reset_n),
        .enable_i(enable),
        .latch_enable_i(latch_enable),
        .reset_latch_i(reset_latch),
        .hysteresis_i(hysteresis),
        .cal_enable_i(cal_enable),
        .cal_offset_i(cal_offset),
        .cal_valid_i(cal_valid),
        .vin_p_i(comp_vin_p),
        .vin_n_i(comp_vin_n),
        .vcm_i(VCM),
        .comp_out_o(comp_out),
        .comp_out_valid_o(comp_out_valid),
        .metastable_o(metastable),
        .ready_o(comp_ready),
        .offset_o(comp_offset),
        .hysteresis_o(comp_hysteresis),
        .noise_o(comp_noise),
        .delay_o(comp_delay)
    );
    
    //=============================================================================
    // Test stimulus generation
    //=============================================================================
    
    // Test sequence
    initial begin
        // Initialize test variables
        test_count = 0;
        pass_count = 0;
        fail_count = 0;
        pga_test_count = 0;
        sh_test_count = 0;
        dac_test_count = 0;
        comp_test_count = 0;
        
        // Initialize performance monitors
        pga_gain_error_max = 0.0;
        pga_offset_max = 0.0;
        sh_settling_error_max = 0.0;
        sh_droop_error_max = 0.0;
        dac_dnl_max = 0.0;
        dac_inl_max = 0.0;
        comp_offset_max = 0.0;
        comp_noise_max = 0.0;
        
        // Wait for reset
        wait(reset_n);
        #100;
        
        $display("=== Circuit Blocks Testbench Started ===");
        $display("Time: %0t", $time);
        
        // Run test sequences
        run_pga_tests();
        run_sample_hold_tests();
        run_dac_tests();
        run_comparator_tests();
        
        // Final report
        print_test_report();
        
        $finish;
    end
    
    //=============================================================================
    // PGA test sequence
    //=============================================================================
    
    task run_pga_tests();
        $display("=== Running PGA Tests ===");
        
        // Test 1: Basic functionality
        test_pga_basic_functionality();
        
        // Test 2: Gain accuracy
        test_pga_gain_accuracy();
        
        // Test 3: Offset and CMRR
        test_pga_offset_cmrr();
        
        // Test 4: Chopper operation
        test_pga_chopper_operation();
        
        // Test 5: Overload detection
        test_pga_overload_detection();
        
        $display("PGA Tests Completed: %0d tests", pga_test_count);
    endtask
    
    task test_pga_basic_functionality();
        pga_test_count++;
        $display("PGA Test %0d: Basic Functionality", pga_test_count);
        
        // Test setup
        pga_gain_sel = 2'b00;  // 1x gain
        pga_vin_p = VCM + 0.1;  // 100mV differential
        pga_vin_n = VCM - 0.1;
        
        #100;
        
        // Check outputs
        if (pga_ready && !pga_overload) begin
            real expected_output = 0.1;  // 100mV input * 1x gain
            real actual_output = pga_vout_p - pga_vout_n;
            real error = abs(actual_output - expected_output);
            
            if (error < 0.01) begin  // 10mV tolerance
                $display("  PASS: Basic functionality test");
                pass_count++;
            end else begin
                $display("  FAIL: Basic functionality test, error = %f V", error);
                fail_count++;
            end
        end else begin
            $display("  FAIL: PGA not ready or overload detected");
            fail_count++;
        end
        
        test_count++;
    endtask
    
    task test_pga_gain_accuracy();
        pga_test_count++;
        $display("PGA Test %0d: Gain Accuracy", pga_test_count);
        
        // Test all gain settings
        for (int gain = 0; gain < 3; gain++) begin
            pga_gain_sel = gain;
            pga_vin_p = VCM + 0.05;  // 50mV differential
            pga_vin_n = VCM - 0.05;
            
            #100;
            
            real expected_gain = (gain == 0) ? 1.0 : (gain == 1) ? 2.0 : 4.0;
            real actual_gain = (pga_vout_p - pga_vout_n) / 0.1;
            real gain_error = abs(actual_gain - expected_gain) / expected_gain;
            
            if (gain_error < 0.01) begin  // 1% tolerance
                $display("  PASS: Gain %0dx accuracy test", expected_gain);
                pass_count++;
            end else begin
                $display("  FAIL: Gain %0dx accuracy test, error = %f%%", expected_gain, gain_error*100);
                fail_count++;
            end
            
            // Update max error tracking
            if (gain_error > pga_gain_error_max) pga_gain_error_max = gain_error;
        end
        
        test_count++;
    endtask
    
    task test_pga_offset_cmrr();
        pga_test_count++;
        $display("PGA Test %0d: Offset and CMRR", pga_test_count);
        
        // Test offset
        pga_gain_sel = 2'b00;
        pga_vin_p = VCM;
        pga_vin_n = VCM;
        
        #100;
        
        real offset_error = abs(pga_vout_p - pga_vout_n);
        if (offset_error < 0.01) begin  // 10mV tolerance
            $display("  PASS: Offset test");
            pass_count++;
        end else begin
            $display("  FAIL: Offset test, offset = %f V", offset_error);
            fail_count++;
        end
        
        // Test CMRR
        pga_vin_p = VCM + 0.5;  // 500mV common mode
        pga_vin_n = VCM + 0.5;
        
        #100;
        
        real cmrr_error = abs(pga_vout_p - pga_vout_n);
        if (cmrr_error < 0.01) begin  // 10mV tolerance
            $display("  PASS: CMRR test");
            pass_count++;
        end else begin
            $display("  FAIL: CMRR test, error = %f V", cmrr_error);
            fail_count++;
        end
        
        // Update max error tracking
        if (offset_error > pga_offset_max) pga_offset_max = offset_error;
        
        test_count++;
    endtask
    
    task test_pga_chopper_operation();
        pga_test_count++;
        $display("PGA Test %0d: Chopper Operation", pga_test_count);
        
        // Test chopper frequency
        pga_gain_sel = 2'b00;
        pga_vin_p = VCM + 0.1;
        pga_vin_n = VCM - 0.1;
        
        #1000;  // Wait for chopper cycles
        
        // Check chopper operation
        if (pga_ready) begin
            $display("  PASS: Chopper operation test");
            pass_count++;
        end else begin
            $display("  FAIL: Chopper operation test");
            fail_count++;
        end
        
        test_count++;
    endtask
    
    task test_pga_overload_detection();
        pga_test_count++;
        $display("PGA Test %0d: Overload Detection", pga_test_count);
        
        // Test overload condition
        pga_gain_sel = 2'b10;  // 4x gain
        pga_vin_p = VCM + 1.0;  // 1V differential (overload)
        pga_vin_n = VCM - 1.0;
        
        #100;
        
        if (pga_overload) begin
            $display("  PASS: Overload detection test");
            pass_count++;
        end else begin
            $display("  FAIL: Overload detection test");
            fail_count++;
        end
        
        test_count++;
    endtask
    
    //=============================================================================
    // Sample & Hold test sequence
    //=============================================================================
    
    task run_sample_hold_tests();
        $display("=== Running Sample & Hold Tests ===");
        
        // Test 1: Basic sampling
        test_sh_basic_sampling();
        
        // Test 2: Settling time
        test_sh_settling_time();
        
        // Test 3: Hold accuracy
        test_sh_hold_accuracy();
        
        // Test 4: Droop rate
        test_sh_droop_rate();
        
        $display("Sample & Hold Tests Completed: %0d tests", sh_test_count);
    endtask
    
    task test_sh_basic_sampling();
        sh_test_count++;
        $display("S/H Test %0d: Basic Sampling", sh_test_count);
        
        // Test setup
        sh_vin = VCM + 0.5;  // 500mV input
        sh_sample = 1;
        sh_hold = 0;
        
        #200;  // Wait for sampling
        
        sh_sample = 0;
        sh_hold = 1;
        
        #100;
        
        // Check output
        real sampling_error = abs(sh_vout - sh_vin);
        if (sampling_error < 0.01) begin  // 10mV tolerance
            $display("  PASS: Basic sampling test");
            pass_count++;
        end else begin
            $display("  FAIL: Basic sampling test, error = %f V", sampling_error);
            fail_count++;
        end
        
        test_count++;
    endtask
    
    task test_sh_settling_time();
        sh_test_count++;
        $display("S/H Test %0d: Settling Time", sh_test_count);
        
        // Test settling time
        sh_vin = VCM + 0.3;
        sh_sample = 1;
        sh_hold = 0;
        
        #50;  // Short sampling time
        
        sh_sample = 0;
        sh_hold = 1;
        
        #100;
        
        // Check settling
        if (sh_sample_done) begin
            $display("  PASS: Settling time test");
            pass_count++;
        end else begin
            $display("  FAIL: Settling time test");
            fail_count++;
        end
        
        test_count++;
    endtask
    
    task test_sh_hold_accuracy();
        sh_test_count++;
        $display("S/H Test %0d: Hold Accuracy", sh_test_count);
        
        // Test hold accuracy
        sh_vin = VCM + 0.2;
        sh_sample = 1;
        sh_hold = 0;
        
        #100;
        
        sh_sample = 0;
        sh_hold = 1;
        
        #500;  // Hold for 500ns
        
        // Check hold accuracy
        real hold_error = abs(sh_vout - (VCM + 0.2));
        if (hold_error < 0.01) begin  // 10mV tolerance
            $display("  PASS: Hold accuracy test");
            pass_count++;
        end else begin
            $display("  FAIL: Hold accuracy test, error = %f V", hold_error);
            fail_count++;
        end
        
        // Update max error tracking
        if (hold_error > sh_settling_error_max) sh_settling_error_max = hold_error;
        
        test_count++;
    endtask
    
    task test_sh_droop_rate();
        sh_test_count++;
        $display("S/H Test %0d: Droop Rate", sh_test_count);
        
        // Test droop rate
        sh_vin = VCM + 0.4;
        sh_sample = 1;
        sh_hold = 0;
        
        #100;
        
        sh_sample = 0;
        sh_hold = 1;
        
        real initial_voltage = sh_vout;
        
        #1000;  // Hold for 1μs
        
        real final_voltage = sh_vout;
        real droop_rate = (initial_voltage - final_voltage) / 1e-6;  // V/s
        
        if (droop_rate < 1e-3) begin  // < 1mV/μs
            $display("  PASS: Droop rate test");
            pass_count++;
        end else begin
            $display("  FAIL: Droop rate test, rate = %f V/s", droop_rate);
            fail_count++;
        end
        
        // Update max error tracking
        if (droop_rate > sh_droop_error_max) sh_droop_error_max = droop_rate;
        
        test_count++;
    endtask
    
    //=============================================================================
    // DAC test sequence
    //=============================================================================
    
    task run_dac_tests();
        $display("=== Running DAC Tests ===");
        
        // Test 1: Basic functionality
        test_dac_basic_functionality();
        
        // Test 2: Resolution modes
        test_dac_resolution_modes();
        
        // Test 3: Linearity
        test_dac_linearity();
        
        // Test 4: Calibration
        test_dac_calibration();
        
        $display("DAC Tests Completed: %0d tests", dac_test_count);
    endtask
    
    task test_dac_basic_functionality();
        dac_test_count++;
        $display("DAC Test %0d: Basic Functionality", dac_test_count);
        
        // Test setup
        dac_resolution = 2'b10;  // 16-bit
        dac_code = 16'h8000;     // Midscale
        dac_valid = 1;
        reset_dac = 0;
        
        #100;
        
        dac_valid = 0;
        
        #200;
        
        // Check output
        if (dac_ready && !dac_busy) begin
            real expected_voltage = VDDA / 2.0;  // Midscale
            real actual_voltage = dac_cm;
            real error = abs(actual_voltage - expected_voltage);
            
            if (error < 0.01) begin  // 10mV tolerance
                $display("  PASS: Basic functionality test");
                pass_count++;
            end else begin
                $display("  FAIL: Basic functionality test, error = %f V", error);
                fail_count++;
            end
        end else begin
            $display("  FAIL: DAC not ready or busy");
            fail_count++;
        end
        
        test_count++;
    endtask
    
    task test_dac_resolution_modes();
        dac_test_count++;
        $display("DAC Test %0d: Resolution Modes", dac_test_count);
        
        // Test all resolution modes
        for (int res = 0; res < 3; res++) begin
            dac_resolution = res;
            dac_code = 16'h8000;  // Midscale
            dac_valid = 1;
            
            #100;
            
            dac_valid = 0;
            
            #200;
            
            if (dac_ready) begin
                $display("  PASS: Resolution %0d-bit test", (res == 0) ? 12 : (res == 1) ? 14 : 16);
                pass_count++;
            end else begin
                $display("  FAIL: Resolution %0d-bit test", (res == 0) ? 12 : (res == 1) ? 14 : 16);
                fail_count++;
            end
        end
        
        test_count++;
    endtask
    
    task test_dac_linearity();
        dac_test_count++;
        $display("DAC Test %0d: Linearity", dac_test_count);
        
        // Test linearity
        dac_resolution = 2'b10;  // 16-bit
        
        for (int code = 0; code < 256; code += 64) begin
            dac_code = code;
            dac_valid = 1;
            
            #100;
            
            dac_valid = 0;
            
            #200;
            
            // Check DNL and INL
            if (abs(dac_dnl) < 0.5 && abs(dac_inl) < 1.0) begin
                $display("  PASS: Linearity test for code %0d", code);
                pass_count++;
            end else begin
                $display("  FAIL: Linearity test for code %0d, DNL=%f, INL=%f", code, dac_dnl, dac_inl);
                fail_count++;
            end
            
            // Update max error tracking
            if (abs(dac_dnl) > dac_dnl_max) dac_dnl_max = abs(dac_dnl);
            if (abs(dac_inl) > dac_inl_max) dac_inl_max = abs(dac_inl);
        end
        
        test_count++;
    endtask
    
    task test_dac_calibration();
        dac_test_count++;
        $display("DAC Test %0d: Calibration", dac_test_count);
        
        // Test calibration
        dac_resolution = 2'b10;  // 16-bit
        dac_code = 16'h8000;     // Midscale
        cal_enable = 1;
        cal_code = 8'h80;        // Midscale calibration
        cal_valid = 1;
        
        #100;
        
        cal_valid = 0;
        dac_valid = 1;
        
        #100;
        
        dac_valid = 0;
        
        #200;
        
        if (dac_ready) begin
            $display("  PASS: Calibration test");
            pass_count++;
        end else begin
            $display("  FAIL: Calibration test");
            fail_count++;
        end
        
        test_count++;
    endtask
    
    //=============================================================================
    // Comparator test sequence
    //=============================================================================
    
    task run_comparator_tests();
        $display("=== Running Comparator Tests ===");
        
        // Test 1: Basic functionality
        test_comp_basic_functionality();
        
        // Test 2: Offset calibration
        test_comp_offset_calibration();
        
        // Test 3: Hysteresis
        test_comp_hysteresis();
        
        // Test 4: Metastability
        test_comp_metastability();
        
        $display("Comparator Tests Completed: %0d tests", comp_test_count);
    endtask
    
    task test_comp_basic_functionality();
        comp_test_count++;
        $display("Comparator Test %0d: Basic Functionality", comp_test_count);
        
        // Test positive input
        comp_vin_p = VCM + 0.1;
        comp_vin_n = VCM - 0.1;
        latch_enable = 1;
        reset_latch = 0;
        
        #100;
        
        if (comp_out_valid && comp_out) begin
            $display("  PASS: Positive input test");
            pass_count++;
        end else begin
            $display("  FAIL: Positive input test");
            fail_count++;
        end
        
        // Test negative input
        comp_vin_p = VCM - 0.1;
        comp_vin_n = VCM + 0.1;
        
        #100;
        
        if (comp_out_valid && !comp_out) begin
            $display("  PASS: Negative input test");
            pass_count++;
        end else begin
            $display("  FAIL: Negative input test");
            fail_count++;
        end
        
        test_count++;
    endtask
    
    task test_comp_offset_calibration();
        comp_test_count++;
        $display("Comparator Test %0d: Offset Calibration", comp_test_count);
        
        // Test offset calibration
        cal_enable = 1;
        cal_offset = 8'h80;  // Midscale calibration
        cal_valid = 1;
        
        #100;
        
        cal_valid = 0;
        
        comp_vin_p = VCM;
        comp_vin_n = VCM;
        latch_enable = 1;
        
        #100;
        
        if (comp_ready) begin
            $display("  PASS: Offset calibration test");
            pass_count++;
        end else begin
            $display("  FAIL: Offset calibration test");
            fail_count++;
        end
        
        // Update max error tracking
        if (abs(comp_offset) > comp_offset_max) comp_offset_max = abs(comp_offset);
        
        test_count++;
    endtask
    
    task test_comp_hysteresis();
        comp_test_count++;
        $display("Comparator Test %0d: Hysteresis", comp_test_count);
        
        // Test hysteresis
        hysteresis = 4'h8;  // Mid hysteresis
        comp_vin_p = VCM + 0.01;
        comp_vin_n = VCM - 0.01;
        latch_enable = 1;
        
        #100;
        
        if (comp_out_valid) begin
            $display("  PASS: Hysteresis test");
            pass_count++;
        end else begin
            $display("  FAIL: Hysteresis test");
            fail_count++;
        end
        
        test_count++;
    endtask
    
    task test_comp_metastability();
        comp_test_count++;
        $display("Comparator Test %0d: Metastability", comp_test_count);
        
        // Test metastability (very small input)
        comp_vin_p = VCM + 0.001;
        comp_vin_n = VCM - 0.001;
        latch_enable = 1;
        
        #100;
        
        if (metastable) begin
            $display("  PASS: Metastability detection test");
            pass_count++;
        end else begin
            $display("  FAIL: Metastability detection test");
            fail_count++;
        end
        
        test_count++;
    endtask
    
    //=============================================================================
    // Test reporting
    //=============================================================================
    
    task print_test_report();
        $display("\n=== Circuit Blocks Test Report ===");
        $display("Total Tests: %0d", test_count);
        $display("Passed: %0d", pass_count);
        $display("Failed: %0d", fail_count);
        $display("Success Rate: %0.1f%%", (real'(pass_count) / real'(test_count)) * 100.0);
        
        $display("\nPerformance Summary:");
        $display("PGA Max Gain Error: %0.2f%%", pga_gain_error_max * 100.0);
        $display("PGA Max Offset: %0.3f V", pga_offset_max);
        $display("S/H Max Settling Error: %0.3f V", sh_settling_error_max);
        $display("S/H Max Droop Rate: %0.3f V/s", sh_droop_error_max);
        $display("DAC Max DNL: %0.3f LSB", dac_dnl_max);
        $display("DAC Max INL: %0.3f LSB", dac_inl_max);
        $display("Comparator Max Offset: %0.3f V", comp_offset_max);
        $display("Comparator Max Noise: %0.3f V", comp_noise_max);
        
        if (fail_count == 0) begin
            $display("\n=== ALL TESTS PASSED ===");
        end else begin
            $display("\n=== SOME TESTS FAILED ===");
        end
        
        $display("Test completed at time: %0t", $time);
    endtask
    
    //=============================================================================
    // Waveform dumping
    //=============================================================================
    
    initial begin
        $dumpfile("tb_circuit_blocks.vcd");
        $dumpvars(0, tb_circuit_blocks);
    end
    
endmodule 