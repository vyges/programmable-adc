//=============================================================================
// Programmable ADC - LVS Netlist
//=============================================================================
// Description: LVS-compatible netlist for layout verification
//              Simplified version for LVS comparison
// Author: Vyges IP Development Team
// Date: 2025
//=============================================================================

//=============================================================================
// Subcircuit: PGA Circuit
//=============================================================================
.subckt pga_circuit VIN_P VIN_N VOUT_P VOUT_N VDDA VSSA CLK CHOPPER_CLK
// Input chopper switches
SW_CHOP_IN1 VIN_P VIN_P_CHOP CLK chopper_switch
SW_CHOP_IN2 VIN_N VIN_N_CHOP CLK chopper_switch

// Input chopper capacitors
C_CHOP_P VIN_P_CHOP VIN_P_CHOP_D VSSA 1e-12
C_CHOP_N VIN_N_CHOP VIN_N_CHOP_D VSSA 1e-12

// Differential amplifier
M1 VOUT_P_AMP VIN_P_CHOP_D VBIAS_N VSSA nmos_40nm W=100e-6 L=0.4e-6
M2 VOUT_N_AMP VIN_N_CHOP_D VBIAS_N VSSA nmos_40nm W=100e-6 L=0.4e-6
M3 VOUT_P_AMP VOUT_P_AMP VDDA VDDA pmos_40nm W=50e-6 L=0.4e-6
M4 VOUT_N_AMP VOUT_N_AMP VDDA VDDA pmos_40nm W=50e-6 L=0.4e-6
M5 VBIAS_N VBIAS_N VSSA VSSA nmos_40nm W=20e-6 L=0.4e-6

// Bias voltage
VBIAS VBIAS_N VSSA 0.6

// Output chopper switches
SW_CHOP_OUT1 VOUT_P_AMP VOUT_P_CHOP CHOPPER_CLK chopper_switch
SW_CHOP_OUT2 VOUT_N_AMP VOUT_N_CHOP CHOPPER_CLK chopper_switch

// Output buffer
M6 VOUT_P VOUT_P_CHOP VBIAS_N VSSA nmos_40nm W=80e-6 L=0.4e-6
M7 VOUT_P VOUT_P VDDA VDDA pmos_40nm W=40e-6 L=0.4e-6
M8 VOUT_N VOUT_N_CHOP VBIAS_N VSSA nmos_40nm W=80e-6 L=0.4e-6
M9 VOUT_N VOUT_N VDDA VDDA pmos_40nm W=40e-6 L=0.4e-6
.ends

//=============================================================================
// Subcircuit: Sample & Hold Circuit
//=============================================================================
.subckt sample_hold_circuit VIN_P VIN_N VOUT_P VOUT_N VDDA VSSA CLK
// Sample switches
SW_SAMPLE_P VIN_P VIN_SH_P CLK sample_switch
SW_SAMPLE_N VIN_N VIN_SH_N CLK sample_switch

// Hold capacitors
C_HOLD_P VIN_SH_P VHOLD_P VSSA 10e-12
C_HOLD_N VIN_SH_N VHOLD_N VSSA 2e-12

// Hold switches
SW_HOLD_P VHOLD_P VHOLD_P_OUT CLK hold_switch
SW_HOLD_N VHOLD_N VHOLD_N_OUT CLK hold_switch

// Output buffer
M10 VOUT_P VHOLD_P_OUT VBIAS_SH VSSA nmos_40nm W=60e-6 L=0.4e-6
M11 VOUT_P VOUT_P VDDA VDDA pmos_40nm W=30e-6 L=0.4e-6
M12 VOUT_N VHOLD_N_OUT VBIAS_SH VSSA nmos_40nm W=60e-6 L=0.4e-6
M13 VOUT_N VOUT_N VDDA VDDA pmos_40nm W=30e-6 L=0.4e-6

// Bias voltage
VBIAS_SH VBIAS_SH VSSA 0.6
.ends

//=============================================================================
// Subcircuit: SAR DAC Circuit
//=============================================================================
.subckt sar_dac_circuit VREF VDAC_OUT VDDA VSSA DAC_CODE_15 DAC_CODE_14 DAC_CODE_13 DAC_CODE_12 DAC_CODE_11 DAC_CODE_10 DAC_CODE_9 DAC_CODE_8 DAC_CODE_7 DAC_CODE_6 DAC_CODE_5 DAC_CODE_4 DAC_CODE_3 DAC_CODE_2 DAC_CODE_1 DAC_CODE_0
// Capacitor array (16-bit)
C_DAC_15 VREF VDAC_OUT DAC_CODE_15 1e-15
C_DAC_14 VREF VDAC_OUT DAC_CODE_14 1e-15
C_DAC_13 VREF VDAC_OUT DAC_CODE_13 1e-15
C_DAC_12 VREF VDAC_OUT DAC_CODE_12 1e-15
C_DAC_11 VREF VDAC_OUT DAC_CODE_11 1e-15
C_DAC_10 VREF VDAC_OUT DAC_CODE_10 1e-15
C_DAC_9  VREF VDAC_OUT DAC_CODE_9  1e-15
C_DAC_8  VREF VDAC_OUT DAC_CODE_8  1e-15
C_DAC_7  VREF VDAC_OUT DAC_CODE_7  1e-15
C_DAC_6  VREF VDAC_OUT DAC_CODE_6  1e-15
C_DAC_5  VREF VDAC_OUT DAC_CODE_5  1e-15
C_DAC_4  VREF VDAC_OUT DAC_CODE_4  1e-15
C_DAC_3  VREF VDAC_OUT DAC_CODE_3  1e-15
C_DAC_2  VREF VDAC_OUT DAC_CODE_2  1e-15
C_DAC_1  VREF VDAC_OUT DAC_CODE_1  1e-15
C_DAC_0  VREF VDAC_OUT DAC_CODE_0  1e-15
.ends

//=============================================================================
// Subcircuit: Comparator Circuit
//=============================================================================
.subckt comparator_circuit VIN_P VIN_N COMP_OUT VDDA VSSA CLK
// Preamp stage
M14 VCOMP_PRE_P VIN_P VBIAS_COMP VSSA nmos_40nm W=80e-6 L=0.4e-6
M15 VCOMP_PRE_N VIN_N VBIAS_COMP VSSA nmos_40nm W=80e-6 L=0.4e-6
M16 VCOMP_PRE_P VCOMP_PRE_P VDDA VDDA pmos_40nm W=40e-6 L=0.4e-6
M17 VCOMP_PRE_N VCOMP_PRE_N VDDA VDDA pmos_40nm W=40e-6 L=0.4e-6

// Comparator bias
VBIAS_COMP VBIAS_COMP VSSA 0.6

// Latch stage
M18 VCOMP_LATCH_P VCOMP_PRE_P VBIAS_LATCH VSSA nmos_40nm W=30e-6 L=0.4e-6
M19 VCOMP_LATCH_N VCOMP_PRE_N VBIAS_LATCH VSSA nmos_40nm W=30e-6 L=0.4e-6
M20 VCOMP_LATCH_P VCOMP_LATCH_P VDDA VDDA pmos_40nm W=15e-6 L=0.4e-6
M21 VCOMP_LATCH_N VCOMP_LATCH_N VDDA VDDA pmos_40nm W=15e-6 L=0.4e-6

// Latch bias
VBIAS_LATCH VBIAS_LATCH VSSA 0.6

// Output buffer
M22 COMP_OUT VCOMP_LATCH_P VBIAS_OUT VSSA nmos_40nm W=20e-6 L=0.4e-6
M23 COMP_OUT COMP_OUT VDDA VDDA pmos_40nm W=10e-6 L=0.4e-6

// Output bias
VBIAS_OUT VBIAS_OUT VSSA 0.6
.ends

//=============================================================================
// Main Circuit
//=============================================================================
// Power supplies
VDD VDDA VSSA 2.8
VSS VSSA 0 0
VREF_SRC VREF_NET VSSA 2.8
VCM_SRC VCM_NET VSSA 1.4

// Clock generation
VCLK CLK VSSA PULSE(0 1.1 0 1e-9 1e-9 99e-9 200e-9)
VCHOPPER CHOPPER_CLK VSSA PULSE(0 1.1 0 1e-9 1e-9 499e-9 1000e-9)

// Test signals
VIN_P VIN_P_NET VSSA SIN(1.4 0.5 100e3 0 0 0)
VIN_N VIN_N_NET VSSA SIN(1.4 0.5 100e3 0 0 180)

// DAC control signals
VDAC_15 DAC_CODE_15 VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_14 DAC_CODE_14 VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_13 DAC_CODE_13 VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_12 DAC_CODE_12 VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_11 DAC_CODE_11 VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_10 DAC_CODE_10 VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_9  DAC_CODE_9  VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_8  DAC_CODE_8  VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_7  DAC_CODE_7  VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_6  DAC_CODE_6  VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_5  DAC_CODE_5  VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_4  DAC_CODE_4  VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_3  DAC_CODE_3  VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_2  DAC_CODE_2  VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_1  DAC_CODE_1  VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)
VDAC_0  DAC_CODE_0  VSSA PULSE(0 2.8 0 1e-9 1e-9 499e-9 1000e-9)

// Circuit instances
XPGA VIN_P_NET VIN_N_NET VOUT_P VOUT_N VDDA VSSA CLK CHOPPER_CLK pga_circuit
XSH VOUT_P VOUT_N VSH_P VSH_N VDDA VSSA CLK sample_hold_circuit
XDAC VREF_NET VDAC_OUT VDDA VSSA DAC_CODE_15 DAC_CODE_14 DAC_CODE_13 DAC_CODE_12 DAC_CODE_11 DAC_CODE_10 DAC_CODE_9 DAC_CODE_8 DAC_CODE_7 DAC_CODE_6 DAC_CODE_5 DAC_CODE_4 DAC_CODE_3 DAC_CODE_2 DAC_CODE_1 DAC_CODE_0 sar_dac_circuit
XCOMP VSH_P VSH_N COMP_OUT VDDA VSSA CLK comparator_circuit

//=============================================================================
// Analysis
//=============================================================================
.TRAN 1e-9 100e-6
.DC VDD 2.5 3.0 0.1
.AC DEC 10 1e3 10e6

//=============================================================================
// Output
//=============================================================================
.PROBE V(VIN_P_NET) V(VIN_N_NET)
.PROBE V(VOUT_P) V(VOUT_N)
.PROBE V(VSH_P) V(VSH_N)
.PROBE V(VDAC_OUT)
.PROBE V(COMP_OUT)
.PROBE V(CLK) V(CHOPPER_CLK)

.END 