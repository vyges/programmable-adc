//=============================================================================
// Programmable ADC - Spectre Netlist
//=============================================================================
// Description: Spectre-compatible netlist for programmable ADC
//              Supports simulation and LVS verification
// Author: Vyges IP Development Team
// Date: 2025
//=============================================================================

//=============================================================================
// Simulation setup
//=============================================================================
simulator lang=spectre
global 0

//=============================================================================
// Include files
//=============================================================================
include "models.scs"
include "corners.scs"

//=============================================================================
// Parameters
//=============================================================================
parameters
    VDDA = 2.8
    VDDD = 1.1
    VCM = 1.4
    VREF = 2.8
    TEMP = 27
    CLK_FREQ = 5e6
    CHOPPER_FREQ = 1e6
    ADC_RESOLUTION = 16
    PGA_GAIN = 1
    CONVERSION_RATE = 5e6
    INPUT_BANDWIDTH = 1e6
    SUPPLY_VOLTAGE = 2.8
    VTN = 0.45
    VTP = -0.45
    KP_N = 200e-6
    KP_P = 80e-6
    LAMBDA_N = 0.1
    LAMBDA_P = 0.1
    CUNIT = 1e-15
    CMISMATCH = 0.001
    TEMP_COEF = 20e-6
    VOLT_COEF = 50e-6
    IBIAS = 100e-6
    PREAMP_GAIN = 60.0
    PREAMP_BW = 10e6
    LATCH_TIME = 8e-9
    HYSTERESIS_MAX = 10e-3
    CHOLD = 10e-12
    CSAMPLE = 2e-12
    SWITCH_RON = 50.0
    SWITCH_ROFF = 1e12
ends

//=============================================================================
// Power supplies
//=============================================================================
VDD (VDDA 0) vsource dc=VDDA
VSS (VSSA 0) vsource dc=0
VREF_SRC (VREF_NET 0) vsource dc=VREF
VCM_SRC (VCM_NET 0) vsource dc=VCM

//=============================================================================
// Clock generation
//=============================================================================
VCLK (CLK 0) vsource type=pulse val0=0 val1=VDDD period=1/CLK_FREQ rise=1e-9 fall=1e-9
VCHOPPER (CHOPPER_CLK 0) vsource type=pulse val0=0 val1=VDDD period=1/CHOPPER_FREQ rise=1e-9 fall=1e-9

//=============================================================================
// Test signals
//=============================================================================
// Differential input signal
VIN_P (VIN_P_NET 0) vsource type=sine freq=100e3 ampl=0.5 offset=VCM
VIN_N (VIN_N_NET 0) vsource type=sine freq=100e3 ampl=0.5 offset=VCM phase=180

//=============================================================================
// PGA Circuit Implementation
//=============================================================================

// Chopper switches
SW_CHOP_IN1 (VIN_P_NET VIN_P_CHOP CLK) switch model=chopper_switch
SW_CHOP_IN2 (VIN_N_NET VIN_N_CHOP CLK) switch model=chopper_switch

// Input chopper capacitors
C_CHOP_P (VIN_P_CHOP VIN_P_CHOP_D 0) capacitor c=1e-12
C_CHOP_N (VIN_N_CHOP VIN_N_CHOP_D 0) capacitor c=1e-12

// Differential amplifier
// Input pair
M1 (VOUT_P_AMP VIN_P_CHOP_D VBIAS_N VSSA) nmos w=100e-6 l=0.4e-6 model=nmos_40nm
M2 (VOUT_N_AMP VIN_N_CHOP_D VBIAS_N VSSA) nmos w=100e-6 l=0.4e-6 model=nmos_40nm

// Load transistors
M3 (VOUT_P_AMP VOUT_P_AMP VDDA VDDA) pmos w=50e-6 l=0.4e-6 model=pmos_40nm
M4 (VOUT_N_AMP VOUT_N_AMP VDDA VDDA) pmos w=50e-6 l=0.4e-6 model=pmos_40nm

// Current source
M5 (VBIAS_N VBIAS_N VSSA VSSA) nmos w=20e-6 l=0.4e-6 model=nmos_40nm

// Bias circuit
VBIAS (VBIAS_N 0) vsource dc=0.6

// Output chopper switches
SW_CHOP_OUT1 (VOUT_P_AMP VOUT_P_CHOP CHOPPER_CLK) switch model=chopper_switch
SW_CHOP_OUT2 (VOUT_N_AMP VOUT_N_CHOP CHOPPER_CLK) switch model=chopper_switch

// Output buffer
M6 (VOUT_P VOUT_P_CHOP VBIAS_N VSSA) nmos w=80e-6 l=0.4e-6 model=nmos_40nm
M7 (VOUT_P VOUT_P VDDA VDDA) pmos w=40e-6 l=0.4e-6 model=pmos_40nm
M8 (VOUT_N VOUT_N_CHOP VBIAS_N VSSA) nmos w=80e-6 l=0.4e-6 model=nmos_40nm
M9 (VOUT_N VOUT_N VDDA VDDA) pmos w=40e-6 l=0.4e-6 model=pmos_40nm

//=============================================================================
// Sample & Hold Circuit Implementation
//=============================================================================

// Sample switches
SW_SAMPLE_P (VOUT_P VIN_SH_P CLK) switch model=sample_switch
SW_SAMPLE_N (VOUT_N VIN_SH_N CLK) switch model=sample_switch

// Hold capacitors
C_HOLD_P (VIN_SH_P VHOLD_P 0) capacitor c=CHOLD
C_HOLD_N (VIN_SH_N VHOLD_N 0) capacitor c=CSAMPLE

// Hold switches
SW_HOLD_P (VHOLD_P VHOLD_P_OUT CLK) switch model=hold_switch
SW_HOLD_N (VHOLD_N VHOLD_N_OUT CLK) switch model=hold_switch

//=============================================================================
// SAR DAC Circuit Implementation
//=============================================================================

// Capacitor array (16-bit)
// MSB capacitors
C_DAC_15 (VREF_NET VDAC_OUT DAC_CODE_15) capacitor c=CUNIT*32768
C_DAC_14 (VREF_NET VDAC_OUT DAC_CODE_14) capacitor c=CUNIT*16384
C_DAC_13 (VREF_NET VDAC_OUT DAC_CODE_13) capacitor c=CUNIT*8192
C_DAC_12 (VREF_NET VDAC_OUT DAC_CODE_12) capacitor c=CUNIT*4096
C_DAC_11 (VREF_NET VDAC_OUT DAC_CODE_11) capacitor c=CUNIT*2048
C_DAC_10 (VREF_NET VDAC_OUT DAC_CODE_10) capacitor c=CUNIT*1024
C_DAC_9  (VREF_NET VDAC_OUT DAC_CODE_9)  capacitor c=CUNIT*512
C_DAC_8  (VREF_NET VDAC_OUT DAC_CODE_8)  capacitor c=CUNIT*256
C_DAC_7  (VREF_NET VDAC_OUT DAC_CODE_7)  capacitor c=CUNIT*128
C_DAC_6  (VREF_NET VDAC_OUT DAC_CODE_6)  capacitor c=CUNIT*64
C_DAC_5  (VREF_NET VDAC_OUT DAC_CODE_5)  capacitor c=CUNIT*32
C_DAC_4  (VREF_NET VDAC_OUT DAC_CODE_4)  capacitor c=CUNIT*16
C_DAC_3  (VREF_NET VDAC_OUT DAC_CODE_3)  capacitor c=CUNIT*8
C_DAC_2  (VREF_NET VDAC_OUT DAC_CODE_2)  capacitor c=CUNIT*4
C_DAC_1  (VREF_NET VDAC_OUT DAC_CODE_1)  capacitor c=CUNIT*2
C_DAC_0  (VREF_NET VDAC_OUT DAC_CODE_0)  capacitor c=CUNIT*1

// DAC control signals (digital to analog conversion)
VDAC_15 (DAC_CODE_15 0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_14 (DAC_CODE_14 0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_13 (DAC_CODE_13 0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_12 (DAC_CODE_12 0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_11 (DAC_CODE_11 0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_10 (DAC_CODE_10 0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_9  (DAC_CODE_9  0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_8  (DAC_CODE_8  0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_7  (DAC_CODE_7  0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_6  (DAC_CODE_6  0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_5  (DAC_CODE_5  0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_4  (DAC_CODE_4  0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_3  (DAC_CODE_3  0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_2  (DAC_CODE_2  0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_1  (DAC_CODE_1  0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9
VDAC_0  (DAC_CODE_0  0) vsource type=pulse val0=0 val1=VREF period=1e-6 rise=1e-9 fall=1e-9

//=============================================================================
// Comparator Circuit Implementation
//=============================================================================

// Preamp stage
M10 (VCOMP_PRE_P VHOLD_P_OUT VBIAS_COMP VSSA) nmos w=80e-6 l=0.4e-6 model=nmos_40nm
M11 (VCOMP_PRE_N VHOLD_N_OUT VBIAS_COMP VSSA) nmos w=80e-6 l=0.4e-6 model=nmos_40nm
M12 (VCOMP_PRE_P VCOMP_PRE_P VDDA VDDA) pmos w=40e-6 l=0.4e-6 model=pmos_40nm
M13 (VCOMP_PRE_N VCOMP_PRE_N VDDA VDDA) pmos w=40e-6 l=0.4e-6 model=pmos_40nm

// Comparator bias
VBIAS_COMP (VBIAS_COMP 0) vsource dc=0.6

// Latch stage
M14 (VCOMP_LATCH_P VCOMP_PRE_P VBIAS_LATCH VSSA) nmos w=30e-6 l=0.4e-6 model=nmos_40nm
M15 (VCOMP_LATCH_N VCOMP_PRE_N VBIAS_LATCH VSSA) nmos w=30e-6 l=0.4e-6 model=nmos_40nm
M16 (VCOMP_LATCH_P VCOMP_LATCH_P VDDA VDDA) pmos w=15e-6 l=0.4e-6 model=pmos_40nm
M17 (VCOMP_LATCH_N VCOMP_LATCH_N VDDA VDDA) pmos w=15e-6 l=0.4e-6 model=pmos_40nm

// Latch bias
VBIAS_LATCH (VBIAS_LATCH 0) vsource dc=0.6

// Output buffer
M18 (COMP_OUT VCOMP_LATCH_P VBIAS_OUT VSSA) nmos w=20e-6 l=0.4e-6 model=nmos_40nm
M19 (COMP_OUT COMP_OUT VDDA VDDA) pmos w=10e-6 l=0.4e-6 model=pmos_40nm

// Output bias
VBIAS_OUT (VBIAS_OUT 0) vsource dc=0.6

//=============================================================================
// Analysis setup
//=============================================================================

// DC analysis
dc dc param=VDDA start=2.5 stop=3.0 step=0.1

// Transient analysis
tran tran stop=100e-6 step=1e-9

// AC analysis
ac ac start=1e3 stop=10e6 dec=10

//=============================================================================
// Output signals
//=============================================================================
// Monitor key signals
save VIN_P_NET VIN_N_NET
save VOUT_P VOUT_N
save VHOLD_P VHOLD_N
save VDAC_OUT
save COMP_OUT
save CLK CHOPPER_CLK

//=============================================================================
// End of netlist
//============================================================================= 