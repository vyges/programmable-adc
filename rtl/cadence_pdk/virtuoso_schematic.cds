//=============================================================================
// Virtuoso Schematic Capture File
//=============================================================================
// Description: Virtuoso schematic for Programmable ADC
// Author: Vyges IP Development Team
// Date: 2024
//=============================================================================

//=============================================================================
// Cell: programmable_adc_schematic
//=============================================================================
cell: programmable_adc_schematic
{
  //=============================================================================
  // Ports
  //=============================================================================
  port: vin_p
  port: vin_n
  port: vout_p
  port: vout_n
  port: vdda
  port: vssa
  port: clk
  port: chopper_clk
  port: dac_code_15
  port: dac_code_14
  port: dac_code_13
  port: dac_code_12
  port: dac_code_11
  port: dac_code_10
  port: dac_code_9
  port: dac_code_8
  port: dac_code_7
  port: dac_code_6
  port: dac_code_5
  port: dac_code_4
  port: dac_code_3
  port: dac_code_2
  port: dac_code_1
  port: dac_code_0
  port: comp_out
  port: vref

  //=============================================================================
  // PGA Circuit Instance
  //=============================================================================
  instance: XPGA
  {
    cell: pga_circuit
    view: schematic
    location: (1000, 2000)
    rotation: 0
    mirror: 0
    parameters: {
      gain: 1
      bandwidth: 1e6
      noise_density: 10e-9
    }
  }

  //=============================================================================
  // Sample & Hold Circuit Instance
  //=============================================================================
  instance: XSH
  {
    cell: sample_hold_circuit
    view: schematic
    location: (2000, 2000)
    rotation: 0
    mirror: 0
    parameters: {
      sample_cap: 10e-12
      hold_cap: 2e-12
      switch_ron: 50
    }
  }

  //=============================================================================
  // SAR DAC Circuit Instance
  //=============================================================================
  instance: XDAC
  {
    cell: sar_dac_circuit
    view: schematic
    location: (3000, 2000)
    rotation: 0
    mirror: 0
    parameters: {
      resolution: 16
      cap_unit: 1e-15
      settling_time: 100e-9
    }
  }

  //=============================================================================
  // Comparator Circuit Instance
  //=============================================================================
  instance: XCOMP
  {
    cell: comparator_circuit
    view: schematic
    location: (4000, 2000)
    rotation: 0
    mirror: 0
    parameters: {
      offset: 1e-6
      hysteresis: 1e-6
      delay: 10e-9
    }
  }

  //=============================================================================
  // Wire Connections
  //=============================================================================
  wire: {
    from: vin_p
    to: XPGA.vin_p
  }
  wire: {
    from: vin_n
    to: XPGA.vin_n
  }
  wire: {
    from: XPGA.vout_p
    to: XSH.vin_p
  }
  wire: {
    from: XPGA.vout_n
    to: XSH.vin_n
  }
  wire: {
    from: XSH.vout_p
    to: XCOMP.vin_p
  }
  wire: {
    from: XSH.vout_n
    to: XCOMP.vin_n
  }
  wire: {
    from: XCOMP.comp_out
    to: comp_out
  }
  wire: {
    from: vdda
    to: XPGA.vdda
    to: XSH.vdda
    to: XDAC.vdda
    to: XCOMP.vdda
  }
  wire: {
    from: vssa
    to: XPGA.vssa
    to: XSH.vssa
    to: XDAC.vssa
    to: XCOMP.vssa
  }
  wire: {
    from: clk
    to: XPGA.clk
    to: XSH.clk
    to: XCOMP.clk
  }
  wire: {
    from: chopper_clk
    to: XPGA.chopper_clk
  }
  wire: {
    from: vref
    to: XDAC.vref
  }
  wire: {
    from: dac_code_15
    to: XDAC.dac_code_15
  }
  wire: {
    from: dac_code_14
    to: XDAC.dac_code_14
  }
  wire: {
    from: dac_code_13
    to: XDAC.dac_code_13
  }
  wire: {
    from: dac_code_12
    to: XDAC.dac_code_12
  }
  wire: {
    from: dac_code_11
    to: XDAC.dac_code_11
  }
  wire: {
    from: dac_code_10
    to: XDAC.dac_code_10
  }
  wire: {
    from: dac_code_9
    to: XDAC.dac_code_9
  }
  wire: {
    from: dac_code_8
    to: XDAC.dac_code_8
  }
  wire: {
    from: dac_code_7
    to: XDAC.dac_code_7
  }
  wire: {
    from: dac_code_6
    to: XDAC.dac_code_6
  }
  wire: {
    from: dac_code_5
    to: XDAC.dac_code_5
  }
  wire: {
    from: dac_code_4
    to: XDAC.dac_code_4
  }
  wire: {
    from: dac_code_3
    to: XDAC.dac_code_3
  }
  wire: {
    from: dac_code_2
    to: XDAC.dac_code_2
  }
  wire: {
    from: dac_code_1
    to: XDAC.dac_code_1
  }
  wire: {
    from: dac_code_0
    to: XDAC.dac_code_0
  }

  //=============================================================================
  // Properties
  //=============================================================================
  property: {
    name: "cellType"
    value: "schematic"
  }
  property: {
    name: "viewType"
    value: "schematic"
  }
  property: {
    name: "simulator"
    value: "spectre"
  }
  property: {
    name: "netlistType"
    value: "spectre"
  }
  property: {
    name: "modelFile"
    value: "models.scs"
  }
  property: {
    name: "corner"
    value: "tt"
  }
}

//=============================================================================
// Cell: pga_circuit
//=============================================================================
cell: pga_circuit
{
  //=============================================================================
  // Ports
  //=============================================================================
  port: vin_p
  port: vin_n
  port: vout_p
  port: vout_n
  port: vdda
  port: vssa
  port: clk
  port: chopper_clk

  //=============================================================================
  // Input Chopper Switches
  //=============================================================================
  instance: SW_CHOP_IN1
  {
    cell: chopper_switch
    view: symbol
    location: (500, 1800)
    rotation: 0
    mirror: 0
  }
  instance: SW_CHOP_IN2
  {
    cell: chopper_switch
    view: symbol
    location: (500, 1600)
    rotation: 0
    mirror: 0
  }

  //=============================================================================
  // Chopper Capacitors
  //=============================================================================
  instance: C_CHOP_P
  {
    cell: cap_40nm
    view: symbol
    location: (700, 1800)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-12
    }
  }
  instance: C_CHOP_N
  {
    cell: cap_40nm
    view: symbol
    location: (700, 1600)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-12
    }
  }

  //=============================================================================
  // Differential Amplifier
  //=============================================================================
  instance: M1
  {
    cell: nmos_40nm
    view: symbol
    location: (1000, 1800)
    rotation: 0
    mirror: 0
    parameters: {
      w: 100e-6
      l: 0.4e-6
    }
  }
  instance: M2
  {
    cell: nmos_40nm
    view: symbol
    location: (1000, 1600)
    rotation: 0
    mirror: 0
    parameters: {
      w: 100e-6
      l: 0.4e-6
    }
  }
  instance: M3
  {
    cell: pmos_40nm
    view: symbol
    location: (1000, 2000)
    rotation: 0
    mirror: 0
    parameters: {
      w: 50e-6
      l: 0.4e-6
    }
  }
  instance: M4
  {
    cell: pmos_40nm
    view: symbol
    location: (1000, 2200)
    rotation: 0
    mirror: 0
    parameters: {
      w: 50e-6
      l: 0.4e-6
    }
  }

  //=============================================================================
  // Output Chopper Switches
  //=============================================================================
  instance: SW_CHOP_OUT1
  {
    cell: chopper_switch
    view: symbol
    location: (1200, 1800)
    rotation: 0
    mirror: 0
  }
  instance: SW_CHOP_OUT2
  {
    cell: chopper_switch
    view: symbol
    location: (1200, 1600)
    rotation: 0
    mirror: 0
  }

  //=============================================================================
  // Output Buffers
  //=============================================================================
  instance: M6
  {
    cell: nmos_40nm
    view: symbol
    location: (1400, 1800)
    rotation: 0
    mirror: 0
    parameters: {
      w: 80e-6
      l: 0.4e-6
    }
  }
  instance: M7
  {
    cell: pmos_40nm
    view: symbol
    location: (1400, 2000)
    rotation: 0
    mirror: 0
    parameters: {
      w: 40e-6
      l: 0.4e-6
    }
  }
  instance: M8
  {
    cell: nmos_40nm
    view: symbol
    location: (1400, 1600)
    rotation: 0
    mirror: 0
    parameters: {
      w: 80e-6
      l: 0.4e-6
    }
  }
  instance: M9
  {
    cell: pmos_40nm
    view: symbol
    location: (1400, 1400)
    rotation: 0
    mirror: 0
    parameters: {
      w: 40e-6
      l: 0.4e-6
    }
  }

  //=============================================================================
  // Wire Connections
  //=============================================================================
  wire: {
    from: vin_p
    to: SW_CHOP_IN1.1
  }
  wire: {
    from: SW_CHOP_IN1.2
    to: C_CHOP_P.1
  }
  wire: {
    from: C_CHOP_P.2
    to: M1.gate
  }
  wire: {
    from: vin_n
    to: SW_CHOP_IN2.1
  }
  wire: {
    from: SW_CHOP_IN2.2
    to: C_CHOP_N.1
  }
  wire: {
    from: C_CHOP_N.2
    to: M2.gate
  }
  wire: {
    from: M1.drain
    to: M3.drain
    to: SW_CHOP_OUT1.1
  }
  wire: {
    from: M2.drain
    to: M4.drain
    to: SW_CHOP_OUT2.1
  }
  wire: {
    from: SW_CHOP_OUT1.2
    to: M6.gate
  }
  wire: {
    from: SW_CHOP_OUT2.2
    to: M8.gate
  }
  wire: {
    from: M6.drain
    to: M7.drain
    to: vout_p
  }
  wire: {
    from: M8.drain
    to: M9.drain
    to: vout_n
  }
  wire: {
    from: vdda
    to: M3.source
    to: M4.source
    to: M7.source
    to: M9.source
  }
  wire: {
    from: vssa
    to: M1.source
    to: M2.source
    to: M6.source
    to: M8.source
    to: C_CHOP_P.3
    to: C_CHOP_N.3
  }
  wire: {
    from: clk
    to: SW_CHOP_IN1.3
    to: SW_CHOP_IN2.3
  }
  wire: {
    from: chopper_clk
    to: SW_CHOP_OUT1.3
    to: SW_CHOP_OUT2.3
  }
}

//=============================================================================
// Cell: sample_hold_circuit
//=============================================================================
cell: sample_hold_circuit
{
  //=============================================================================
  // Ports
  //=============================================================================
  port: vin_p
  port: vin_n
  port: vout_p
  port: vout_n
  port: vdda
  port: vssa
  port: clk

  //=============================================================================
  // Sample Switches
  //=============================================================================
  instance: SW_SAMPLE_P
  {
    cell: sample_switch
    view: symbol
    location: (500, 1800)
    rotation: 0
    mirror: 0
  }
  instance: SW_SAMPLE_N
  {
    cell: sample_switch
    view: symbol
    location: (500, 1600)
    rotation: 0
    mirror: 0
  }

  //=============================================================================
  // Hold Capacitors
  //=============================================================================
  instance: C_HOLD_P
  {
    cell: cap_40nm
    view: symbol
    location: (700, 1800)
    rotation: 0
    mirror: 0
    parameters: {
      c: 10e-12
    }
  }
  instance: C_HOLD_N
  {
    cell: cap_40nm
    view: symbol
    location: (700, 1600)
    rotation: 0
    mirror: 0
    parameters: {
      c: 2e-12
    }
  }

  //=============================================================================
  // Hold Switches
  //=============================================================================
  instance: SW_HOLD_P
  {
    cell: hold_switch
    view: symbol
    location: (900, 1800)
    rotation: 0
    mirror: 0
  }
  instance: SW_HOLD_N
  {
    cell: hold_switch
    view: symbol
    location: (900, 1600)
    rotation: 0
    mirror: 0
  }

  //=============================================================================
  // Output Buffers
  //=============================================================================
  instance: M10
  {
    cell: nmos_40nm
    view: symbol
    location: (1100, 1800)
    rotation: 0
    mirror: 0
    parameters: {
      w: 60e-6
      l: 0.4e-6
    }
  }
  instance: M11
  {
    cell: pmos_40nm
    view: symbol
    location: (1100, 2000)
    rotation: 0
    mirror: 0
    parameters: {
      w: 30e-6
      l: 0.4e-6
    }
  }
  instance: M12
  {
    cell: nmos_40nm
    view: symbol
    location: (1100, 1600)
    rotation: 0
    mirror: 0
    parameters: {
      w: 60e-6
      l: 0.4e-6
    }
  }
  instance: M13
  {
    cell: pmos_40nm
    view: symbol
    location: (1100, 1400)
    rotation: 0
    mirror: 0
    parameters: {
      w: 30e-6
      l: 0.4e-6
    }
  }

  //=============================================================================
  // Wire Connections
  //=============================================================================
  wire: {
    from: vin_p
    to: SW_SAMPLE_P.1
  }
  wire: {
    from: SW_SAMPLE_P.2
    to: C_HOLD_P.1
  }
  wire: {
    from: C_HOLD_P.2
    to: SW_HOLD_P.1
  }
  wire: {
    from: SW_HOLD_P.2
    to: M10.gate
  }
  wire: {
    from: vin_n
    to: SW_SAMPLE_N.1
  }
  wire: {
    from: SW_SAMPLE_N.2
    to: C_HOLD_N.1
  }
  wire: {
    from: C_HOLD_N.2
    to: SW_HOLD_N.1
  }
  wire: {
    from: SW_HOLD_N.2
    to: M12.gate
  }
  wire: {
    from: M10.drain
    to: M11.drain
    to: vout_p
  }
  wire: {
    from: M12.drain
    to: M13.drain
    to: vout_n
  }
  wire: {
    from: vdda
    to: M11.source
    to: M13.source
  }
  wire: {
    from: vssa
    to: M10.source
    to: M12.source
    to: C_HOLD_P.3
    to: C_HOLD_N.3
  }
  wire: {
    from: clk
    to: SW_SAMPLE_P.3
    to: SW_SAMPLE_N.3
    to: SW_HOLD_P.3
    to: SW_HOLD_N.3
  }
}

//=============================================================================
// Cell: sar_dac_circuit
//=============================================================================
cell: sar_dac_circuit
{
  //=============================================================================
  // Ports
  //=============================================================================
  port: vref
  port: vdac_out
  port: vdda
  port: vssa
  port: dac_code_15
  port: dac_code_14
  port: dac_code_13
  port: dac_code_12
  port: dac_code_11
  port: dac_code_10
  port: dac_code_9
  port: dac_code_8
  port: dac_code_7
  port: dac_code_6
  port: dac_code_5
  port: dac_code_4
  port: dac_code_3
  port: dac_code_2
  port: dac_code_1
  port: dac_code_0

  //=============================================================================
  // Capacitor Array (16-bit)
  //=============================================================================
  instance: C_DAC_15
  {
    cell: cap_40nm
    view: symbol
    location: (500, 2400)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_14
  {
    cell: cap_40nm
    view: symbol
    location: (500, 2200)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_13
  {
    cell: cap_40nm
    view: symbol
    location: (500, 2000)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_12
  {
    cell: cap_40nm
    view: symbol
    location: (500, 1800)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_11
  {
    cell: cap_40nm
    view: symbol
    location: (500, 1600)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_10
  {
    cell: cap_40nm
    view: symbol
    location: (500, 1400)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_9
  {
    cell: cap_40nm
    view: symbol
    location: (500, 1200)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_8
  {
    cell: cap_40nm
    view: symbol
    location: (500, 1000)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_7
  {
    cell: cap_40nm
    view: symbol
    location: (500, 800)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_6
  {
    cell: cap_40nm
    view: symbol
    location: (500, 600)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_5
  {
    cell: cap_40nm
    view: symbol
    location: (500, 400)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_4
  {
    cell: cap_40nm
    view: symbol
    location: (500, 200)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_3
  {
    cell: cap_40nm
    view: symbol
    location: (500, 0)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_2
  {
    cell: cap_40nm
    view: symbol
    location: (500, -200)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_1
  {
    cell: cap_40nm
    view: symbol
    location: (500, -400)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }
  instance: C_DAC_0
  {
    cell: cap_40nm
    view: symbol
    location: (500, -600)
    rotation: 0
    mirror: 0
    parameters: {
      c: 1e-15
    }
  }

  //=============================================================================
  // Wire Connections
  //=============================================================================
  wire: {
    from: vref
    to: C_DAC_15.1
    to: C_DAC_14.1
    to: C_DAC_13.1
    to: C_DAC_12.1
    to: C_DAC_11.1
    to: C_DAC_10.1
    to: C_DAC_9.1
    to: C_DAC_8.1
    to: C_DAC_7.1
    to: C_DAC_6.1
    to: C_DAC_5.1
    to: C_DAC_4.1
    to: C_DAC_3.1
    to: C_DAC_2.1
    to: C_DAC_1.1
    to: C_DAC_0.1
  }
  wire: {
    from: C_DAC_15.2
    to: C_DAC_14.2
    to: C_DAC_13.2
    to: C_DAC_12.2
    to: C_DAC_11.2
    to: C_DAC_10.2
    to: C_DAC_9.2
    to: C_DAC_8.2
    to: C_DAC_7.2
    to: C_DAC_6.2
    to: C_DAC_5.2
    to: C_DAC_4.2
    to: C_DAC_3.2
    to: C_DAC_2.2
    to: C_DAC_1.2
    to: C_DAC_0.2
    to: vdac_out
  }
  wire: {
    from: dac_code_15
    to: C_DAC_15.3
  }
  wire: {
    from: dac_code_14
    to: C_DAC_14.3
  }
  wire: {
    from: dac_code_13
    to: C_DAC_13.3
  }
  wire: {
    from: dac_code_12
    to: C_DAC_12.3
  }
  wire: {
    from: dac_code_11
    to: C_DAC_11.3
  }
  wire: {
    from: dac_code_10
    to: C_DAC_10.3
  }
  wire: {
    from: dac_code_9
    to: C_DAC_9.3
  }
  wire: {
    from: dac_code_8
    to: C_DAC_8.3
  }
  wire: {
    from: dac_code_7
    to: C_DAC_7.3
  }
  wire: {
    from: dac_code_6
    to: C_DAC_6.3
  }
  wire: {
    from: dac_code_5
    to: C_DAC_5.3
  }
  wire: {
    from: dac_code_4
    to: C_DAC_4.3
  }
  wire: {
    from: dac_code_3
    to: C_DAC_3.3
  }
  wire: {
    from: dac_code_2
    to: C_DAC_2.3
  }
  wire: {
    from: dac_code_1
    to: C_DAC_1.3
  }
  wire: {
    from: dac_code_0
    to: C_DAC_0.3
  }
}

//=============================================================================
// Cell: comparator_circuit
//=============================================================================
cell: comparator_circuit
{
  //=============================================================================
  // Ports
  //=============================================================================
  port: vin_p
  port: vin_n
  port: comp_out
  port: vdda
  port: vssa
  port: clk

  //=============================================================================
  // Preamp Stage
  //=============================================================================
  instance: M14
  {
    cell: nmos_40nm
    view: symbol
    location: (500, 1800)
    rotation: 0
    mirror: 0
    parameters: {
      w: 80e-6
      l: 0.4e-6
    }
  }
  instance: M15
  {
    cell: nmos_40nm
    view: symbol
    location: (500, 1600)
    rotation: 0
    mirror: 0
    parameters: {
      w: 80e-6
      l: 0.4e-6
    }
  }
  instance: M16
  {
    cell: pmos_40nm
    view: symbol
    location: (500, 2000)
    rotation: 0
    mirror: 0
    parameters: {
      w: 40e-6
      l: 0.4e-6
    }
  }
  instance: M17
  {
    cell: pmos_40nm
    view: symbol
    location: (500, 2200)
    rotation: 0
    mirror: 0
    parameters: {
      w: 40e-6
      l: 0.4e-6
    }
  }

  //=============================================================================
  // Latch Stage
  //=============================================================================
  instance: M18
  {
    cell: nmos_40nm
    view: symbol
    location: (700, 1800)
    rotation: 0
    mirror: 0
    parameters: {
      w: 30e-6
      l: 0.4e-6
    }
  }
  instance: M19
  {
    cell: nmos_40nm
    view: symbol
    location: (700, 1600)
    rotation: 0
    mirror: 0
    parameters: {
      w: 30e-6
      l: 0.4e-6
    }
  }
  instance: M20
  {
    cell: pmos_40nm
    view: symbol
    location: (700, 2000)
    rotation: 0
    mirror: 0
    parameters: {
      w: 15e-6
      l: 0.4e-6
    }
  }
  instance: M21
  {
    cell: pmos_40nm
    view: symbol
    location: (700, 2200)
    rotation: 0
    mirror: 0
    parameters: {
      w: 15e-6
      l: 0.4e-6
    }
  }

  //=============================================================================
  // Output Buffer
  //=============================================================================
  instance: M22
  {
    cell: nmos_40nm
    view: symbol
    location: (900, 1800)
    rotation: 0
    mirror: 0
    parameters: {
      w: 20e-6
      l: 0.4e-6
    }
  }
  instance: M23
  {
    cell: pmos_40nm
    view: symbol
    location: (900, 2000)
    rotation: 0
    mirror: 0
    parameters: {
      w: 10e-6
      l: 0.4e-6
    }
  }

  //=============================================================================
  // Wire Connections
  //=============================================================================
  wire: {
    from: vin_p
    to: M14.gate
  }
  wire: {
    from: vin_n
    to: M15.gate
  }
  wire: {
    from: M14.drain
    to: M16.drain
    to: M18.gate
  }
  wire: {
    from: M15.drain
    to: M17.drain
    to: M19.gate
  }
  wire: {
    from: M18.drain
    to: M20.drain
    to: M22.gate
  }
  wire: {
    from: M19.drain
    to: M21.drain
  }
  wire: {
    from: M22.drain
    to: M23.drain
    to: comp_out
  }
  wire: {
    from: vdda
    to: M16.source
    to: M17.source
    to: M20.source
    to: M21.source
    to: M23.source
  }
  wire: {
    from: vssa
    to: M14.source
    to: M15.source
    to: M18.source
    to: M19.source
    to: M22.source
  }
} 