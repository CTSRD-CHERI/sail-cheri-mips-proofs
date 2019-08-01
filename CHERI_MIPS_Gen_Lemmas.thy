theory CHERI_MIPS_Gen_Lemmas
imports CHERI_MIPS_Instantiation
begin

context CHERI_MIPS_Axiom_Inv_Automaton
begin

lemma non_cap_regsI[intro, simp]:
  "non_cap_reg BranchPending_ref"
  "non_cap_reg CID_ref"
  "non_cap_reg CP0BadInstr_ref"
  "non_cap_reg CP0BadInstrP_ref"
  "non_cap_reg CP0BadVAddr_ref"
  "non_cap_reg CP0Cause_ref"
  "non_cap_reg CP0Compare_ref"
  "non_cap_reg CP0ConfigK0_ref"
  "non_cap_reg CP0Count_ref"
  "non_cap_reg CP0HWREna_ref"
  "non_cap_reg CP0LLAddr_ref"
  "non_cap_reg CP0LLBit_ref"
  "non_cap_reg CP0Status_ref"
  "non_cap_reg CP0UserLocal_ref"
  "non_cap_reg CurrentInstrBits_ref"
  "non_cap_reg DelayedPC_ref"
  "non_cap_reg GPR_ref"
  "non_cap_reg HI_ref"
  "non_cap_reg InBranchDelay_ref"
  "non_cap_reg LO_ref"
  "non_cap_reg LastInstrBits_ref"
  "non_cap_reg NextInBranchDelay_ref"
  "non_cap_reg NextPC_ref"
  "non_cap_reg PC_ref"
  "non_cap_reg TLBContext_ref"
  "non_cap_reg TLBEntry00_ref"
  "non_cap_reg TLBEntry01_ref"
  "non_cap_reg TLBEntry02_ref"
  "non_cap_reg TLBEntry03_ref"
  "non_cap_reg TLBEntry04_ref"
  "non_cap_reg TLBEntry05_ref"
  "non_cap_reg TLBEntry06_ref"
  "non_cap_reg TLBEntry07_ref"
  "non_cap_reg TLBEntry08_ref"
  "non_cap_reg TLBEntry09_ref"
  "non_cap_reg TLBEntry10_ref"
  "non_cap_reg TLBEntry11_ref"
  "non_cap_reg TLBEntry12_ref"
  "non_cap_reg TLBEntry13_ref"
  "non_cap_reg TLBEntry14_ref"
  "non_cap_reg TLBEntry15_ref"
  "non_cap_reg TLBEntry16_ref"
  "non_cap_reg TLBEntry17_ref"
  "non_cap_reg TLBEntry18_ref"
  "non_cap_reg TLBEntry19_ref"
  "non_cap_reg TLBEntry20_ref"
  "non_cap_reg TLBEntry21_ref"
  "non_cap_reg TLBEntry22_ref"
  "non_cap_reg TLBEntry23_ref"
  "non_cap_reg TLBEntry24_ref"
  "non_cap_reg TLBEntry25_ref"
  "non_cap_reg TLBEntry26_ref"
  "non_cap_reg TLBEntry27_ref"
  "non_cap_reg TLBEntry28_ref"
  "non_cap_reg TLBEntry29_ref"
  "non_cap_reg TLBEntry30_ref"
  "non_cap_reg TLBEntry31_ref"
  "non_cap_reg TLBEntry32_ref"
  "non_cap_reg TLBEntry33_ref"
  "non_cap_reg TLBEntry34_ref"
  "non_cap_reg TLBEntry35_ref"
  "non_cap_reg TLBEntry36_ref"
  "non_cap_reg TLBEntry37_ref"
  "non_cap_reg TLBEntry38_ref"
  "non_cap_reg TLBEntry39_ref"
  "non_cap_reg TLBEntry40_ref"
  "non_cap_reg TLBEntry41_ref"
  "non_cap_reg TLBEntry42_ref"
  "non_cap_reg TLBEntry43_ref"
  "non_cap_reg TLBEntry44_ref"
  "non_cap_reg TLBEntry45_ref"
  "non_cap_reg TLBEntry46_ref"
  "non_cap_reg TLBEntry47_ref"
  "non_cap_reg TLBEntry48_ref"
  "non_cap_reg TLBEntry49_ref"
  "non_cap_reg TLBEntry50_ref"
  "non_cap_reg TLBEntry51_ref"
  "non_cap_reg TLBEntry52_ref"
  "non_cap_reg TLBEntry53_ref"
  "non_cap_reg TLBEntry54_ref"
  "non_cap_reg TLBEntry55_ref"
  "non_cap_reg TLBEntry56_ref"
  "non_cap_reg TLBEntry57_ref"
  "non_cap_reg TLBEntry58_ref"
  "non_cap_reg TLBEntry59_ref"
  "non_cap_reg TLBEntry60_ref"
  "non_cap_reg TLBEntry61_ref"
  "non_cap_reg TLBEntry62_ref"
  "non_cap_reg TLBEntry63_ref"
  "non_cap_reg TLBEntryHi_ref"
  "non_cap_reg TLBEntryLo0_ref"
  "non_cap_reg TLBEntryLo1_ref"
  "non_cap_reg TLBIndex_ref"
  "non_cap_reg TLBPageMask_ref"
  "non_cap_reg TLBProbe_ref"
  "non_cap_reg TLBRandom_ref"
  "non_cap_reg TLBWired_ref"
  "non_cap_reg TLBXContext_ref"
  "non_cap_reg UART_RDATA_ref"
  "non_cap_reg UART_RVALID_ref"
  "non_cap_reg UART_WDATA_ref"
  "non_cap_reg UART_WRITTEN_ref"
  unfolding BranchPending_ref_def CID_ref_def CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0BadVAddr_ref_def
     CP0Cause_ref_def CP0Compare_ref_def CP0ConfigK0_ref_def CP0Count_ref_def CP0HWREna_ref_def
     CP0LLAddr_ref_def CP0LLBit_ref_def CP0Status_ref_def CP0UserLocal_ref_def CurrentInstrBits_ref_def
     DelayedPC_ref_def GPR_ref_def HI_ref_def InBranchDelay_ref_def LO_ref_def
     LastInstrBits_ref_def NextInBranchDelay_ref_def NextPC_ref_def PC_ref_def TLBContext_ref_def
     TLBEntry00_ref_def TLBEntry01_ref_def TLBEntry02_ref_def TLBEntry03_ref_def TLBEntry04_ref_def
     TLBEntry05_ref_def TLBEntry06_ref_def TLBEntry07_ref_def TLBEntry08_ref_def TLBEntry09_ref_def
     TLBEntry10_ref_def TLBEntry11_ref_def TLBEntry12_ref_def TLBEntry13_ref_def TLBEntry14_ref_def
     TLBEntry15_ref_def TLBEntry16_ref_def TLBEntry17_ref_def TLBEntry18_ref_def TLBEntry19_ref_def
     TLBEntry20_ref_def TLBEntry21_ref_def TLBEntry22_ref_def TLBEntry23_ref_def TLBEntry24_ref_def
     TLBEntry25_ref_def TLBEntry26_ref_def TLBEntry27_ref_def TLBEntry28_ref_def TLBEntry29_ref_def
     TLBEntry30_ref_def TLBEntry31_ref_def TLBEntry32_ref_def TLBEntry33_ref_def TLBEntry34_ref_def
     TLBEntry35_ref_def TLBEntry36_ref_def TLBEntry37_ref_def TLBEntry38_ref_def TLBEntry39_ref_def
     TLBEntry40_ref_def TLBEntry41_ref_def TLBEntry42_ref_def TLBEntry43_ref_def TLBEntry44_ref_def
     TLBEntry45_ref_def TLBEntry46_ref_def TLBEntry47_ref_def TLBEntry48_ref_def TLBEntry49_ref_def
     TLBEntry50_ref_def TLBEntry51_ref_def TLBEntry52_ref_def TLBEntry53_ref_def TLBEntry54_ref_def
     TLBEntry55_ref_def TLBEntry56_ref_def TLBEntry57_ref_def TLBEntry58_ref_def TLBEntry59_ref_def
     TLBEntry60_ref_def TLBEntry61_ref_def TLBEntry62_ref_def TLBEntry63_ref_def TLBEntryHi_ref_def
     TLBEntryLo0_ref_def TLBEntryLo1_ref_def TLBIndex_ref_def TLBPageMask_ref_def TLBProbe_ref_def
     TLBRandom_ref_def TLBWired_ref_def TLBXContext_ref_def UART_RDATA_ref_def UART_RVALID_ref_def
     UART_WDATA_ref_def UART_WRITTEN_ref_def
  by (auto simp: non_cap_reg_def)

lemmas non_cap_exp_rw_non_cap_reg[non_cap_expI] =
  non_cap_regsI[THEN non_cap_exp_read_non_cap_reg]
  non_cap_regsI[THEN non_cap_exp_write_non_cap_reg]

lemma non_cap_exp_undefined_option[non_cap_expI]:
  "non_cap_exp (undefined_option arg0)"
  by (non_cap_expI simp: undefined_option_def)

lemma non_cap_exp_undefined_exception[non_cap_expI]:
  "non_cap_exp (undefined_exception arg0)"
  by (non_cap_expI simp: undefined_exception_def)

lemma non_cap_exp_undefined_CauseReg[non_cap_expI]:
  "non_cap_exp (undefined_CauseReg arg0)"
  by (non_cap_expI simp: undefined_CauseReg_def)

lemma non_cap_exp_set_CauseReg_bits[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_CauseReg_bits arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_CauseReg_bits_def)

lemma non_cap_exp_set_CauseReg_BD[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_CauseReg_BD arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_CauseReg_BD_def)

lemma non_cap_exp_set_CauseReg_CE[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_CauseReg_CE arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_CauseReg_CE_def)

lemma non_cap_exp_set_CauseReg_IV[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_CauseReg_IV arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_CauseReg_IV_def)

lemma non_cap_exp_set_CauseReg_WP[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_CauseReg_WP arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_CauseReg_WP_def)

lemma non_cap_exp_set_CauseReg_IP[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_CauseReg_IP arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_CauseReg_IP_def)

lemma non_cap_exp_set_CauseReg_ExcCode[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_CauseReg_ExcCode arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_CauseReg_ExcCode_def)

lemma non_cap_exp_undefined_TLBEntryLoReg[non_cap_expI]:
  "non_cap_exp (undefined_TLBEntryLoReg arg0)"
  by (non_cap_expI simp: undefined_TLBEntryLoReg_def)

lemma non_cap_exp_set_TLBEntryLoReg_bits[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntryLoReg_bits arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntryLoReg_bits_def)

lemma non_cap_exp_set_TLBEntryLoReg_CapS[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntryLoReg_CapS arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntryLoReg_CapS_def)

lemma non_cap_exp_set_TLBEntryLoReg_CapL[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntryLoReg_CapL arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntryLoReg_CapL_def)

lemma non_cap_exp_set_TLBEntryLoReg_PFN[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntryLoReg_PFN arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntryLoReg_PFN_def)

lemma non_cap_exp_set_TLBEntryLoReg_C[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntryLoReg_C arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntryLoReg_C_def)

lemma non_cap_exp_set_TLBEntryLoReg_D[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntryLoReg_D arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntryLoReg_D_def)

lemma non_cap_exp_set_TLBEntryLoReg_V[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntryLoReg_V arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntryLoReg_V_def)

lemma non_cap_exp_set_TLBEntryLoReg_G[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntryLoReg_G arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntryLoReg_G_def)

lemma non_cap_exp_undefined_TLBEntryHiReg[non_cap_expI]:
  "non_cap_exp (undefined_TLBEntryHiReg arg0)"
  by (non_cap_expI simp: undefined_TLBEntryHiReg_def)

lemma non_cap_exp_set_TLBEntryHiReg_bits[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntryHiReg_bits arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntryHiReg_bits_def)

lemma non_cap_exp_set_TLBEntryHiReg_R[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntryHiReg_R arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntryHiReg_R_def)

lemma non_cap_exp_set_TLBEntryHiReg_VPN2[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntryHiReg_VPN2 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntryHiReg_VPN2_def)

lemma non_cap_exp_set_TLBEntryHiReg_ASID[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntryHiReg_ASID arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntryHiReg_ASID_def)

lemma non_cap_exp_undefined_ContextReg[non_cap_expI]:
  "non_cap_exp (undefined_ContextReg arg0)"
  by (non_cap_expI simp: undefined_ContextReg_def)

lemma non_cap_exp_set_ContextReg_bits[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_ContextReg_bits arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_ContextReg_bits_def)

lemma non_cap_exp_set_ContextReg_PTEBase[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_ContextReg_PTEBase arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_ContextReg_PTEBase_def)

lemma non_cap_exp_set_ContextReg_BadVPN2[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_ContextReg_BadVPN2 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_ContextReg_BadVPN2_def)

lemma non_cap_exp_undefined_XContextReg[non_cap_expI]:
  "non_cap_exp (undefined_XContextReg arg0)"
  by (non_cap_expI simp: undefined_XContextReg_def)

lemma non_cap_exp_set_XContextReg_bits[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_XContextReg_bits arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_XContextReg_bits_def)

lemma non_cap_exp_set_XContextReg_XPTEBase[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_XContextReg_XPTEBase arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_XContextReg_XPTEBase_def)

lemma non_cap_exp_set_XContextReg_XR[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_XContextReg_XR arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_XContextReg_XR_def)

lemma non_cap_exp_set_XContextReg_XBadVPN2[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_XContextReg_XBadVPN2 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_XContextReg_XBadVPN2_def)

lemma non_cap_exp_undefined_TLBEntry[non_cap_expI]:
  "non_cap_exp (undefined_TLBEntry arg0)"
  by (non_cap_expI simp: undefined_TLBEntry_def)

lemma non_cap_exp_set_TLBEntry_bits[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_bits arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_bits_def)

lemma non_cap_exp_set_TLBEntry_pagemask[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_pagemask arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_pagemask_def)

lemma non_cap_exp_set_TLBEntry_r[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_r arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_r_def)

lemma non_cap_exp_set_TLBEntry_vpn2[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_vpn2 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_vpn2_def)

lemma non_cap_exp_set_TLBEntry_asid[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_asid arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_asid_def)

lemma non_cap_exp_set_TLBEntry_g[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_g arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_g_def)

lemma non_cap_exp_set_TLBEntry_valid[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_valid arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_valid_def)

lemma non_cap_exp_set_TLBEntry_caps1[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_caps1 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_caps1_def)

lemma non_cap_exp_set_TLBEntry_capl1[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_capl1 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_capl1_def)

lemma non_cap_exp_set_TLBEntry_pfn1[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_pfn1 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_pfn1_def)

lemma non_cap_exp_set_TLBEntry_c1[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_c1 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_c1_def)

lemma non_cap_exp_set_TLBEntry_d1[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_d1 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_d1_def)

lemma non_cap_exp_set_TLBEntry_v1[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_v1 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_v1_def)

lemma non_cap_exp_set_TLBEntry_caps0[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_caps0 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_caps0_def)

lemma non_cap_exp_set_TLBEntry_capl0[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_capl0 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_capl0_def)

lemma non_cap_exp_set_TLBEntry_pfn0[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_pfn0 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_pfn0_def)

lemma non_cap_exp_set_TLBEntry_c0[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_c0 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_c0_def)

lemma non_cap_exp_set_TLBEntry_d0[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_d0 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_d0_def)

lemma non_cap_exp_set_TLBEntry_v0[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_TLBEntry_v0 arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_TLBEntry_v0_def)

lemma non_cap_exp_undefined_StatusReg[non_cap_expI]:
  "non_cap_exp (undefined_StatusReg arg0)"
  by (non_cap_expI simp: undefined_StatusReg_def)

lemma non_cap_exp_set_StatusReg_bits[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_StatusReg_bits arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_StatusReg_bits_def)

lemma non_cap_exp_set_StatusReg_CU[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_StatusReg_CU arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_StatusReg_CU_def)

lemma non_cap_exp_set_StatusReg_BEV[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_StatusReg_BEV arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_StatusReg_BEV_def)

lemma non_cap_exp_set_StatusReg_IM[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_StatusReg_IM arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_StatusReg_IM_def)

lemma non_cap_exp_set_StatusReg_KX[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_StatusReg_KX arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_StatusReg_KX_def)

lemma non_cap_exp_set_StatusReg_SX[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_StatusReg_SX arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_StatusReg_SX_def)

lemma non_cap_exp_set_StatusReg_UX[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_StatusReg_UX arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_StatusReg_UX_def)

lemma non_cap_exp_set_StatusReg_KSU[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_StatusReg_KSU arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_StatusReg_KSU_def)

lemma non_cap_exp_set_StatusReg_ERL[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_StatusReg_ERL arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_StatusReg_ERL_def)

lemma non_cap_exp_set_StatusReg_EXL[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_StatusReg_EXL arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_StatusReg_EXL_def)

lemma non_cap_exp_set_StatusReg_IE[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_StatusReg_IE arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_StatusReg_IE_def)

lemma non_cap_exp_execute_branch_mips[non_cap_expI]:
  "non_cap_exp (execute_branch_mips arg0)"
  by (non_cap_expI simp: execute_branch_mips_def)

lemma non_cap_exp_rGPR[non_cap_expI]:
  "non_cap_exp (rGPR arg0)"
  by (non_cap_expI simp: rGPR_def)

lemma non_cap_exp_wGPR[non_cap_expI]:
  "non_cap_exp (wGPR arg0 arg1)"
  by (non_cap_expI simp: wGPR_def)

lemma non_cap_exp_MEM_sync[non_cap_expI]:
  "non_cap_exp (MEM_sync arg0)"
  by (non_cap_expI simp: MEM_sync_def)

lemma non_cap_exp_undefined_Exception[non_cap_expI]:
  "non_cap_exp (undefined_Exception arg0)"
  by (non_cap_expI simp: undefined_Exception_def)

lemma non_cap_exp_exceptionVectorOffset[non_cap_expI]:
  "non_cap_exp (exceptionVectorOffset arg0)"
  by (non_cap_expI simp: exceptionVectorOffset_def)

lemma non_cap_exp_exceptionVectorBase[non_cap_expI]:
  "non_cap_exp (exceptionVectorBase arg0)"
  by (non_cap_expI simp: exceptionVectorBase_def)

lemma non_cap_exp_updateBadInstr[non_cap_expI]:
  "non_cap_exp (updateBadInstr arg0)"
  by (non_cap_expI simp: updateBadInstr_def)

lemma non_cap_exp_undefined_Capability[non_cap_expI]:
  "non_cap_exp (undefined_Capability arg0)"
  by (non_cap_expI simp: undefined_Capability_def)

lemma non_cap_exp_undefined_MemAccessType[non_cap_expI]:
  "non_cap_exp (undefined_MemAccessType arg0)"
  by (non_cap_expI simp: undefined_MemAccessType_def)

lemma non_cap_exp_undefined_AccessLevel[non_cap_expI]:
  "non_cap_exp (undefined_AccessLevel arg0)"
  by (non_cap_expI simp: undefined_AccessLevel_def)

lemma non_cap_exp_getAccessLevel[non_cap_expI]:
  "non_cap_exp (getAccessLevel arg0)"
  by (non_cap_expI simp: getAccessLevel_def)

lemma non_cap_exp_undefined_CapCauseReg[non_cap_expI]:
  "non_cap_exp (undefined_CapCauseReg arg0)"
  by (non_cap_expI simp: undefined_CapCauseReg_def)

lemma non_cap_exp_set_CapCauseReg_ExcCode[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_CapCauseReg_ExcCode arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_CapCauseReg_ExcCode_def)

lemma non_cap_exp_set_CapCauseReg_RegNum[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_CapCauseReg_RegNum arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_CapCauseReg_RegNum_def)

lemma non_cap_exp_undefined_decode_failure[non_cap_expI]:
  "non_cap_exp (undefined_decode_failure arg0)"
  by (non_cap_expI simp: undefined_decode_failure_def)

lemma non_cap_exp_undefined_Comparison[non_cap_expI]:
  "non_cap_exp (undefined_Comparison arg0)"
  by (non_cap_expI simp: undefined_Comparison_def)

lemma non_cap_exp_undefined_WordType[non_cap_expI]:
  "non_cap_exp (undefined_WordType arg0)"
  by (non_cap_expI simp: undefined_WordType_def)

lemma non_cap_exp_undefined_WordTypeUnaligned[non_cap_expI]:
  "non_cap_exp (undefined_WordTypeUnaligned arg0)"
  by (non_cap_expI simp: undefined_WordTypeUnaligned_def)

lemma non_cap_exp_init_cp0_state[non_cap_expI]:
  "non_cap_exp (init_cp0_state arg0)"
  by (non_cap_expI simp: init_cp0_state_def)

lemma non_cap_exp_tlbSearch[non_cap_expI]:
  "non_cap_exp (tlbSearch arg0)"
  by (non_cap_expI simp: tlbSearch_def)

lemma non_cap_exp_undefined_CPtrCmpOp[non_cap_expI]:
  "non_cap_exp (undefined_CPtrCmpOp arg0)"
  by (non_cap_expI simp: undefined_CPtrCmpOp_def)

lemma non_cap_exp_undefined_ClearRegSet[non_cap_expI]:
  "non_cap_exp (undefined_ClearRegSet arg0)"
  by (non_cap_expI simp: undefined_ClearRegSet_def)

lemma non_cap_exp_capToString[non_cap_expI]:
  "non_cap_exp (capToString arg0 arg1)"
  by (non_cap_expI simp: capToString_def)

lemma non_cap_exp_undefined_CapEx[non_cap_expI]:
  "non_cap_exp (undefined_CapEx arg0)"
  by (non_cap_expI simp: undefined_CapEx_def)

lemma non_cap_exp_set_CapCauseReg_bits[non_cap_expI]:
  assumes "non_cap_reg arg0"
  shows "non_cap_exp (set_CapCauseReg_bits arg0 arg1)"
  using assms
  by (non_cap_expI simp: set_CapCauseReg_bits_def)

lemma non_cap_exp_execute_XORI[non_cap_expI]:
  "non_cap_exp (execute_XORI arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_XORI_def)

lemma non_cap_exp_execute_XOR[non_cap_expI]:
  "non_cap_exp (execute_XOR arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_XOR_def)

lemma non_cap_exp_execute_SYNC[non_cap_expI]:
  "non_cap_exp (execute_SYNC arg0)"
  by (non_cap_expI simp: execute_SYNC_def)

lemma non_cap_exp_execute_SUBU[non_cap_expI]:
  "non_cap_exp (execute_SUBU arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_SUBU_def)

lemma non_cap_exp_execute_SRLV[non_cap_expI]:
  "non_cap_exp (execute_SRLV arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_SRLV_def)

lemma non_cap_exp_execute_SRL[non_cap_expI]:
  "non_cap_exp (execute_SRL arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_SRL_def)

lemma non_cap_exp_execute_SRAV[non_cap_expI]:
  "non_cap_exp (execute_SRAV arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_SRAV_def)

lemma non_cap_exp_execute_SRA[non_cap_expI]:
  "non_cap_exp (execute_SRA arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_SRA_def)

lemma non_cap_exp_execute_SLTU[non_cap_expI]:
  "non_cap_exp (execute_SLTU arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_SLTU_def)

lemma non_cap_exp_execute_SLTIU[non_cap_expI]:
  "non_cap_exp (execute_SLTIU arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_SLTIU_def)

lemma non_cap_exp_execute_SLTI[non_cap_expI]:
  "non_cap_exp (execute_SLTI arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_SLTI_def)

lemma non_cap_exp_execute_SLT[non_cap_expI]:
  "non_cap_exp (execute_SLT arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_SLT_def)

lemma non_cap_exp_execute_SLLV[non_cap_expI]:
  "non_cap_exp (execute_SLLV arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_SLLV_def)

lemma non_cap_exp_execute_SLL[non_cap_expI]:
  "non_cap_exp (execute_SLL arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_SLL_def)

lemma non_cap_exp_execute_ORI[non_cap_expI]:
  "non_cap_exp (execute_ORI arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_ORI_def)

lemma non_cap_exp_execute_OR[non_cap_expI]:
  "non_cap_exp (execute_OR arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_OR_def)

lemma non_cap_exp_execute_NOR[non_cap_expI]:
  "non_cap_exp (execute_NOR arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_NOR_def)

lemma non_cap_exp_execute_MULTU[non_cap_expI]:
  "non_cap_exp (execute_MULTU arg0 arg1)"
  by (non_cap_expI simp: execute_MULTU_def)

lemma non_cap_exp_execute_MULT[non_cap_expI]:
  "non_cap_exp (execute_MULT arg0 arg1)"
  by (non_cap_expI simp: execute_MULT_def)

lemma non_cap_exp_execute_MUL[non_cap_expI]:
  "non_cap_exp (execute_MUL arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_MUL_def)

lemma non_cap_exp_execute_MTLO[non_cap_expI]:
  "non_cap_exp (execute_MTLO arg0)"
  by (non_cap_expI simp: execute_MTLO_def)

lemma non_cap_exp_execute_MTHI[non_cap_expI]:
  "non_cap_exp (execute_MTHI arg0)"
  by (non_cap_expI simp: execute_MTHI_def)

lemma non_cap_exp_execute_MSUBU[non_cap_expI]:
  "non_cap_exp (execute_MSUBU arg0 arg1)"
  by (non_cap_expI simp: execute_MSUBU_def)

lemma non_cap_exp_execute_MSUB[non_cap_expI]:
  "non_cap_exp (execute_MSUB arg0 arg1)"
  by (non_cap_expI simp: execute_MSUB_def)

lemma non_cap_exp_execute_MOVZ[non_cap_expI]:
  "non_cap_exp (execute_MOVZ arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_MOVZ_def)

lemma non_cap_exp_execute_MOVN[non_cap_expI]:
  "non_cap_exp (execute_MOVN arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_MOVN_def)

lemma non_cap_exp_execute_MFLO[non_cap_expI]:
  "non_cap_exp (execute_MFLO arg0)"
  by (non_cap_expI simp: execute_MFLO_def)

lemma non_cap_exp_execute_MFHI[non_cap_expI]:
  "non_cap_exp (execute_MFHI arg0)"
  by (non_cap_expI simp: execute_MFHI_def)

lemma non_cap_exp_execute_MADDU[non_cap_expI]:
  "non_cap_exp (execute_MADDU arg0 arg1)"
  by (non_cap_expI simp: execute_MADDU_def)

lemma non_cap_exp_execute_MADD[non_cap_expI]:
  "non_cap_exp (execute_MADD arg0 arg1)"
  by (non_cap_expI simp: execute_MADD_def)

lemma non_cap_exp_execute_LUI[non_cap_expI]:
  "non_cap_exp (execute_LUI arg0 arg1)"
  by (non_cap_expI simp: execute_LUI_def)

lemma non_cap_exp_execute_DSUBU[non_cap_expI]:
  "non_cap_exp (execute_DSUBU arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_DSUBU_def)

lemma non_cap_exp_execute_DSRLV[non_cap_expI]:
  "non_cap_exp (execute_DSRLV arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_DSRLV_def)

lemma non_cap_exp_execute_DSRL32[non_cap_expI]:
  "non_cap_exp (execute_DSRL32 arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_DSRL32_def)

lemma non_cap_exp_execute_DSRL[non_cap_expI]:
  "non_cap_exp (execute_DSRL arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_DSRL_def)

lemma non_cap_exp_execute_DSRAV[non_cap_expI]:
  "non_cap_exp (execute_DSRAV arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_DSRAV_def)

lemma non_cap_exp_execute_DSRA32[non_cap_expI]:
  "non_cap_exp (execute_DSRA32 arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_DSRA32_def)

lemma non_cap_exp_execute_DSRA[non_cap_expI]:
  "non_cap_exp (execute_DSRA arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_DSRA_def)

lemma non_cap_exp_execute_DSLLV[non_cap_expI]:
  "non_cap_exp (execute_DSLLV arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_DSLLV_def)

lemma non_cap_exp_execute_DSLL32[non_cap_expI]:
  "non_cap_exp (execute_DSLL32 arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_DSLL32_def)

lemma non_cap_exp_execute_DSLL[non_cap_expI]:
  "non_cap_exp (execute_DSLL arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_DSLL_def)

lemma non_cap_exp_execute_DMULTU[non_cap_expI]:
  "non_cap_exp (execute_DMULTU arg0 arg1)"
  by (non_cap_expI simp: execute_DMULTU_def)

lemma non_cap_exp_execute_DMULT[non_cap_expI]:
  "non_cap_exp (execute_DMULT arg0 arg1)"
  by (non_cap_expI simp: execute_DMULT_def)

lemma non_cap_exp_execute_DIVU[non_cap_expI]:
  "non_cap_exp (execute_DIVU arg0 arg1)"
  by (non_cap_expI simp: execute_DIVU_def)

lemma non_cap_exp_execute_DIV[non_cap_expI]:
  "non_cap_exp (execute_DIV arg0 arg1)"
  by (non_cap_expI simp: execute_DIV_def)

lemma non_cap_exp_execute_DDIVU[non_cap_expI]:
  "non_cap_exp (execute_DDIVU arg0 arg1)"
  by (non_cap_expI simp: execute_DDIVU_def)

lemma non_cap_exp_execute_DDIV[non_cap_expI]:
  "non_cap_exp (execute_DDIV arg0 arg1)"
  by (non_cap_expI simp: execute_DDIV_def)

lemma non_cap_exp_execute_DADDU[non_cap_expI]:
  "non_cap_exp (execute_DADDU arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_DADDU_def)

lemma non_cap_exp_execute_DADDIU[non_cap_expI]:
  "non_cap_exp (execute_DADDIU arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_DADDIU_def)

lemma non_cap_exp_execute_ANDI[non_cap_expI]:
  "non_cap_exp (execute_ANDI arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_ANDI_def)

lemma non_cap_exp_execute_AND[non_cap_expI]:
  "non_cap_exp (execute_AND arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_AND_def)

lemma non_cap_exp_execute_ADDU[non_cap_expI]:
  "non_cap_exp (execute_ADDU arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_ADDU_def)

lemma non_cap_exp_execute_ADDIU[non_cap_expI]:
  "non_cap_exp (execute_ADDIU arg0 arg1 arg2)"
  by (non_cap_expI simp: execute_ADDIU_def)

lemma non_mem_exp_set_CauseReg_bits[non_mem_expI]:
  "non_mem_exp (set_CauseReg_bits arg0 arg1)"
  by (non_mem_expI simp: set_CauseReg_bits_def)

lemma non_mem_exp_set_CauseReg_BD[non_mem_expI]:
  "non_mem_exp (set_CauseReg_BD arg0 arg1)"
  by (non_mem_expI simp: set_CauseReg_BD_def)

lemma non_mem_exp_set_CauseReg_CE[non_mem_expI]:
  "non_mem_exp (set_CauseReg_CE arg0 arg1)"
  by (non_mem_expI simp: set_CauseReg_CE_def)

lemma non_mem_exp_set_CauseReg_IV[non_mem_expI]:
  "non_mem_exp (set_CauseReg_IV arg0 arg1)"
  by (non_mem_expI simp: set_CauseReg_IV_def)

lemma non_mem_exp_set_CauseReg_WP[non_mem_expI]:
  "non_mem_exp (set_CauseReg_WP arg0 arg1)"
  by (non_mem_expI simp: set_CauseReg_WP_def)

lemma non_mem_exp_set_CauseReg_IP[non_mem_expI]:
  "non_mem_exp (set_CauseReg_IP arg0 arg1)"
  by (non_mem_expI simp: set_CauseReg_IP_def)

lemma non_mem_exp_set_CauseReg_ExcCode[non_mem_expI]:
  "non_mem_exp (set_CauseReg_ExcCode arg0 arg1)"
  by (non_mem_expI simp: set_CauseReg_ExcCode_def)

lemma non_mem_exp_set_TLBEntryLoReg_bits[non_mem_expI]:
  "non_mem_exp (set_TLBEntryLoReg_bits arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntryLoReg_bits_def)

lemma non_mem_exp_set_TLBEntryLoReg_CapS[non_mem_expI]:
  "non_mem_exp (set_TLBEntryLoReg_CapS arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntryLoReg_CapS_def)

lemma non_mem_exp_set_TLBEntryLoReg_CapL[non_mem_expI]:
  "non_mem_exp (set_TLBEntryLoReg_CapL arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntryLoReg_CapL_def)

lemma non_mem_exp_set_TLBEntryLoReg_PFN[non_mem_expI]:
  "non_mem_exp (set_TLBEntryLoReg_PFN arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntryLoReg_PFN_def)

lemma non_mem_exp_set_TLBEntryLoReg_C[non_mem_expI]:
  "non_mem_exp (set_TLBEntryLoReg_C arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntryLoReg_C_def)

lemma non_mem_exp_set_TLBEntryLoReg_D[non_mem_expI]:
  "non_mem_exp (set_TLBEntryLoReg_D arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntryLoReg_D_def)

lemma non_mem_exp_set_TLBEntryLoReg_V[non_mem_expI]:
  "non_mem_exp (set_TLBEntryLoReg_V arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntryLoReg_V_def)

lemma non_mem_exp_set_TLBEntryLoReg_G[non_mem_expI]:
  "non_mem_exp (set_TLBEntryLoReg_G arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntryLoReg_G_def)

lemma non_mem_exp_set_TLBEntryHiReg_bits[non_mem_expI]:
  "non_mem_exp (set_TLBEntryHiReg_bits arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntryHiReg_bits_def)

lemma non_mem_exp_set_TLBEntryHiReg_R[non_mem_expI]:
  "non_mem_exp (set_TLBEntryHiReg_R arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntryHiReg_R_def)

lemma non_mem_exp_set_TLBEntryHiReg_VPN2[non_mem_expI]:
  "non_mem_exp (set_TLBEntryHiReg_VPN2 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntryHiReg_VPN2_def)

lemma non_mem_exp_set_TLBEntryHiReg_ASID[non_mem_expI]:
  "non_mem_exp (set_TLBEntryHiReg_ASID arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntryHiReg_ASID_def)

lemma non_mem_exp_set_ContextReg_bits[non_mem_expI]:
  "non_mem_exp (set_ContextReg_bits arg0 arg1)"
  by (non_mem_expI simp: set_ContextReg_bits_def)

lemma non_mem_exp_set_ContextReg_PTEBase[non_mem_expI]:
  "non_mem_exp (set_ContextReg_PTEBase arg0 arg1)"
  by (non_mem_expI simp: set_ContextReg_PTEBase_def)

lemma non_mem_exp_set_ContextReg_BadVPN2[non_mem_expI]:
  "non_mem_exp (set_ContextReg_BadVPN2 arg0 arg1)"
  by (non_mem_expI simp: set_ContextReg_BadVPN2_def)

lemma non_mem_exp_set_XContextReg_bits[non_mem_expI]:
  "non_mem_exp (set_XContextReg_bits arg0 arg1)"
  by (non_mem_expI simp: set_XContextReg_bits_def)

lemma non_mem_exp_set_XContextReg_XPTEBase[non_mem_expI]:
  "non_mem_exp (set_XContextReg_XPTEBase arg0 arg1)"
  by (non_mem_expI simp: set_XContextReg_XPTEBase_def)

lemma non_mem_exp_set_XContextReg_XR[non_mem_expI]:
  "non_mem_exp (set_XContextReg_XR arg0 arg1)"
  by (non_mem_expI simp: set_XContextReg_XR_def)

lemma non_mem_exp_set_XContextReg_XBadVPN2[non_mem_expI]:
  "non_mem_exp (set_XContextReg_XBadVPN2 arg0 arg1)"
  by (non_mem_expI simp: set_XContextReg_XBadVPN2_def)

lemma non_mem_exp_set_TLBEntry_bits[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_bits arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_bits_def)

lemma non_mem_exp_set_TLBEntry_pagemask[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_pagemask arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_pagemask_def)

lemma non_mem_exp_set_TLBEntry_r[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_r arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_r_def)

lemma non_mem_exp_set_TLBEntry_vpn2[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_vpn2 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_vpn2_def)

lemma non_mem_exp_set_TLBEntry_asid[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_asid arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_asid_def)

lemma non_mem_exp_set_TLBEntry_g[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_g arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_g_def)

lemma non_mem_exp_set_TLBEntry_valid[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_valid arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_valid_def)

lemma non_mem_exp_set_TLBEntry_caps1[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_caps1 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_caps1_def)

lemma non_mem_exp_set_TLBEntry_capl1[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_capl1 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_capl1_def)

lemma non_mem_exp_set_TLBEntry_pfn1[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_pfn1 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_pfn1_def)

lemma non_mem_exp_set_TLBEntry_c1[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_c1 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_c1_def)

lemma non_mem_exp_set_TLBEntry_d1[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_d1 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_d1_def)

lemma non_mem_exp_set_TLBEntry_v1[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_v1 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_v1_def)

lemma non_mem_exp_set_TLBEntry_caps0[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_caps0 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_caps0_def)

lemma non_mem_exp_set_TLBEntry_capl0[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_capl0 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_capl0_def)

lemma non_mem_exp_set_TLBEntry_pfn0[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_pfn0 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_pfn0_def)

lemma non_mem_exp_set_TLBEntry_c0[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_c0 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_c0_def)

lemma non_mem_exp_set_TLBEntry_d0[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_d0 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_d0_def)

lemma non_mem_exp_set_TLBEntry_v0[non_mem_expI]:
  "non_mem_exp (set_TLBEntry_v0 arg0 arg1)"
  by (non_mem_expI simp: set_TLBEntry_v0_def)

lemma non_mem_exp_set_StatusReg_bits[non_mem_expI]:
  "non_mem_exp (set_StatusReg_bits arg0 arg1)"
  by (non_mem_expI simp: set_StatusReg_bits_def)

lemma non_mem_exp_set_StatusReg_CU[non_mem_expI]:
  "non_mem_exp (set_StatusReg_CU arg0 arg1)"
  by (non_mem_expI simp: set_StatusReg_CU_def)

lemma non_mem_exp_set_StatusReg_BEV[non_mem_expI]:
  "non_mem_exp (set_StatusReg_BEV arg0 arg1)"
  by (non_mem_expI simp: set_StatusReg_BEV_def)

lemma non_mem_exp_set_StatusReg_IM[non_mem_expI]:
  "non_mem_exp (set_StatusReg_IM arg0 arg1)"
  by (non_mem_expI simp: set_StatusReg_IM_def)

lemma non_mem_exp_set_StatusReg_KX[non_mem_expI]:
  "non_mem_exp (set_StatusReg_KX arg0 arg1)"
  by (non_mem_expI simp: set_StatusReg_KX_def)

lemma non_mem_exp_set_StatusReg_SX[non_mem_expI]:
  "non_mem_exp (set_StatusReg_SX arg0 arg1)"
  by (non_mem_expI simp: set_StatusReg_SX_def)

lemma non_mem_exp_set_StatusReg_UX[non_mem_expI]:
  "non_mem_exp (set_StatusReg_UX arg0 arg1)"
  by (non_mem_expI simp: set_StatusReg_UX_def)

lemma non_mem_exp_set_StatusReg_KSU[non_mem_expI]:
  "non_mem_exp (set_StatusReg_KSU arg0 arg1)"
  by (non_mem_expI simp: set_StatusReg_KSU_def)

lemma non_mem_exp_set_StatusReg_ERL[non_mem_expI]:
  "non_mem_exp (set_StatusReg_ERL arg0 arg1)"
  by (non_mem_expI simp: set_StatusReg_ERL_def)

lemma non_mem_exp_set_StatusReg_EXL[non_mem_expI]:
  "non_mem_exp (set_StatusReg_EXL arg0 arg1)"
  by (non_mem_expI simp: set_StatusReg_EXL_def)

lemma non_mem_exp_set_StatusReg_IE[non_mem_expI]:
  "non_mem_exp (set_StatusReg_IE arg0 arg1)"
  by (non_mem_expI simp: set_StatusReg_IE_def)

lemma non_mem_exp_set_CapCauseReg_ExcCode[non_mem_expI]:
  "non_mem_exp (set_CapCauseReg_ExcCode arg0 arg1)"
  by (non_mem_expI simp: set_CapCauseReg_ExcCode_def)

lemma non_mem_exp_set_CapCauseReg_RegNum[non_mem_expI]:
  "non_mem_exp (set_CapCauseReg_RegNum arg0 arg1)"
  by (non_mem_expI simp: set_CapCauseReg_RegNum_def)

lemma non_mem_exp_set_next_pcc[non_mem_expI]:
  "non_mem_exp (set_next_pcc arg0)"
  by (non_mem_expI simp: set_next_pcc_def)

lemma non_mem_exp_SignalException[non_mem_expI]:
  "non_mem_exp (SignalException arg0)"
  by (non_mem_expI simp: SignalException_def)

lemma non_mem_exp_SignalExceptionBadAddr[non_mem_expI]:
  "non_mem_exp (SignalExceptionBadAddr arg0 arg1)"
  by (non_mem_expI simp: SignalExceptionBadAddr_def)

lemma non_mem_exp_SignalExceptionTLB[non_mem_expI]:
  "non_mem_exp (SignalExceptionTLB arg0 arg1)"
  by (non_mem_expI simp: SignalExceptionTLB_def)

lemma non_mem_exp_pcc_access_system_regs[non_mem_expI]:
  "non_mem_exp (pcc_access_system_regs arg0)"
  by (non_mem_expI simp: pcc_access_system_regs_def)

lemma non_mem_exp_raise_c2_exception8[non_mem_expI]:
  "non_mem_exp (raise_c2_exception8 arg0 arg1)"
  by (non_mem_expI simp: raise_c2_exception8_def)

lemma non_mem_exp_raise_c2_exception_noreg[non_mem_expI]:
  "non_mem_exp (raise_c2_exception_noreg arg0)"
  by (non_mem_expI simp: raise_c2_exception_noreg_def)

lemma non_mem_exp_checkCP0AccessHook[non_mem_expI]:
  "non_mem_exp (checkCP0AccessHook arg0)"
  by (non_mem_expI simp: checkCP0AccessHook_def)

lemma non_mem_exp_checkCP0Access[non_mem_expI]:
  "non_mem_exp (checkCP0Access arg0)"
  by (non_mem_expI simp: checkCP0Access_def)

lemma non_mem_exp_incrementCP0Count[non_mem_expI]:
  "non_mem_exp (incrementCP0Count arg0)"
  by (non_mem_expI simp: incrementCP0Count_def)

lemma non_mem_exp_TLBTranslate2[non_mem_expI]:
  "non_mem_exp (TLBTranslate2 arg0 arg1)"
  by (non_mem_expI simp: TLBTranslate2_def)

lemma non_mem_exp_TLBTranslateC[non_mem_expI]:
  "non_mem_exp (TLBTranslateC arg0 arg1)"
  by (non_mem_expI simp: TLBTranslateC_def)

lemma non_mem_exp_TLBTranslate[non_mem_expI]:
  "non_mem_exp (TLBTranslate arg0 arg1)"
  by (non_mem_expI simp: TLBTranslate_def)

lemma non_mem_exp_execute_branch_pcc[non_mem_expI]:
  "non_mem_exp (execute_branch_pcc arg0)"
  by (non_mem_expI simp: execute_branch_pcc_def)

lemma non_mem_exp_ERETHook[non_mem_expI]:
  "non_mem_exp (ERETHook arg0)"
  by (non_mem_expI simp: ERETHook_def)

lemma non_mem_exp_raise_c2_exception[non_mem_expI]:
  "non_mem_exp (raise_c2_exception arg0 arg1)"
  by (non_mem_expI simp: raise_c2_exception_def)

lemma non_mem_exp_checkDDCPerms[non_mem_expI]:
  "non_mem_exp (checkDDCPerms arg0 arg1)"
  by (non_mem_expI simp: checkDDCPerms_def)

lemma non_mem_exp_addrWrapper[non_mem_expI]:
  "non_mem_exp (addrWrapper arg0 arg1 arg2)"
  by (non_mem_expI simp: addrWrapper_def)

lemma non_mem_exp_addrWrapperUnaligned[non_mem_expI]:
  "non_mem_exp (addrWrapperUnaligned arg0 arg1 arg2)"
  by (non_mem_expI simp: addrWrapperUnaligned_def)

lemma non_mem_exp_execute_branch[non_mem_expI]:
  "non_mem_exp (execute_branch arg0)"
  by (non_mem_expI simp: execute_branch_def)

lemma non_mem_exp_TranslatePC[non_mem_expI]:
  "non_mem_exp (TranslatePC arg0)"
  by (non_mem_expI simp: TranslatePC_def)

lemma non_mem_exp_checkCP2usable[non_mem_expI]:
  "non_mem_exp (checkCP2usable arg0)"
  by (non_mem_expI simp: checkCP2usable_def)

lemma non_mem_exp_get_CP0EPC[non_mem_expI]:
  "non_mem_exp (get_CP0EPC arg0)"
  by (non_mem_expI simp: get_CP0EPC_def)

lemma non_mem_exp_set_CP0EPC[non_mem_expI]:
  "non_mem_exp (set_CP0EPC arg0)"
  by (non_mem_expI simp: set_CP0EPC_def)

lemma non_mem_exp_get_CP0ErrorEPC[non_mem_expI]:
  "non_mem_exp (get_CP0ErrorEPC arg0)"
  by (non_mem_expI simp: get_CP0ErrorEPC_def)

lemma non_mem_exp_set_CP0ErrorEPC[non_mem_expI]:
  "non_mem_exp (set_CP0ErrorEPC arg0)"
  by (non_mem_expI simp: set_CP0ErrorEPC_def)

lemma non_mem_exp_dump_cp2_state[non_mem_expI]:
  "non_mem_exp (dump_cp2_state arg0)"
  by (non_mem_expI simp: dump_cp2_state_def)

lemma non_mem_exp_TLBWriteEntry[non_mem_expI]:
  "non_mem_exp (TLBWriteEntry arg0)"
  by (non_mem_expI simp: TLBWriteEntry_def)

lemma non_mem_exp_execute_WAIT[non_mem_expI]:
  "non_mem_exp (execute_WAIT arg0)"
  by (non_mem_expI simp: execute_WAIT_def)

lemma non_mem_exp_execute_TRAPREG[non_mem_expI]:
  "non_mem_exp (execute_TRAPREG arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_TRAPREG_def)

lemma non_mem_exp_execute_TRAPIMM[non_mem_expI]:
  "non_mem_exp (execute_TRAPIMM arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_TRAPIMM_def)

lemma non_mem_exp_execute_TLBWR[non_mem_expI]:
  "non_mem_exp (execute_TLBWR arg0)"
  by (non_mem_expI simp: execute_TLBWR_def)

lemma non_mem_exp_execute_TLBWI[non_mem_expI]:
  "non_mem_exp (execute_TLBWI arg0)"
  by (non_mem_expI simp: execute_TLBWI_def)

lemma non_mem_exp_execute_TLBR[non_mem_expI]:
  "non_mem_exp (execute_TLBR arg0)"
  by (non_mem_expI simp: execute_TLBR_def)

lemma non_mem_exp_execute_TLBP[non_mem_expI]:
  "non_mem_exp (execute_TLBP arg0)"
  by (non_mem_expI simp: execute_TLBP_def)

lemma non_mem_exp_execute_SYSCALL[non_mem_expI]:
  "non_mem_exp (execute_SYSCALL arg0)"
  by (non_mem_expI simp: execute_SYSCALL_def)

lemma non_mem_exp_execute_SUB[non_mem_expI]:
  "non_mem_exp (execute_SUB arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_SUB_def)

lemma non_mem_exp_execute_RI[non_mem_expI]:
  "non_mem_exp (execute_RI arg0)"
  by (non_mem_expI simp: execute_RI_def)

lemma non_mem_exp_execute_RDHWR[non_mem_expI]:
  "non_mem_exp (execute_RDHWR arg0 arg1)"
  by (non_mem_expI simp: execute_RDHWR_def)

lemma non_mem_exp_execute_MTC0[non_mem_expI]:
  "non_mem_exp (execute_MTC0 arg0 arg1 arg2 arg3)"
  by (non_mem_expI simp: execute_MTC0_def)

lemma non_mem_exp_execute_MFC0[non_mem_expI]:
  "non_mem_exp (execute_MFC0 arg0 arg1 arg2 arg3)"
  by (non_mem_expI simp: execute_MFC0_def)

lemma non_mem_exp_execute_JR[non_mem_expI]:
  "non_mem_exp (execute_JR arg0)"
  by (non_mem_expI simp: execute_JR_def)

lemma non_mem_exp_execute_JALR[non_mem_expI]:
  "non_mem_exp (execute_JALR arg0 arg1)"
  by (non_mem_expI simp: execute_JALR_def)

lemma non_mem_exp_execute_JAL[non_mem_expI]:
  "non_mem_exp (execute_JAL arg0)"
  by (non_mem_expI simp: execute_JAL_def)

lemma non_mem_exp_execute_J[non_mem_expI]:
  "non_mem_exp (execute_J arg0)"
  by (non_mem_expI simp: execute_J_def)

lemma non_mem_exp_execute_ERET[non_mem_expI]:
  "non_mem_exp (execute_ERET arg0)"
  by (non_mem_expI simp: execute_ERET_def)

lemma non_mem_exp_execute_DSUB[non_mem_expI]:
  "non_mem_exp (execute_DSUB arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_DSUB_def)

lemma non_mem_exp_execute_DADDI[non_mem_expI]:
  "non_mem_exp (execute_DADDI arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_DADDI_def)

lemma non_mem_exp_execute_DADD[non_mem_expI]:
  "non_mem_exp (execute_DADD arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_DADD_def)

lemma non_mem_exp_execute_ClearRegs[non_mem_expI]:
  "non_mem_exp (execute_ClearRegs arg0 arg1)"
  by (non_mem_expI simp: execute_ClearRegs_def)

lemma non_mem_exp_execute_CWriteHwr[non_mem_expI]:
  "non_mem_exp (execute_CWriteHwr arg0 arg1)"
  by (non_mem_expI simp: execute_CWriteHwr_def)

lemma non_mem_exp_execute_CUnseal[non_mem_expI]:
  "non_mem_exp (execute_CUnseal arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CUnseal_def)

lemma non_mem_exp_execute_CToPtr[non_mem_expI]:
  "non_mem_exp (execute_CToPtr arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CToPtr_def)

lemma non_mem_exp_execute_CTestSubset[non_mem_expI]:
  "non_mem_exp (execute_CTestSubset arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CTestSubset_def)

lemma non_mem_exp_execute_CSub[non_mem_expI]:
  "non_mem_exp (execute_CSub arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CSub_def)

lemma non_mem_exp_execute_CSetOffset[non_mem_expI]:
  "non_mem_exp (execute_CSetOffset arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CSetOffset_def)

lemma non_mem_exp_execute_CSetFlags[non_mem_expI]:
  "non_mem_exp (execute_CSetFlags arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CSetFlags_def)

lemma non_mem_exp_execute_CSetCause[non_mem_expI]:
  "non_mem_exp (execute_CSetCause arg0)"
  by (non_mem_expI simp: execute_CSetCause_def)

lemma non_mem_exp_execute_CSetCID[non_mem_expI]:
  "non_mem_exp (execute_CSetCID arg0)"
  by (non_mem_expI simp: execute_CSetCID_def)

lemma non_mem_exp_execute_CSetBoundsImmediate[non_mem_expI]:
  "non_mem_exp (execute_CSetBoundsImmediate arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CSetBoundsImmediate_def)

lemma non_mem_exp_execute_CSetBoundsExact[non_mem_expI]:
  "non_mem_exp (execute_CSetBoundsExact arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CSetBoundsExact_def)

lemma non_mem_exp_execute_CSetBounds[non_mem_expI]:
  "non_mem_exp (execute_CSetBounds arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CSetBounds_def)

lemma non_mem_exp_execute_CSetAddr[non_mem_expI]:
  "non_mem_exp (execute_CSetAddr arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CSetAddr_def)

lemma non_mem_exp_execute_CSeal[non_mem_expI]:
  "non_mem_exp (execute_CSeal arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CSeal_def)

lemma non_mem_exp_execute_CReturn[non_mem_expI]:
  "non_mem_exp (execute_CReturn arg0)"
  by (non_mem_expI simp: execute_CReturn_def)

lemma non_mem_exp_execute_CReadHwr[non_mem_expI]:
  "non_mem_exp (execute_CReadHwr arg0 arg1)"
  by (non_mem_expI simp: execute_CReadHwr_def)

lemma non_mem_exp_execute_CRAP[non_mem_expI]:
  "non_mem_exp (execute_CRAP arg0 arg1)"
  by (non_mem_expI simp: execute_CRAP_def)

lemma non_mem_exp_execute_CRAM[non_mem_expI]:
  "non_mem_exp (execute_CRAM arg0 arg1)"
  by (non_mem_expI simp: execute_CRAM_def)

lemma non_mem_exp_execute_CPtrCmp[non_mem_expI]:
  "non_mem_exp (execute_CPtrCmp arg0 arg1 arg2 arg3)"
  by (non_mem_expI simp: execute_CPtrCmp_def)

lemma non_mem_exp_execute_CMove[non_mem_expI]:
  "non_mem_exp (execute_CMove arg0 arg1)"
  by (non_mem_expI simp: execute_CMove_def)

lemma non_mem_exp_execute_CMOVX[non_mem_expI]:
  "non_mem_exp (execute_CMOVX arg0 arg1 arg2 arg3)"
  by (non_mem_expI simp: execute_CMOVX_def)

lemma non_mem_exp_execute_CJALR[non_mem_expI]:
  "non_mem_exp (execute_CJALR arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CJALR_def)

lemma non_mem_exp_execute_CIncOffsetImmediate[non_mem_expI]:
  "non_mem_exp (execute_CIncOffsetImmediate arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CIncOffsetImmediate_def)

lemma non_mem_exp_execute_CIncOffset[non_mem_expI]:
  "non_mem_exp (execute_CIncOffset arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CIncOffset_def)

lemma non_mem_exp_execute_CGetType[non_mem_expI]:
  "non_mem_exp (execute_CGetType arg0 arg1)"
  by (non_mem_expI simp: execute_CGetType_def)

lemma non_mem_exp_execute_CGetTag[non_mem_expI]:
  "non_mem_exp (execute_CGetTag arg0 arg1)"
  by (non_mem_expI simp: execute_CGetTag_def)

lemma non_mem_exp_execute_CGetSealed[non_mem_expI]:
  "non_mem_exp (execute_CGetSealed arg0 arg1)"
  by (non_mem_expI simp: execute_CGetSealed_def)

lemma non_mem_exp_execute_CGetPerm[non_mem_expI]:
  "non_mem_exp (execute_CGetPerm arg0 arg1)"
  by (non_mem_expI simp: execute_CGetPerm_def)

lemma non_mem_exp_execute_CGetPCCSetOffset[non_mem_expI]:
  "non_mem_exp (execute_CGetPCCSetOffset arg0 arg1)"
  by (non_mem_expI simp: execute_CGetPCCSetOffset_def)

lemma non_mem_exp_execute_CGetPCC[non_mem_expI]:
  "non_mem_exp (execute_CGetPCC arg0)"
  by (non_mem_expI simp: execute_CGetPCC_def)

lemma non_mem_exp_execute_CGetOffset[non_mem_expI]:
  "non_mem_exp (execute_CGetOffset arg0 arg1)"
  by (non_mem_expI simp: execute_CGetOffset_def)

lemma non_mem_exp_execute_CGetLen[non_mem_expI]:
  "non_mem_exp (execute_CGetLen arg0 arg1)"
  by (non_mem_expI simp: execute_CGetLen_def)

lemma non_mem_exp_execute_CGetFlags[non_mem_expI]:
  "non_mem_exp (execute_CGetFlags arg0 arg1)"
  by (non_mem_expI simp: execute_CGetFlags_def)

lemma non_mem_exp_execute_CGetCause[non_mem_expI]:
  "non_mem_exp (execute_CGetCause arg0)"
  by (non_mem_expI simp: execute_CGetCause_def)

lemma non_mem_exp_execute_CGetCID[non_mem_expI]:
  "non_mem_exp (execute_CGetCID arg0)"
  by (non_mem_expI simp: execute_CGetCID_def)

lemma non_mem_exp_execute_CGetBase[non_mem_expI]:
  "non_mem_exp (execute_CGetBase arg0 arg1)"
  by (non_mem_expI simp: execute_CGetBase_def)

lemma non_mem_exp_execute_CGetAndAddr[non_mem_expI]:
  "non_mem_exp (execute_CGetAndAddr arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CGetAndAddr_def)

lemma non_mem_exp_execute_CGetAddr[non_mem_expI]:
  "non_mem_exp (execute_CGetAddr arg0 arg1)"
  by (non_mem_expI simp: execute_CGetAddr_def)

lemma non_mem_exp_execute_CFromPtr[non_mem_expI]:
  "non_mem_exp (execute_CFromPtr arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CFromPtr_def)

lemma non_mem_exp_execute_CCopyType[non_mem_expI]:
  "non_mem_exp (execute_CCopyType arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CCopyType_def)

lemma non_mem_exp_execute_CClearTag[non_mem_expI]:
  "non_mem_exp (execute_CClearTag arg0 arg1)"
  by (non_mem_expI simp: execute_CClearTag_def)

lemma non_mem_exp_execute_CCheckType[non_mem_expI]:
  "non_mem_exp (execute_CCheckType arg0 arg1)"
  by (non_mem_expI simp: execute_CCheckType_def)

lemma non_mem_exp_execute_CCheckTag[non_mem_expI]:
  "non_mem_exp (execute_CCheckTag arg0)"
  by (non_mem_expI simp: execute_CCheckTag_def)

lemma non_mem_exp_execute_CCheckPerm[non_mem_expI]:
  "non_mem_exp (execute_CCheckPerm arg0 arg1)"
  by (non_mem_expI simp: execute_CCheckPerm_def)

lemma non_mem_exp_execute_CCall[non_mem_expI]:
  "non_mem_exp (execute_CCall arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CCall_def)

lemma non_mem_exp_execute_CCSeal[non_mem_expI]:
  "non_mem_exp (execute_CCSeal arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CCSeal_def)

lemma non_mem_exp_execute_CBuildCap[non_mem_expI]:
  "non_mem_exp (execute_CBuildCap arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CBuildCap_def)

lemma non_mem_exp_execute_CBZ[non_mem_expI]:
  "non_mem_exp (execute_CBZ arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CBZ_def)

lemma non_mem_exp_execute_CBX[non_mem_expI]:
  "non_mem_exp (execute_CBX arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CBX_def)

lemma non_mem_exp_execute_CAndPerm[non_mem_expI]:
  "non_mem_exp (execute_CAndPerm arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CAndPerm_def)

lemma non_mem_exp_execute_CAndAddr[non_mem_expI]:
  "non_mem_exp (execute_CAndAddr arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CAndAddr_def)

lemma non_mem_exp_execute_CACHE[non_mem_expI]:
  "non_mem_exp (execute_CACHE arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_CACHE_def)

lemma non_mem_exp_execute_BREAK[non_mem_expI]:
  "non_mem_exp (execute_BREAK arg0)"
  by (non_mem_expI simp: execute_BREAK_def)

lemma non_mem_exp_execute_BEQ[non_mem_expI]:
  "non_mem_exp (execute_BEQ arg0 arg1 arg2 arg3 arg4)"
  by (non_mem_expI simp: execute_BEQ_def)

lemma non_mem_exp_execute_BCMPZ[non_mem_expI]:
  "non_mem_exp (execute_BCMPZ arg0 arg1 arg2 arg3 arg4)"
  by (non_mem_expI simp: execute_BCMPZ_def)

lemma non_mem_exp_execute_ADDI[non_mem_expI]:
  "non_mem_exp (execute_ADDI arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_ADDI_def)

lemma non_mem_exp_execute_ADD[non_mem_expI]:
  "non_mem_exp (execute_ADD arg0 arg1 arg2)"
  by (non_mem_expI simp: execute_ADD_def)

lemma no_reg_writes_to_undefined_option[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_option arg0)"
  unfolding undefined_option_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MIPS_write[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MIPS_write arg0 arg1 arg2)"
  unfolding MIPS_write_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MIPS_read[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MIPS_read arg0 arg1)"
  unfolding MIPS_read_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_exception[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_exception arg0)"
  unfolding undefined_exception_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_CauseReg[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_CauseReg arg0)"
  unfolding undefined_CauseReg_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_CauseReg_bits[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_CauseReg_bits arg0 arg1)"
  using assms
  unfolding set_CauseReg_bits_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_CauseReg_BD[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_CauseReg_BD arg0 arg1)"
  using assms
  unfolding set_CauseReg_BD_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_CauseReg_CE[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_CauseReg_CE arg0 arg1)"
  using assms
  unfolding set_CauseReg_CE_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_CauseReg_IV[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_CauseReg_IV arg0 arg1)"
  using assms
  unfolding set_CauseReg_IV_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_CauseReg_WP[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_CauseReg_WP arg0 arg1)"
  using assms
  unfolding set_CauseReg_WP_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_CauseReg_IP[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_CauseReg_IP arg0 arg1)"
  using assms
  unfolding set_CauseReg_IP_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_CauseReg_ExcCode[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_CauseReg_ExcCode arg0 arg1)"
  using assms
  unfolding set_CauseReg_ExcCode_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_TLBEntryLoReg[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_TLBEntryLoReg arg0)"
  unfolding undefined_TLBEntryLoReg_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntryLoReg_bits[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntryLoReg_bits arg0 arg1)"
  using assms
  unfolding set_TLBEntryLoReg_bits_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntryLoReg_CapS[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntryLoReg_CapS arg0 arg1)"
  using assms
  unfolding set_TLBEntryLoReg_CapS_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntryLoReg_CapL[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntryLoReg_CapL arg0 arg1)"
  using assms
  unfolding set_TLBEntryLoReg_CapL_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntryLoReg_PFN[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntryLoReg_PFN arg0 arg1)"
  using assms
  unfolding set_TLBEntryLoReg_PFN_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntryLoReg_C[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntryLoReg_C arg0 arg1)"
  using assms
  unfolding set_TLBEntryLoReg_C_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntryLoReg_D[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntryLoReg_D arg0 arg1)"
  using assms
  unfolding set_TLBEntryLoReg_D_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntryLoReg_V[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntryLoReg_V arg0 arg1)"
  using assms
  unfolding set_TLBEntryLoReg_V_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntryLoReg_G[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntryLoReg_G arg0 arg1)"
  using assms
  unfolding set_TLBEntryLoReg_G_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_TLBEntryHiReg[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_TLBEntryHiReg arg0)"
  unfolding undefined_TLBEntryHiReg_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntryHiReg_bits[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntryHiReg_bits arg0 arg1)"
  using assms
  unfolding set_TLBEntryHiReg_bits_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntryHiReg_R[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntryHiReg_R arg0 arg1)"
  using assms
  unfolding set_TLBEntryHiReg_R_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntryHiReg_VPN2[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntryHiReg_VPN2 arg0 arg1)"
  using assms
  unfolding set_TLBEntryHiReg_VPN2_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntryHiReg_ASID[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntryHiReg_ASID arg0 arg1)"
  using assms
  unfolding set_TLBEntryHiReg_ASID_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_ContextReg[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_ContextReg arg0)"
  unfolding undefined_ContextReg_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_ContextReg_bits[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_ContextReg_bits arg0 arg1)"
  using assms
  unfolding set_ContextReg_bits_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_ContextReg_PTEBase[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_ContextReg_PTEBase arg0 arg1)"
  using assms
  unfolding set_ContextReg_PTEBase_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_ContextReg_BadVPN2[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_ContextReg_BadVPN2 arg0 arg1)"
  using assms
  unfolding set_ContextReg_BadVPN2_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_XContextReg[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_XContextReg arg0)"
  unfolding undefined_XContextReg_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_XContextReg_bits[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_XContextReg_bits arg0 arg1)"
  using assms
  unfolding set_XContextReg_bits_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_XContextReg_XPTEBase[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_XContextReg_XPTEBase arg0 arg1)"
  using assms
  unfolding set_XContextReg_XPTEBase_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_XContextReg_XR[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_XContextReg_XR arg0 arg1)"
  using assms
  unfolding set_XContextReg_XR_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_XContextReg_XBadVPN2[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_XContextReg_XBadVPN2 arg0 arg1)"
  using assms
  unfolding set_XContextReg_XBadVPN2_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_TLBEntry[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_TLBEntry arg0)"
  unfolding undefined_TLBEntry_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_bits[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_bits arg0 arg1)"
  using assms
  unfolding set_TLBEntry_bits_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_pagemask[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_pagemask arg0 arg1)"
  using assms
  unfolding set_TLBEntry_pagemask_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_r[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_r arg0 arg1)"
  using assms
  unfolding set_TLBEntry_r_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_vpn2[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_vpn2 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_vpn2_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_asid[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_asid arg0 arg1)"
  using assms
  unfolding set_TLBEntry_asid_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_g[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_g arg0 arg1)"
  using assms
  unfolding set_TLBEntry_g_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_valid[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_valid arg0 arg1)"
  using assms
  unfolding set_TLBEntry_valid_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_caps1[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_caps1 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_caps1_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_capl1[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_capl1 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_capl1_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_pfn1[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_pfn1 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_pfn1_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_c1[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_c1 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_c1_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_d1[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_d1 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_d1_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_v1[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_v1 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_v1_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_caps0[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_caps0 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_caps0_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_capl0[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_capl0 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_capl0_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_pfn0[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_pfn0 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_pfn0_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_c0[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_c0 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_c0_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_d0[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_d0 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_d0_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_TLBEntry_v0[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_TLBEntry_v0 arg0 arg1)"
  using assms
  unfolding set_TLBEntry_v0_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_StatusReg[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_StatusReg arg0)"
  unfolding undefined_StatusReg_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_StatusReg_bits[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_StatusReg_bits arg0 arg1)"
  using assms
  unfolding set_StatusReg_bits_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_StatusReg_CU[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_StatusReg_CU arg0 arg1)"
  using assms
  unfolding set_StatusReg_CU_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_StatusReg_BEV[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_StatusReg_BEV arg0 arg1)"
  using assms
  unfolding set_StatusReg_BEV_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_StatusReg_IM[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_StatusReg_IM arg0 arg1)"
  using assms
  unfolding set_StatusReg_IM_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_StatusReg_KX[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_StatusReg_KX arg0 arg1)"
  using assms
  unfolding set_StatusReg_KX_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_StatusReg_SX[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_StatusReg_SX arg0 arg1)"
  using assms
  unfolding set_StatusReg_SX_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_StatusReg_UX[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_StatusReg_UX arg0 arg1)"
  using assms
  unfolding set_StatusReg_UX_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_StatusReg_KSU[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_StatusReg_KSU arg0 arg1)"
  using assms
  unfolding set_StatusReg_KSU_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_StatusReg_ERL[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_StatusReg_ERL arg0 arg1)"
  using assms
  unfolding set_StatusReg_ERL_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_StatusReg_EXL[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_StatusReg_EXL arg0 arg1)"
  using assms
  unfolding set_StatusReg_EXL_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_StatusReg_IE[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_StatusReg_IE arg0 arg1)"
  using assms
  unfolding set_StatusReg_IE_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_execute_branch_mips[no_reg_writes_toI, simp]:
  assumes "{''BranchPending'', ''DelayedPC'', ''NextInBranchDelay''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (execute_branch_mips arg0)"
  using assms
  unfolding execute_branch_mips_def bind_assoc
  by (no_reg_writes_toI simp: BranchPending_ref_def DelayedPC_ref_def NextInBranchDelay_ref_def)

lemma no_reg_writes_to_rGPR[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (rGPR arg0)"
  unfolding rGPR_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_wGPR[no_reg_writes_toI, simp]:
  assumes "{''GPR''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (wGPR arg0 arg1)"
  using assms
  unfolding wGPR_def bind_assoc
  by (no_reg_writes_toI simp: GPR_ref_def)

lemma no_reg_writes_to_MEMr[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMr arg0 arg1)"
  unfolding MEMr_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MEMr_reserve[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMr_reserve arg0 arg1)"
  unfolding MEMr_reserve_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MEM_sync[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEM_sync arg0)"
  unfolding MEM_sync_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MEMea[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMea arg0 arg1)"
  unfolding MEMea_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MEMea_conditional[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMea_conditional arg0 arg1)"
  unfolding MEMea_conditional_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MEMval[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMval arg0 arg1 arg2)"
  unfolding MEMval_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MEMval_conditional[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMval_conditional arg0 arg1 arg2)"
  unfolding MEMval_conditional_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_Exception[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_Exception arg0)"
  unfolding undefined_Exception_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_exceptionVectorOffset[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (exceptionVectorOffset arg0)"
  unfolding exceptionVectorOffset_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_exceptionVectorBase[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (exceptionVectorBase arg0)"
  unfolding exceptionVectorBase_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_updateBadInstr[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (updateBadInstr arg0)"
  using assms
  unfolding updateBadInstr_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def)

lemma no_reg_writes_to_undefined_Capability[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_Capability arg0)"
  unfolding undefined_Capability_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_next_pcc[no_reg_writes_toI, simp]:
  assumes "{''DelayedPCC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (set_next_pcc arg0)"
  using assms
  unfolding set_next_pcc_def bind_assoc
  by (no_reg_writes_toI simp: DelayedPCC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_SignalException[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0Cause'', ''CP0Status'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (SignalException arg0)"
  using assms
  unfolding SignalException_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0Cause_ref_def CP0Status_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_SignalExceptionBadAddr[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0BadVAddr'', ''CP0Cause'', ''CP0Status'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (SignalExceptionBadAddr arg0 arg1)"
  using assms
  unfolding SignalExceptionBadAddr_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0BadVAddr_ref_def CP0Cause_ref_def CP0Status_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_SignalExceptionTLB[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0BadVAddr'', ''CP0Cause'', ''CP0Status'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC'', ''TLBContext'', ''TLBEntryHi'', ''TLBXContext''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (SignalExceptionTLB arg0 arg1)"
  using assms
  unfolding SignalExceptionTLB_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0BadVAddr_ref_def CP0Cause_ref_def CP0Status_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def TLBContext_ref_def TLBEntryHi_ref_def TLBXContext_ref_def)

lemma no_reg_writes_to_undefined_MemAccessType[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_MemAccessType arg0)"
  unfolding undefined_MemAccessType_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_AccessLevel[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_AccessLevel arg0)"
  unfolding undefined_AccessLevel_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_getAccessLevel[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (getAccessLevel arg0)"
  unfolding getAccessLevel_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_pcc_access_system_regs[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (pcc_access_system_regs arg0)"
  unfolding pcc_access_system_regs_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_CapCauseReg[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_CapCauseReg arg0)"
  unfolding undefined_CapCauseReg_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_CapCauseReg_ExcCode[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_CapCauseReg_ExcCode arg0 arg1)"
  using assms
  unfolding set_CapCauseReg_ExcCode_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_CapCauseReg_RegNum[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_CapCauseReg_RegNum arg0 arg1)"
  using assms
  unfolding set_CapCauseReg_RegNum_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_raise_c2_exception8[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0Cause'', ''CP0Status'', ''CapCause'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (raise_c2_exception8 arg0 arg1)"
  using assms
  unfolding raise_c2_exception8_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0Cause_ref_def CP0Status_ref_def CapCause_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_raise_c2_exception_noreg[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0Cause'', ''CP0Status'', ''CapCause'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (raise_c2_exception_noreg arg0)"
  using assms
  unfolding raise_c2_exception_noreg_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0Cause_ref_def CP0Status_ref_def CapCause_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_checkCP0AccessHook[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0Cause'', ''CP0Status'', ''CapCause'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (checkCP0AccessHook arg0)"
  using assms
  unfolding checkCP0AccessHook_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0Cause_ref_def CP0Status_ref_def CapCause_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_checkCP0Access[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0Cause'', ''CP0Status'', ''CapCause'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (checkCP0Access arg0)"
  using assms
  unfolding checkCP0Access_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0Cause_ref_def CP0Status_ref_def CapCause_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_incrementCP0Count[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0Cause'', ''CP0Count'', ''CP0Status'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC'', ''TLBRandom''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (incrementCP0Count arg0)"
  using assms
  unfolding incrementCP0Count_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0Cause_ref_def CP0Count_ref_def CP0Status_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def TLBRandom_ref_def)

lemma no_reg_writes_to_undefined_decode_failure[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_decode_failure arg0)"
  unfolding undefined_decode_failure_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_Comparison[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_Comparison arg0)"
  unfolding undefined_Comparison_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_WordType[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_WordType arg0)"
  unfolding undefined_WordType_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_WordTypeUnaligned[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_WordTypeUnaligned arg0)"
  unfolding undefined_WordTypeUnaligned_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MEMr_wrapper[no_reg_writes_toI, simp]:
  assumes "{''UART_RVALID''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (MEMr_wrapper arg0 arg1)"
  using assms
  unfolding MEMr_wrapper_def bind_assoc
  by (no_reg_writes_toI simp: UART_RVALID_ref_def)

lemma no_reg_writes_to_MEMr_reserve_wrapper[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMr_reserve_wrapper arg0 arg1)"
  unfolding MEMr_reserve_wrapper_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_init_cp0_state[no_reg_writes_toI, simp]:
  assumes "{''CP0Status''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (init_cp0_state arg0)"
  using assms
  unfolding init_cp0_state_def bind_assoc
  by (no_reg_writes_toI simp: CP0Status_ref_def)

lemma no_reg_writes_to_tlbSearch[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (tlbSearch arg0)"
  unfolding tlbSearch_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_TLBTranslate2[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0BadVAddr'', ''CP0Cause'', ''CP0Status'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC'', ''TLBContext'', ''TLBEntryHi'', ''TLBXContext''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (TLBTranslate2 arg0 arg1)"
  using assms
  unfolding TLBTranslate2_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0BadVAddr_ref_def CP0Cause_ref_def CP0Status_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def TLBContext_ref_def TLBEntryHi_ref_def TLBXContext_ref_def)

lemma no_reg_writes_to_TLBTranslateC[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0BadVAddr'', ''CP0Cause'', ''CP0Status'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC'', ''TLBContext'', ''TLBEntryHi'', ''TLBXContext''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (TLBTranslateC arg0 arg1)"
  using assms
  unfolding TLBTranslateC_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0BadVAddr_ref_def CP0Cause_ref_def CP0Status_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def TLBContext_ref_def TLBEntryHi_ref_def TLBXContext_ref_def)

lemma no_reg_writes_to_TLBTranslate[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0BadVAddr'', ''CP0Cause'', ''CP0Status'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC'', ''TLBContext'', ''TLBEntryHi'', ''TLBXContext''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (TLBTranslate arg0 arg1)"
  using assms
  unfolding TLBTranslate_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0BadVAddr_ref_def CP0Cause_ref_def CP0Status_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def TLBContext_ref_def TLBEntryHi_ref_def TLBXContext_ref_def)

lemma no_reg_writes_to_undefined_CPtrCmpOp[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_CPtrCmpOp arg0)"
  unfolding undefined_CPtrCmpOp_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_ClearRegSet[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_ClearRegSet arg0)"
  unfolding undefined_ClearRegSet_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_capToString[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (capToString arg0 arg1)"
  unfolding capToString_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_undefined_CapEx[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_CapEx arg0)"
  unfolding undefined_CapEx_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_CapCauseReg_bits[no_reg_writes_toI, simp]:
  assumes "name arg0 \<notin> Rs"
  shows "no_reg_writes_to Rs (set_CapCauseReg_bits arg0 arg1)"
  using assms
  unfolding set_CapCauseReg_bits_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_execute_branch_pcc[no_reg_writes_toI, simp]:
  assumes "{''BranchPending'', ''DelayedPC'', ''DelayedPCC'', ''NextInBranchDelay''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (execute_branch_pcc arg0)"
  using assms
  unfolding execute_branch_pcc_def bind_assoc
  by (no_reg_writes_toI simp: BranchPending_ref_def DelayedPC_ref_def DelayedPCC_ref_def NextInBranchDelay_ref_def)

lemma no_reg_writes_to_ERETHook[no_reg_writes_toI, simp]:
  assumes "{''DelayedPCC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (ERETHook arg0)"
  using assms
  unfolding ERETHook_def bind_assoc
  by (no_reg_writes_toI simp: DelayedPCC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_raise_c2_exception[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0Cause'', ''CP0Status'', ''CapCause'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (raise_c2_exception arg0 arg1)"
  using assms
  unfolding raise_c2_exception_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0Cause_ref_def CP0Status_ref_def CapCause_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_MEMr_tagged[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMr_tagged arg0 arg1 arg2)"
  unfolding MEMr_tagged_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MEMr_tagged_reserve[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMr_tagged_reserve arg0 arg1 arg2)"
  unfolding MEMr_tagged_reserve_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MEMw_tagged[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMw_tagged arg0 arg1 arg2 arg3)"
  unfolding MEMw_tagged_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MEMw_tagged_conditional[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMw_tagged_conditional arg0 arg1 arg2 arg3)"
  unfolding MEMw_tagged_conditional_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_MEMw_wrapper[no_reg_writes_toI, simp]:
  assumes "{''UART_WDATA'', ''UART_WRITTEN''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (MEMw_wrapper arg0 arg1 arg2)"
  using assms
  unfolding MEMw_wrapper_def bind_assoc
  by (no_reg_writes_toI simp: UART_WDATA_ref_def UART_WRITTEN_ref_def)

lemma no_reg_writes_to_MEMw_conditional_wrapper[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMw_conditional_wrapper arg0 arg1 arg2)"
  unfolding MEMw_conditional_wrapper_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_checkDDCPerms[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0Cause'', ''CP0Status'', ''CapCause'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (checkDDCPerms arg0 arg1)"
  using assms
  unfolding checkDDCPerms_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0Cause_ref_def CP0Status_ref_def CapCause_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_addrWrapper[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0Cause'', ''CP0Status'', ''CapCause'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (addrWrapper arg0 arg1 arg2)"
  using assms
  unfolding addrWrapper_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0Cause_ref_def CP0Status_ref_def CapCause_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_addrWrapperUnaligned[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0Cause'', ''CP0Status'', ''CapCause'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (addrWrapperUnaligned arg0 arg1 arg2)"
  using assms
  unfolding addrWrapperUnaligned_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0Cause_ref_def CP0Status_ref_def CapCause_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_execute_branch[no_reg_writes_toI, simp]:
  assumes "{''BranchPending'', ''CP0BadInstr'', ''CP0BadInstrP'', ''CP0Cause'', ''CP0Status'', ''CapCause'', ''DelayedPC'', ''DelayedPCC'', ''EPCC'', ''NextInBranchDelay'', ''NextPC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (execute_branch arg0)"
  using assms
  unfolding execute_branch_def bind_assoc
  by (no_reg_writes_toI simp: BranchPending_ref_def CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0Cause_ref_def CP0Status_ref_def CapCause_ref_def DelayedPC_ref_def DelayedPCC_ref_def EPCC_ref_def NextInBranchDelay_ref_def NextPC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_TranslatePC[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0BadVAddr'', ''CP0Cause'', ''CP0Count'', ''CP0Status'', ''CapCause'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC'', ''TLBContext'', ''TLBEntryHi'', ''TLBRandom'', ''TLBXContext''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (TranslatePC arg0)"
  using assms
  unfolding TranslatePC_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0BadVAddr_ref_def CP0Cause_ref_def CP0Count_ref_def CP0Status_ref_def CapCause_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def TLBContext_ref_def TLBEntryHi_ref_def TLBRandom_ref_def TLBXContext_ref_def)

lemma no_reg_writes_to_checkCP2usable[no_reg_writes_toI, simp]:
  assumes "{''CP0BadInstr'', ''CP0BadInstrP'', ''CP0Cause'', ''CP0Status'', ''DelayedPCC'', ''EPCC'', ''NextPC'', ''NextPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (checkCP2usable arg0)"
  using assms
  unfolding checkCP2usable_def bind_assoc
  by (no_reg_writes_toI simp: CP0BadInstr_ref_def CP0BadInstrP_ref_def CP0Cause_ref_def CP0Status_ref_def DelayedPCC_ref_def EPCC_ref_def NextPC_ref_def NextPCC_ref_def)

lemma no_reg_writes_to_get_CP0EPC[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (get_CP0EPC arg0)"
  unfolding get_CP0EPC_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_CP0EPC[no_reg_writes_toI, simp]:
  assumes "{''EPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (set_CP0EPC arg0)"
  using assms
  unfolding set_CP0EPC_def bind_assoc
  by (no_reg_writes_toI simp: EPCC_ref_def)

lemma no_reg_writes_to_get_CP0ErrorEPC[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (get_CP0ErrorEPC arg0)"
  unfolding get_CP0ErrorEPC_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_set_CP0ErrorEPC[no_reg_writes_toI, simp]:
  assumes "{''ErrorEPCC''} \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (set_CP0ErrorEPC arg0)"
  using assms
  unfolding set_CP0ErrorEPC_def bind_assoc
  by (no_reg_writes_toI simp: ErrorEPCC_ref_def)

lemma no_reg_writes_to_dump_cp2_state[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (dump_cp2_state arg0)"
  unfolding dump_cp2_state_def bind_assoc
  by (no_reg_writes_toI)

end

end
