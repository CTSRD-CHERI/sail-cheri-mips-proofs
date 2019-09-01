theory CHERI_MIPS_Reg_Axioms
imports CHERI_MIPS_Gen_Lemmas
begin

context CHERI_MIPS_Reg_Automaton
begin

lemma preserves_invariant_write_non_inv_regs[preserves_invariantI]:
  "\<And>v. traces_preserve_invariant (write_reg BranchPending_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C01_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C02_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C03_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C04_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C05_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C06_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C07_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C08_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C09_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C10_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C11_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C12_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C13_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C14_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C15_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C16_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C17_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C18_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C19_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C20_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C21_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C22_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C23_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C24_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C25_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C26_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C27_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C28_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C29_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C30_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C31_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CID_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CP0BadInstr_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CP0BadInstrP_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CP0BadVAddr_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CP0Cause_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CP0Compare_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CP0ConfigK0_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CP0Count_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CP0HWREna_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CP0LLAddr_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CP0LLBit_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CP0Status_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CP0UserLocal_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CPLR_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CULR_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CapCause_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg CurrentInstrBits_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg DDC_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg DelayedPC_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg DelayedPCC_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg EPCC_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg ErrorEPCC_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg GPR_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg HI_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg InBranchDelay_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg KCC_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg KDC_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg KR1C_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg KR2C_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg LO_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg LastInstrBits_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg NextInBranchDelay_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg NextPC_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg NextPCC_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg PC_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBContext_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry00_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry01_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry02_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry03_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry04_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry05_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry06_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry07_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry08_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry09_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry10_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry11_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry12_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry13_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry14_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry15_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry16_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry17_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry18_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry19_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry20_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry21_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry22_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry23_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry24_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry25_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry26_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry27_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry28_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry29_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry30_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry31_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry32_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry33_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry34_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry35_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry36_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry37_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry38_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry39_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry40_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry41_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry42_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry43_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry44_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry45_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry46_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry47_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry48_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry49_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry50_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry51_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry52_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry53_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry54_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry55_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry56_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry57_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry58_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry59_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry60_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry61_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry62_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntry63_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntryHi_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntryLo0_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntryLo1_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBIndex_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBPageMask_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBProbe_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBRandom_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBWired_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBXContext_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg UART_RDATA_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg UART_RVALID_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg UART_WDATA_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg UART_WRITTEN_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg InstCount_ref v)"
  unfolding BranchPending_ref_def C01_ref_def C02_ref_def C03_ref_def C04_ref_def
     C05_ref_def C06_ref_def C07_ref_def C08_ref_def C09_ref_def
     C10_ref_def C11_ref_def C12_ref_def C13_ref_def C14_ref_def
     C15_ref_def C16_ref_def C17_ref_def C18_ref_def C19_ref_def
     C20_ref_def C21_ref_def C22_ref_def C23_ref_def C24_ref_def
     C25_ref_def C26_ref_def C27_ref_def C28_ref_def C29_ref_def
     C30_ref_def C31_ref_def CID_ref_def CP0BadInstr_ref_def CP0BadInstrP_ref_def
     CP0BadVAddr_ref_def CP0Cause_ref_def CP0Compare_ref_def CP0ConfigK0_ref_def CP0Count_ref_def
     CP0HWREna_ref_def CP0LLAddr_ref_def CP0LLBit_ref_def CP0Status_ref_def CP0UserLocal_ref_def
     CPLR_ref_def CULR_ref_def CapCause_ref_def CurrentInstrBits_ref_def DDC_ref_def
     DelayedPC_ref_def DelayedPCC_ref_def EPCC_ref_def ErrorEPCC_ref_def GPR_ref_def
     HI_ref_def InBranchDelay_ref_def KCC_ref_def KDC_ref_def KR1C_ref_def
     KR2C_ref_def LO_ref_def LastInstrBits_ref_def NextInBranchDelay_ref_def NextPC_ref_def
     NextPCC_ref_def PC_ref_def TLBContext_ref_def TLBEntry00_ref_def TLBEntry01_ref_def
     TLBEntry02_ref_def TLBEntry03_ref_def TLBEntry04_ref_def TLBEntry05_ref_def TLBEntry06_ref_def
     TLBEntry07_ref_def TLBEntry08_ref_def TLBEntry09_ref_def TLBEntry10_ref_def TLBEntry11_ref_def
     TLBEntry12_ref_def TLBEntry13_ref_def TLBEntry14_ref_def TLBEntry15_ref_def TLBEntry16_ref_def
     TLBEntry17_ref_def TLBEntry18_ref_def TLBEntry19_ref_def TLBEntry20_ref_def TLBEntry21_ref_def
     TLBEntry22_ref_def TLBEntry23_ref_def TLBEntry24_ref_def TLBEntry25_ref_def TLBEntry26_ref_def
     TLBEntry27_ref_def TLBEntry28_ref_def TLBEntry29_ref_def TLBEntry30_ref_def TLBEntry31_ref_def
     TLBEntry32_ref_def TLBEntry33_ref_def TLBEntry34_ref_def TLBEntry35_ref_def TLBEntry36_ref_def
     TLBEntry37_ref_def TLBEntry38_ref_def TLBEntry39_ref_def TLBEntry40_ref_def TLBEntry41_ref_def
     TLBEntry42_ref_def TLBEntry43_ref_def TLBEntry44_ref_def TLBEntry45_ref_def TLBEntry46_ref_def
     TLBEntry47_ref_def TLBEntry48_ref_def TLBEntry49_ref_def TLBEntry50_ref_def TLBEntry51_ref_def
     TLBEntry52_ref_def TLBEntry53_ref_def TLBEntry54_ref_def TLBEntry55_ref_def TLBEntry56_ref_def
     TLBEntry57_ref_def TLBEntry58_ref_def TLBEntry59_ref_def TLBEntry60_ref_def TLBEntry61_ref_def
     TLBEntry62_ref_def TLBEntry63_ref_def TLBEntryHi_ref_def TLBEntryLo0_ref_def TLBEntryLo1_ref_def
     TLBIndex_ref_def TLBPageMask_ref_def TLBProbe_ref_def TLBRandom_ref_def TLBWired_ref_def
     TLBXContext_ref_def UART_RDATA_ref_def UART_RVALID_ref_def UART_WDATA_ref_def UART_WRITTEN_ref_def
     InstCount_ref_def
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg; simp)+

(*lemma preserves_invariant_no_writes_to_inv_regs[preserves_invariantI]:
  "\<And>arg0. traces_preserve_invariant (undefined_option arg0)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MIPS_write arg0 arg1 arg2)"
  "\<And>arg0 arg1. traces_preserve_invariant (MIPS_read arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (undefined_exception arg0)"
  "\<And>arg0. traces_preserve_invariant (undefined_CauseReg arg0)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_bits arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_BD arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_CE arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_IV arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_WP arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_IP arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_ExcCode arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (undefined_TLBEntryLoReg arg0)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_bits arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_CapS arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_CapL arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_PFN arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_C arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_D arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_V arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_G arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (undefined_TLBEntryHiReg arg0)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryHiReg_bits arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryHiReg_R arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryHiReg_VPN2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryHiReg_ASID arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (undefined_ContextReg arg0)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_ContextReg_bits arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_ContextReg_PTEBase arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_ContextReg_BadVPN2 arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (undefined_XContextReg arg0)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_XContextReg_bits arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_XContextReg_XPTEBase arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_XContextReg_XR arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_XContextReg_XBadVPN2 arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (undefined_TLBEntry arg0)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_bits arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_pagemask arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_r arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_vpn2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_asid arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_g arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_valid arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_caps1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_capl1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_pfn1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_c1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_d1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_v1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_caps0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_capl0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_pfn0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_c0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_d0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_v0 arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (undefined_StatusReg arg0)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_bits arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_CU arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_BEV arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_IM arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_KX arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_SX arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_UX arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_KSU arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_ERL arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_EXL arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_IE arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (execute_branch_mips arg0)"
  "\<And>arg0. traces_preserve_invariant (rGPR arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (wGPR arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr_reserve arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (MEM_sync arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMea arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMea_conditional arg0 arg1)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMval arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMval_conditional arg0 arg1 arg2)"
  "\<And>arg0. traces_preserve_invariant (undefined_Exception arg0)"
  "\<And>arg0. traces_preserve_invariant (exceptionVectorOffset arg0)"
  "\<And>arg0. traces_preserve_invariant (exceptionVectorBase arg0)"
  "\<And>arg0. traces_preserve_invariant (updateBadInstr arg0)"
  "\<And>arg0. traces_preserve_invariant (undefined_Capability arg0)"
  "\<And>arg0. traces_preserve_invariant (set_next_pcc arg0)"
  "\<And>arg0. traces_preserve_invariant (SignalException arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (SignalExceptionBadAddr arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (SignalExceptionTLB arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (undefined_MemAccessType arg0)"
  "\<And>arg0. traces_preserve_invariant (undefined_AccessLevel arg0)"
  "\<And>arg0. traces_preserve_invariant (getAccessLevel arg0)"
  "\<And>arg0. traces_preserve_invariant (pcc_access_system_regs arg0)"
  "\<And>arg0. traces_preserve_invariant (undefined_CapCauseReg arg0)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CapCauseReg_ExcCode arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CapCauseReg_RegNum arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (raise_c2_exception8 arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (raise_c2_exception_noreg arg0)"
  "\<And>arg0. traces_preserve_invariant (checkCP0AccessHook arg0)"
  "\<And>arg0. traces_preserve_invariant (checkCP0Access arg0)"
  "\<And>arg0. traces_preserve_invariant (incrementCP0Count arg0)"
  "\<And>arg0. traces_preserve_invariant (undefined_decode_failure arg0)"
  "\<And>arg0. traces_preserve_invariant (undefined_Comparison arg0)"
  "\<And>arg0. traces_preserve_invariant (undefined_WordType arg0)"
  "\<And>arg0. traces_preserve_invariant (undefined_WordTypeUnaligned arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr_wrapper arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr_reserve_wrapper arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (init_cp0_state arg0)"
  "\<And>arg0. traces_preserve_invariant (tlbSearch arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (TLBTranslate2 arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (TLBTranslateC arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (TLBTranslate arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (undefined_CPtrCmpOp arg0)"
  "\<And>arg0. traces_preserve_invariant (undefined_ClearRegSet arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (capToString arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (undefined_CapEx arg0)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CapCauseReg_bits arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (execute_branch_pcc arg0)"
  "\<And>arg0. traces_preserve_invariant (ERETHook arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (raise_c2_exception arg0 arg1)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMr_tagged arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMr_tagged_reserve arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2 arg3. traces_preserve_invariant (MEMw_tagged arg0 arg1 arg2 arg3)"
  "\<And>arg0 arg1 arg2 arg3. traces_preserve_invariant (MEMw_tagged_conditional arg0 arg1 arg2 arg3)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMw_wrapper arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMw_conditional_wrapper arg0 arg1 arg2)"
  "\<And>arg0 arg1. traces_preserve_invariant (checkDDCPerms arg0 arg1)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (addrWrapper arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (addrWrapperUnaligned arg0 arg1 arg2)"
  "\<And>arg0. traces_preserve_invariant (execute_branch arg0)"
  "\<And>arg0. traces_preserve_invariant (TranslatePC arg0)"
  "\<And>arg0. traces_preserve_invariant (checkCP2usable arg0)"
  "\<And>arg0. traces_preserve_invariant (get_CP0EPC arg0)"
  "\<And>arg0. traces_preserve_invariant (set_CP0EPC arg0)"
  "\<And>arg0. traces_preserve_invariant (get_CP0ErrorEPC arg0)"
  "\<And>arg0. traces_preserve_invariant (set_CP0ErrorEPC arg0)"
  "\<And>arg0. traces_preserve_invariant (dump_cp2_state arg0)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_toI; simp)+*)

lemma preserves_invariant_no_writes_to_inv_regs[preserves_invariantI]:
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MIPS_write arg0 arg1 arg2)"
  "\<And>arg0 arg1. traces_preserve_invariant (MIPS_read arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_BD arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_CE arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_IV arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_IP arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_ExcCode arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_bits arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_CapS arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_CapL arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_PFN arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_C arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_D arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_V arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_G arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryHiReg_R arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryHiReg_VPN2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryHiReg_ASID arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_ContextReg_PTEBase arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_ContextReg_BadVPN2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_XContextReg_XPTEBase arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_XContextReg_XR arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_XContextReg_XBadVPN2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_pagemask arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_r arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_vpn2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_asid arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_g arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_valid arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_caps1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_capl1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_pfn1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_c1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_d1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_v1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_caps0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_capl0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_pfn0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_c0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_d0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_v0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_CU arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_BEV arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_IM arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_KX arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_SX arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_UX arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_KSU arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_ERL arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_EXL arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_IE arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (execute_branch_mips arg0)"
  "\<And>arg0. traces_preserve_invariant (rGPR arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (wGPR arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr_reserve arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (MEM_sync arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMea arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMea_conditional arg0 arg1)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMval arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMval_conditional arg0 arg1 arg2)"
  "\<And>arg0. traces_preserve_invariant (exceptionVectorOffset arg0)"
  "\<And>arg0. traces_preserve_invariant (exceptionVectorBase arg0)"
  "\<And>arg0. traces_preserve_invariant (updateBadInstr arg0)"
  "\<And>arg0. traces_preserve_invariant (set_next_pcc arg0)"
  "\<And>arg0. traces_preserve_invariant (SignalException arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (SignalExceptionBadAddr arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (SignalExceptionTLB arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (getAccessLevel arg0)"
  "\<And>arg0. traces_preserve_invariant (pcc_access_system_regs arg0)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CapCauseReg_ExcCode arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CapCauseReg_RegNum arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (raise_c2_exception8 arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (raise_c2_exception_noreg arg0)"
  "\<And>arg0. traces_preserve_invariant (checkCP0AccessHook arg0)"
  "\<And>arg0. traces_preserve_invariant (checkCP0Access arg0)"
  "\<And>arg0. traces_preserve_invariant (incrementCP0Count arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr_wrapper arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr_reserve_wrapper arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (tlbSearch arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (TLBTranslate2 arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (TLBTranslateC arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (TLBTranslate arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (capToString arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (execute_branch_pcc arg0)"
  "\<And>arg0. traces_preserve_invariant (ERETHook arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (raise_c2_exception arg0 arg1)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMr_tagged arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMr_tagged_reserve arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2 arg3. traces_preserve_invariant (MEMw_tagged arg0 arg1 arg2 arg3)"
  "\<And>arg0 arg1 arg2 arg3. traces_preserve_invariant (MEMw_tagged_conditional arg0 arg1 arg2 arg3)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMw_wrapper arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMw_conditional_wrapper arg0 arg1 arg2)"
  "\<And>arg0 arg1. traces_preserve_invariant (checkDDCPerms arg0 arg1)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (addrWrapper arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (addrWrapperUnaligned arg0 arg1 arg2)"
  "\<And>arg0. traces_preserve_invariant (execute_branch arg0)"
  "\<And>arg0. traces_preserve_invariant (checkCP2usable arg0)"
  "\<And>arg0. traces_preserve_invariant (get_CP0EPC arg0)"
  "\<And>arg0. traces_preserve_invariant (set_CP0EPC arg0)"
  "\<And>arg0. traces_preserve_invariant (get_CP0ErrorEPC arg0)"
  "\<And>arg0. traces_preserve_invariant (set_CP0ErrorEPC arg0)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_toI; simp)+

lemma preserves_invariant_write_reg[preserves_invariantI]:
  assumes "name r \<notin> inv_regs"
  shows "traces_preserve_invariant (write_reg r v)"
  using assms
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_toI)

lemma preserves_invariant_TLBWriteEntry[preserves_invariantI]:
  "traces_preserve_invariant (TLBWriteEntry idx)"
  unfolding TLBWriteEntry_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_option[preserves_invariantI]:
  "runs_preserve_invariant (undefined_option arg0)"
  unfolding undefined_option_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_exception[preserves_invariantI]:
  "runs_preserve_invariant (undefined_exception arg0)"
  unfolding undefined_exception_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_CauseReg[preserves_invariantI]:
  "runs_preserve_invariant (undefined_CauseReg arg0)"
  unfolding undefined_CauseReg_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_set_CauseReg_bits[preserves_invariantI]:
  assumes "name arg0 \<notin> inv_regs"
  shows "runs_preserve_invariant (set_CauseReg_bits arg0 arg1)"
  using assms
  unfolding set_CauseReg_bits_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_set_CauseReg_WP[preserves_invariantI]:
  assumes "name arg0 \<notin> inv_regs"
  shows "runs_preserve_invariant (set_CauseReg_WP arg0 arg1)"
  using assms
  unfolding set_CauseReg_WP_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_TLBEntryLoReg[preserves_invariantI]:
  "runs_preserve_invariant (undefined_TLBEntryLoReg arg0)"
  unfolding undefined_TLBEntryLoReg_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_TLBEntryHiReg[preserves_invariantI]:
  "runs_preserve_invariant (undefined_TLBEntryHiReg arg0)"
  unfolding undefined_TLBEntryHiReg_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_set_TLBEntryHiReg_bits[preserves_invariantI]:
  assumes "name arg0 \<notin> inv_regs"
  shows "runs_preserve_invariant (set_TLBEntryHiReg_bits arg0 arg1)"
  using assms
  unfolding set_TLBEntryHiReg_bits_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_ContextReg[preserves_invariantI]:
  "runs_preserve_invariant (undefined_ContextReg arg0)"
  unfolding undefined_ContextReg_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_set_ContextReg_bits[preserves_invariantI]:
  assumes "name arg0 \<notin> inv_regs"
  shows "runs_preserve_invariant (set_ContextReg_bits arg0 arg1)"
  using assms
  unfolding set_ContextReg_bits_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_XContextReg[preserves_invariantI]:
  "runs_preserve_invariant (undefined_XContextReg arg0)"
  unfolding undefined_XContextReg_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_set_XContextReg_bits[preserves_invariantI]:
  assumes "name arg0 \<notin> inv_regs"
  shows "runs_preserve_invariant (set_XContextReg_bits arg0 arg1)"
  using assms
  unfolding set_XContextReg_bits_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_TLBEntry[preserves_invariantI]:
  "runs_preserve_invariant (undefined_TLBEntry arg0)"
  unfolding undefined_TLBEntry_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_set_TLBEntry_bits[preserves_invariantI]:
  assumes "name arg0 \<notin> inv_regs"
  shows "runs_preserve_invariant (set_TLBEntry_bits arg0 arg1)"
  using assms
  unfolding set_TLBEntry_bits_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_StatusReg[preserves_invariantI]:
  "runs_preserve_invariant (undefined_StatusReg arg0)"
  unfolding undefined_StatusReg_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_set_StatusReg_bits[preserves_invariantI]:
  assumes "name arg0 \<notin> inv_regs"
  shows "runs_preserve_invariant (set_StatusReg_bits arg0 arg1)"
  using assms
  unfolding set_StatusReg_bits_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_Exception[preserves_invariantI]:
  "runs_preserve_invariant (undefined_Exception arg0)"
  unfolding undefined_Exception_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_Capability[preserves_invariantI]:
  "runs_preserve_invariant (undefined_Capability arg0)"
  unfolding undefined_Capability_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_MemAccessType[preserves_invariantI]:
  "runs_preserve_invariant (undefined_MemAccessType arg0)"
  unfolding undefined_MemAccessType_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_AccessLevel[preserves_invariantI]:
  "runs_preserve_invariant (undefined_AccessLevel arg0)"
  unfolding undefined_AccessLevel_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_CapCauseReg[preserves_invariantI]:
  "runs_preserve_invariant (undefined_CapCauseReg arg0)"
  unfolding undefined_CapCauseReg_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_decode_failure[preserves_invariantI]:
  "runs_preserve_invariant (undefined_decode_failure arg0)"
  unfolding undefined_decode_failure_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_Comparison[preserves_invariantI]:
  "runs_preserve_invariant (undefined_Comparison arg0)"
  unfolding undefined_Comparison_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_WordType[preserves_invariantI]:
  "runs_preserve_invariant (undefined_WordType arg0)"
  unfolding undefined_WordType_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_WordTypeUnaligned[preserves_invariantI]:
  "runs_preserve_invariant (undefined_WordTypeUnaligned arg0)"
  unfolding undefined_WordTypeUnaligned_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_init_cp0_state[preserves_invariantI]:
  "runs_preserve_invariant (init_cp0_state arg0)"
  unfolding init_cp0_state_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_CPtrCmpOp[preserves_invariantI]:
  "runs_preserve_invariant (undefined_CPtrCmpOp arg0)"
  unfolding undefined_CPtrCmpOp_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_ClearRegSet[preserves_invariantI]:
  "runs_preserve_invariant (undefined_ClearRegSet arg0)"
  unfolding undefined_ClearRegSet_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_undefined_CapEx[preserves_invariantI]:
  "runs_preserve_invariant (undefined_CapEx arg0)"
  unfolding undefined_CapEx_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_set_CapCauseReg_bits[preserves_invariantI]:
  assumes "name arg0 \<notin> inv_regs"
  shows "runs_preserve_invariant (set_CapCauseReg_bits arg0 arg1)"
  using assms
  unfolding set_CapCauseReg_bits_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_TranslatePC[preserves_invariantI]:
  "runs_preserve_invariant (TranslatePC arg0)"
  unfolding TranslatePC_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_dump_cp2_state[preserves_invariantI]:
  "runs_preserve_invariant (dump_cp2_state arg0)"
  unfolding dump_cp2_state_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_XORI[preserves_invariantI]:
  "runs_preserve_invariant (execute_XORI arg0 arg1 arg2)"
  unfolding execute_XORI_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_XOR[preserves_invariantI]:
  "runs_preserve_invariant (execute_XOR arg0 arg1 arg2)"
  unfolding execute_XOR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_WAIT[preserves_invariantI]:
  "runs_preserve_invariant (execute_WAIT arg0)"
  unfolding execute_WAIT_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_TRAPREG[preserves_invariantI]:
  "runs_preserve_invariant (execute_TRAPREG arg0 arg1 arg2)"
  unfolding execute_TRAPREG_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_TRAPIMM[preserves_invariantI]:
  "runs_preserve_invariant (execute_TRAPIMM arg0 arg1 arg2)"
  unfolding execute_TRAPIMM_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_TLBWR[preserves_invariantI]:
  "runs_preserve_invariant (execute_TLBWR arg0)"
  unfolding execute_TLBWR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_TLBWI[preserves_invariantI]:
  "runs_preserve_invariant (execute_TLBWI arg0)"
  unfolding execute_TLBWI_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_TLBR[preserves_invariantI]:
  "runs_preserve_invariant (execute_TLBR arg0)"
  unfolding execute_TLBR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_TLBP[preserves_invariantI]:
  "runs_preserve_invariant (execute_TLBP arg0)"
  unfolding execute_TLBP_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_Store[preserves_invariantI]:
  "runs_preserve_invariant (execute_Store arg0 arg1 arg2 arg3 arg4)"
  unfolding execute_Store_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SYSCALL[preserves_invariantI]:
  "runs_preserve_invariant (execute_SYSCALL arg0)"
  unfolding execute_SYSCALL_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SYNC[preserves_invariantI]:
  "runs_preserve_invariant (execute_SYNC arg0)"
  unfolding execute_SYNC_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SWR[preserves_invariantI]:
  "runs_preserve_invariant (execute_SWR arg0 arg1 arg2)"
  unfolding execute_SWR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SWL[preserves_invariantI]:
  "runs_preserve_invariant (execute_SWL arg0 arg1 arg2)"
  unfolding execute_SWL_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SUBU[preserves_invariantI]:
  "runs_preserve_invariant (execute_SUBU arg0 arg1 arg2)"
  unfolding execute_SUBU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SUB[preserves_invariantI]:
  "runs_preserve_invariant (execute_SUB arg0 arg1 arg2)"
  unfolding execute_SUB_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SRLV[preserves_invariantI]:
  "runs_preserve_invariant (execute_SRLV arg0 arg1 arg2)"
  unfolding execute_SRLV_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SRL[preserves_invariantI]:
  "runs_preserve_invariant (execute_SRL arg0 arg1 arg2)"
  unfolding execute_SRL_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SRAV[preserves_invariantI]:
  "runs_preserve_invariant (execute_SRAV arg0 arg1 arg2)"
  unfolding execute_SRAV_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SRA[preserves_invariantI]:
  "runs_preserve_invariant (execute_SRA arg0 arg1 arg2)"
  unfolding execute_SRA_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SLTU[preserves_invariantI]:
  "runs_preserve_invariant (execute_SLTU arg0 arg1 arg2)"
  unfolding execute_SLTU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SLTIU[preserves_invariantI]:
  "runs_preserve_invariant (execute_SLTIU arg0 arg1 arg2)"
  unfolding execute_SLTIU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SLTI[preserves_invariantI]:
  "runs_preserve_invariant (execute_SLTI arg0 arg1 arg2)"
  unfolding execute_SLTI_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SLT[preserves_invariantI]:
  "runs_preserve_invariant (execute_SLT arg0 arg1 arg2)"
  unfolding execute_SLT_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SLLV[preserves_invariantI]:
  "runs_preserve_invariant (execute_SLLV arg0 arg1 arg2)"
  unfolding execute_SLLV_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SLL[preserves_invariantI]:
  "runs_preserve_invariant (execute_SLL arg0 arg1 arg2)"
  unfolding execute_SLL_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SDR[preserves_invariantI]:
  "runs_preserve_invariant (execute_SDR arg0 arg1 arg2)"
  unfolding execute_SDR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_SDL[preserves_invariantI]:
  "runs_preserve_invariant (execute_SDL arg0 arg1 arg2)"
  unfolding execute_SDL_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_RI[preserves_invariantI]:
  "runs_preserve_invariant (execute_RI arg0)"
  unfolding execute_RI_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_RDHWR[preserves_invariantI]:
  "runs_preserve_invariant (execute_RDHWR arg0 arg1)"
  unfolding execute_RDHWR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_ORI[preserves_invariantI]:
  "runs_preserve_invariant (execute_ORI arg0 arg1 arg2)"
  unfolding execute_ORI_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_OR[preserves_invariantI]:
  "runs_preserve_invariant (execute_OR arg0 arg1 arg2)"
  unfolding execute_OR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_NOR[preserves_invariantI]:
  "runs_preserve_invariant (execute_NOR arg0 arg1 arg2)"
  unfolding execute_NOR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MULTU[preserves_invariantI]:
  "runs_preserve_invariant (execute_MULTU arg0 arg1)"
  unfolding execute_MULTU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MULT[preserves_invariantI]:
  "runs_preserve_invariant (execute_MULT arg0 arg1)"
  unfolding execute_MULT_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MUL[preserves_invariantI]:
  "runs_preserve_invariant (execute_MUL arg0 arg1 arg2)"
  unfolding execute_MUL_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MTLO[preserves_invariantI]:
  "runs_preserve_invariant (execute_MTLO arg0)"
  unfolding execute_MTLO_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MTHI[preserves_invariantI]:
  "runs_preserve_invariant (execute_MTHI arg0)"
  unfolding execute_MTHI_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MTC0[preserves_invariantI]:
  "runs_preserve_invariant (execute_MTC0 arg0 arg1 arg2 arg3)"
  unfolding execute_MTC0_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MSUBU[preserves_invariantI]:
  "runs_preserve_invariant (execute_MSUBU arg0 arg1)"
  unfolding execute_MSUBU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MSUB[preserves_invariantI]:
  "runs_preserve_invariant (execute_MSUB arg0 arg1)"
  unfolding execute_MSUB_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MOVZ[preserves_invariantI]:
  "runs_preserve_invariant (execute_MOVZ arg0 arg1 arg2)"
  unfolding execute_MOVZ_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MOVN[preserves_invariantI]:
  "runs_preserve_invariant (execute_MOVN arg0 arg1 arg2)"
  unfolding execute_MOVN_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MFLO[preserves_invariantI]:
  "runs_preserve_invariant (execute_MFLO arg0)"
  unfolding execute_MFLO_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MFHI[preserves_invariantI]:
  "runs_preserve_invariant (execute_MFHI arg0)"
  unfolding execute_MFHI_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MFC0[preserves_invariantI]:
  "runs_preserve_invariant (execute_MFC0 arg0 arg1 arg2 arg3)"
  unfolding execute_MFC0_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MADDU[preserves_invariantI]:
  "runs_preserve_invariant (execute_MADDU arg0 arg1)"
  unfolding execute_MADDU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_MADD[preserves_invariantI]:
  "runs_preserve_invariant (execute_MADD arg0 arg1)"
  unfolding execute_MADD_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_Load[preserves_invariantI]:
  "runs_preserve_invariant (execute_Load arg0 arg1 arg2 arg3 arg4 arg5)"
  unfolding execute_Load_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_LWR[preserves_invariantI]:
  "runs_preserve_invariant (execute_LWR arg0 arg1 arg2)"
  unfolding execute_LWR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_LWL[preserves_invariantI]:
  "runs_preserve_invariant (execute_LWL arg0 arg1 arg2)"
  unfolding execute_LWL_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_LUI[preserves_invariantI]:
  "runs_preserve_invariant (execute_LUI arg0 arg1)"
  unfolding execute_LUI_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_LDR[preserves_invariantI]:
  "runs_preserve_invariant (execute_LDR arg0 arg1 arg2)"
  unfolding execute_LDR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_LDL[preserves_invariantI]:
  "runs_preserve_invariant (execute_LDL arg0 arg1 arg2)"
  unfolding execute_LDL_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_JR[preserves_invariantI]:
  "runs_preserve_invariant (execute_JR arg0)"
  unfolding execute_JR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_JALR[preserves_invariantI]:
  "runs_preserve_invariant (execute_JALR arg0 arg1)"
  unfolding execute_JALR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_JAL[preserves_invariantI]:
  "runs_preserve_invariant (execute_JAL arg0)"
  unfolding execute_JAL_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_J[preserves_invariantI]:
  "runs_preserve_invariant (execute_J arg0)"
  unfolding execute_J_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_ERET[preserves_invariantI]:
  "runs_preserve_invariant (execute_ERET arg0)"
  unfolding execute_ERET_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DSUBU[preserves_invariantI]:
  "runs_preserve_invariant (execute_DSUBU arg0 arg1 arg2)"
  unfolding execute_DSUBU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DSUB[preserves_invariantI]:
  "runs_preserve_invariant (execute_DSUB arg0 arg1 arg2)"
  unfolding execute_DSUB_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DSRLV[preserves_invariantI]:
  "runs_preserve_invariant (execute_DSRLV arg0 arg1 arg2)"
  unfolding execute_DSRLV_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DSRL32[preserves_invariantI]:
  "runs_preserve_invariant (execute_DSRL32 arg0 arg1 arg2)"
  unfolding execute_DSRL32_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DSRL[preserves_invariantI]:
  "runs_preserve_invariant (execute_DSRL arg0 arg1 arg2)"
  unfolding execute_DSRL_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DSRAV[preserves_invariantI]:
  "runs_preserve_invariant (execute_DSRAV arg0 arg1 arg2)"
  unfolding execute_DSRAV_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DSRA32[preserves_invariantI]:
  "runs_preserve_invariant (execute_DSRA32 arg0 arg1 arg2)"
  unfolding execute_DSRA32_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DSRA[preserves_invariantI]:
  "runs_preserve_invariant (execute_DSRA arg0 arg1 arg2)"
  unfolding execute_DSRA_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DSLLV[preserves_invariantI]:
  "runs_preserve_invariant (execute_DSLLV arg0 arg1 arg2)"
  unfolding execute_DSLLV_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DSLL32[preserves_invariantI]:
  "runs_preserve_invariant (execute_DSLL32 arg0 arg1 arg2)"
  unfolding execute_DSLL32_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DSLL[preserves_invariantI]:
  "runs_preserve_invariant (execute_DSLL arg0 arg1 arg2)"
  unfolding execute_DSLL_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DMULTU[preserves_invariantI]:
  "runs_preserve_invariant (execute_DMULTU arg0 arg1)"
  unfolding execute_DMULTU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DMULT[preserves_invariantI]:
  "runs_preserve_invariant (execute_DMULT arg0 arg1)"
  unfolding execute_DMULT_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DIVU[preserves_invariantI]:
  "runs_preserve_invariant (execute_DIVU arg0 arg1)"
  unfolding execute_DIVU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DIV[preserves_invariantI]:
  "runs_preserve_invariant (execute_DIV arg0 arg1)"
  unfolding execute_DIV_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DDIVU[preserves_invariantI]:
  "runs_preserve_invariant (execute_DDIVU arg0 arg1)"
  unfolding execute_DDIVU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DDIV[preserves_invariantI]:
  "runs_preserve_invariant (execute_DDIV arg0 arg1)"
  unfolding execute_DDIV_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DADDU[preserves_invariantI]:
  "runs_preserve_invariant (execute_DADDU arg0 arg1 arg2)"
  unfolding execute_DADDU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DADDIU[preserves_invariantI]:
  "runs_preserve_invariant (execute_DADDIU arg0 arg1 arg2)"
  unfolding execute_DADDIU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DADDI[preserves_invariantI]:
  "runs_preserve_invariant (execute_DADDI arg0 arg1 arg2)"
  unfolding execute_DADDI_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_DADD[preserves_invariantI]:
  "runs_preserve_invariant (execute_DADD arg0 arg1 arg2)"
  unfolding execute_DADD_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_ClearRegs[preserves_invariantI]:
  "runs_preserve_invariant (execute_ClearRegs arg0 arg1)"
  unfolding execute_ClearRegs_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CWriteHwr[preserves_invariantI]:
  "runs_preserve_invariant (execute_CWriteHwr arg0 arg1)"
  unfolding execute_CWriteHwr_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CUnseal[preserves_invariantI]:
  "runs_preserve_invariant (execute_CUnseal arg0 arg1 arg2)"
  unfolding execute_CUnseal_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CToPtr[preserves_invariantI]:
  "runs_preserve_invariant (execute_CToPtr arg0 arg1 arg2)"
  unfolding execute_CToPtr_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CTestSubset[preserves_invariantI]:
  "runs_preserve_invariant (execute_CTestSubset arg0 arg1 arg2)"
  unfolding execute_CTestSubset_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CSub[preserves_invariantI]:
  "runs_preserve_invariant (execute_CSub arg0 arg1 arg2)"
  unfolding execute_CSub_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CStoreConditional[preserves_invariantI]:
  "runs_preserve_invariant (execute_CStoreConditional arg0 arg1 arg2 arg3)"
  unfolding execute_CStoreConditional_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CStore[preserves_invariantI]:
  "runs_preserve_invariant (execute_CStore arg0 arg1 arg2 arg3 arg4)"
  unfolding execute_CStore_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CSetOffset[preserves_invariantI]:
  "runs_preserve_invariant (execute_CSetOffset arg0 arg1 arg2)"
  unfolding execute_CSetOffset_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CSetFlags[preserves_invariantI]:
  "runs_preserve_invariant (execute_CSetFlags arg0 arg1 arg2)"
  unfolding execute_CSetFlags_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CSetCause[preserves_invariantI]:
  "runs_preserve_invariant (execute_CSetCause arg0)"
  unfolding execute_CSetCause_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CSetCID[preserves_invariantI]:
  "runs_preserve_invariant (execute_CSetCID arg0)"
  unfolding execute_CSetCID_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CSetBoundsImmediate[preserves_invariantI]:
  "runs_preserve_invariant (execute_CSetBoundsImmediate arg0 arg1 arg2)"
  unfolding execute_CSetBoundsImmediate_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CSetBoundsExact[preserves_invariantI]:
  "runs_preserve_invariant (execute_CSetBoundsExact arg0 arg1 arg2)"
  unfolding execute_CSetBoundsExact_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CSetBounds[preserves_invariantI]:
  "runs_preserve_invariant (execute_CSetBounds arg0 arg1 arg2)"
  unfolding execute_CSetBounds_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CSetAddr[preserves_invariantI]:
  "runs_preserve_invariant (execute_CSetAddr arg0 arg1 arg2)"
  unfolding execute_CSetAddr_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CSeal[preserves_invariantI]:
  "runs_preserve_invariant (execute_CSeal arg0 arg1 arg2)"
  unfolding execute_CSeal_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CSCC[preserves_invariantI]:
  "runs_preserve_invariant (execute_CSCC arg0 arg1 arg2)"
  unfolding execute_CSCC_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CSC[preserves_invariantI]:
  "runs_preserve_invariant (execute_CSC arg0 arg1 arg2 arg3)"
  unfolding execute_CSC_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CReturn[preserves_invariantI]:
  "runs_preserve_invariant (execute_CReturn arg0)"
  unfolding execute_CReturn_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CReadHwr[preserves_invariantI]:
  "runs_preserve_invariant (execute_CReadHwr arg0 arg1)"
  unfolding execute_CReadHwr_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CRAP[preserves_invariantI]:
  "runs_preserve_invariant (execute_CRAP arg0 arg1)"
  unfolding execute_CRAP_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CRAM[preserves_invariantI]:
  "runs_preserve_invariant (execute_CRAM arg0 arg1)"
  unfolding execute_CRAM_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CPtrCmp[preserves_invariantI]:
  "runs_preserve_invariant (execute_CPtrCmp arg0 arg1 arg2 arg3)"
  unfolding execute_CPtrCmp_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CMove[preserves_invariantI]:
  "runs_preserve_invariant (execute_CMove arg0 arg1)"
  unfolding execute_CMove_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CMOVX[preserves_invariantI]:
  "runs_preserve_invariant (execute_CMOVX arg0 arg1 arg2 arg3)"
  unfolding execute_CMOVX_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CLoadTags[preserves_invariantI]:
  "runs_preserve_invariant (execute_CLoadTags arg0 arg1)"
  unfolding execute_CLoadTags_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CLoadLinked[preserves_invariantI]:
  "runs_preserve_invariant (execute_CLoadLinked arg0 arg1 arg2 arg3)"
  unfolding execute_CLoadLinked_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CLoad[preserves_invariantI]:
  "runs_preserve_invariant (execute_CLoad arg0 arg1 arg2 arg3 arg4 arg5)"
  unfolding execute_CLoad_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CLLC[preserves_invariantI]:
  "runs_preserve_invariant (execute_CLLC arg0 arg1)"
  unfolding execute_CLLC_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CLCBI[preserves_invariantI]:
  "runs_preserve_invariant (execute_CLCBI arg0 arg1 arg2)"
  unfolding execute_CLCBI_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CLC[preserves_invariantI]:
  "runs_preserve_invariant (execute_CLC arg0 arg1 arg2 arg3)"
  unfolding execute_CLC_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CJALR[preserves_invariantI]:
  "runs_preserve_invariant (execute_CJALR arg0 arg1 arg2)"
  unfolding execute_CJALR_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CIncOffsetImmediate[preserves_invariantI]:
  "runs_preserve_invariant (execute_CIncOffsetImmediate arg0 arg1 arg2)"
  unfolding execute_CIncOffsetImmediate_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CIncOffset[preserves_invariantI]:
  "runs_preserve_invariant (execute_CIncOffset arg0 arg1 arg2)"
  unfolding execute_CIncOffset_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetType[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetType arg0 arg1)"
  unfolding execute_CGetType_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetTag[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetTag arg0 arg1)"
  unfolding execute_CGetTag_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetSealed[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetSealed arg0 arg1)"
  unfolding execute_CGetSealed_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetPerm[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetPerm arg0 arg1)"
  unfolding execute_CGetPerm_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetPCCSetOffset[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetPCCSetOffset arg0 arg1)"
  unfolding execute_CGetPCCSetOffset_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetPCC[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetPCC arg0)"
  unfolding execute_CGetPCC_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetOffset[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetOffset arg0 arg1)"
  unfolding execute_CGetOffset_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetLen[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetLen arg0 arg1)"
  unfolding execute_CGetLen_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetFlags[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetFlags arg0 arg1)"
  unfolding execute_CGetFlags_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetCause[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetCause arg0)"
  unfolding execute_CGetCause_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetCID[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetCID arg0)"
  unfolding execute_CGetCID_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetBase[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetBase arg0 arg1)"
  unfolding execute_CGetBase_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetAndAddr[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetAndAddr arg0 arg1 arg2)"
  unfolding execute_CGetAndAddr_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CGetAddr[preserves_invariantI]:
  "runs_preserve_invariant (execute_CGetAddr arg0 arg1)"
  unfolding execute_CGetAddr_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CFromPtr[preserves_invariantI]:
  "runs_preserve_invariant (execute_CFromPtr arg0 arg1 arg2)"
  unfolding execute_CFromPtr_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CCopyType[preserves_invariantI]:
  "runs_preserve_invariant (execute_CCopyType arg0 arg1 arg2)"
  unfolding execute_CCopyType_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CClearTag[preserves_invariantI]:
  "runs_preserve_invariant (execute_CClearTag arg0 arg1)"
  unfolding execute_CClearTag_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CCheckType[preserves_invariantI]:
  "runs_preserve_invariant (execute_CCheckType arg0 arg1)"
  unfolding execute_CCheckType_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CCheckTag[preserves_invariantI]:
  "runs_preserve_invariant (execute_CCheckTag arg0)"
  unfolding execute_CCheckTag_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CCheckPerm[preserves_invariantI]:
  "runs_preserve_invariant (execute_CCheckPerm arg0 arg1)"
  unfolding execute_CCheckPerm_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CCall[preserves_invariantI]:
  "runs_preserve_invariant (execute_CCall arg0 arg1 arg2)"
  unfolding execute_CCall_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CCSeal[preserves_invariantI]:
  "runs_preserve_invariant (execute_CCSeal arg0 arg1 arg2)"
  unfolding execute_CCSeal_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CBuildCap[preserves_invariantI]:
  "runs_preserve_invariant (execute_CBuildCap arg0 arg1 arg2)"
  unfolding execute_CBuildCap_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CBZ[preserves_invariantI]:
  "runs_preserve_invariant (execute_CBZ arg0 arg1 arg2)"
  unfolding execute_CBZ_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CBX[preserves_invariantI]:
  "runs_preserve_invariant (execute_CBX arg0 arg1 arg2)"
  unfolding execute_CBX_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CAndPerm[preserves_invariantI]:
  "runs_preserve_invariant (execute_CAndPerm arg0 arg1 arg2)"
  unfolding execute_CAndPerm_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CAndAddr[preserves_invariantI]:
  "runs_preserve_invariant (execute_CAndAddr arg0 arg1 arg2)"
  unfolding execute_CAndAddr_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_CACHE[preserves_invariantI]:
  "runs_preserve_invariant (execute_CACHE arg0 arg1 arg2)"
  unfolding execute_CACHE_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_BREAK[preserves_invariantI]:
  "runs_preserve_invariant (execute_BREAK arg0)"
  unfolding execute_BREAK_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_BEQ[preserves_invariantI]:
  "runs_preserve_invariant (execute_BEQ arg0 arg1 arg2 arg3 arg4)"
  unfolding execute_BEQ_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_BCMPZ[preserves_invariantI]:
  "runs_preserve_invariant (execute_BCMPZ arg0 arg1 arg2 arg3 arg4)"
  unfolding execute_BCMPZ_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_ANDI[preserves_invariantI]:
  "runs_preserve_invariant (execute_ANDI arg0 arg1 arg2)"
  unfolding execute_ANDI_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_AND[preserves_invariantI]:
  "runs_preserve_invariant (execute_AND arg0 arg1 arg2)"
  unfolding execute_AND_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_ADDU[preserves_invariantI]:
  "runs_preserve_invariant (execute_ADDU arg0 arg1 arg2)"
  unfolding execute_ADDU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_ADDIU[preserves_invariantI]:
  "runs_preserve_invariant (execute_ADDIU arg0 arg1 arg2)"
  unfolding execute_ADDIU_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_ADDI[preserves_invariantI]:
  "runs_preserve_invariant (execute_ADDI arg0 arg1 arg2)"
  unfolding execute_ADDI_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute_ADD[preserves_invariantI]:
  "runs_preserve_invariant (execute_ADD arg0 arg1 arg2)"
  unfolding execute_ADD_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_execute[preserves_invariantI]:
  "runs_preserve_invariant (execute instr)"
  by (cases instr rule: execute.cases; simp; preserves_invariantI)

lemma traces_enabled_write_cap_regs[traces_enabledI]:
  assumes "c \<in> derivable_caps s"
  shows "traces_enabled (write_reg C01_ref c) s regs"
    and "traces_enabled (write_reg C02_ref c) s regs"
    and "traces_enabled (write_reg C03_ref c) s regs"
    and "traces_enabled (write_reg C04_ref c) s regs"
    and "traces_enabled (write_reg C05_ref c) s regs"
    and "traces_enabled (write_reg C06_ref c) s regs"
    and "traces_enabled (write_reg C07_ref c) s regs"
    and "traces_enabled (write_reg C08_ref c) s regs"
    and "traces_enabled (write_reg C09_ref c) s regs"
    and "traces_enabled (write_reg C10_ref c) s regs"
    and "traces_enabled (write_reg C11_ref c) s regs"
    and "traces_enabled (write_reg C12_ref c) s regs"
    and "traces_enabled (write_reg C13_ref c) s regs"
    and "traces_enabled (write_reg C14_ref c) s regs"
    and "traces_enabled (write_reg C15_ref c) s regs"
    and "traces_enabled (write_reg C16_ref c) s regs"
    and "traces_enabled (write_reg C17_ref c) s regs"
    and "traces_enabled (write_reg C18_ref c) s regs"
    and "traces_enabled (write_reg C19_ref c) s regs"
    and "traces_enabled (write_reg C20_ref c) s regs"
    and "traces_enabled (write_reg C21_ref c) s regs"
    and "traces_enabled (write_reg C22_ref c) s regs"
    and "traces_enabled (write_reg C23_ref c) s regs"
    and "traces_enabled (write_reg C24_ref c) s regs"
    and "traces_enabled (write_reg C25_ref c) s regs"
    and "traces_enabled (write_reg C26_ref c) s regs"
    and "traces_enabled (write_reg C27_ref c) s regs"
    and "traces_enabled (write_reg C28_ref c) s regs"
    and "traces_enabled (write_reg C29_ref c) s regs"
    and "traces_enabled (write_reg C30_ref c) s regs"
    and "traces_enabled (write_reg C31_ref c) s regs"
    and "traces_enabled (write_reg CPLR_ref c) s regs"
    and "traces_enabled (write_reg CULR_ref c) s regs"
    and "traces_enabled (write_reg DDC_ref c) s regs"
    and "traces_enabled (write_reg DelayedPCC_ref c) s regs"
    and "traces_enabled (write_reg EPCC_ref c) s regs"
    and "traces_enabled (write_reg ErrorEPCC_ref c) s regs"
    and "traces_enabled (write_reg KCC_ref c) s regs"
    and "traces_enabled (write_reg KDC_ref c) s regs"
    and "traces_enabled (write_reg KR1C_ref c) s regs"
    and "traces_enabled (write_reg KR2C_ref c) s regs"
    and "\<And>c. traces_enabled (write_reg CapCause_ref c) s regs"
    and "traces_enabled (write_reg NextPCC_ref c) s regs"
    and "traces_enabled (write_reg PCC_ref c) s regs"
  using assms
  by (intro traces_enabled_write_reg; auto simp: register_defs derivable_caps_def)+

lemma traces_enabled_read_cap_regs[traces_enabledI]:
  "traces_enabled (read_reg C01_ref) s regs"
  "traces_enabled (read_reg C02_ref) s regs"
  "traces_enabled (read_reg C03_ref) s regs"
  "traces_enabled (read_reg C04_ref) s regs"
  "traces_enabled (read_reg C05_ref) s regs"
  "traces_enabled (read_reg C06_ref) s regs"
  "traces_enabled (read_reg C07_ref) s regs"
  "traces_enabled (read_reg C08_ref) s regs"
  "traces_enabled (read_reg C09_ref) s regs"
  "traces_enabled (read_reg C10_ref) s regs"
  "traces_enabled (read_reg C11_ref) s regs"
  "traces_enabled (read_reg C12_ref) s regs"
  "traces_enabled (read_reg C13_ref) s regs"
  "traces_enabled (read_reg C14_ref) s regs"
  "traces_enabled (read_reg C15_ref) s regs"
  "traces_enabled (read_reg C16_ref) s regs"
  "traces_enabled (read_reg C17_ref) s regs"
  "traces_enabled (read_reg C18_ref) s regs"
  "traces_enabled (read_reg C19_ref) s regs"
  "traces_enabled (read_reg C20_ref) s regs"
  "traces_enabled (read_reg C21_ref) s regs"
  "traces_enabled (read_reg C22_ref) s regs"
  "traces_enabled (read_reg C23_ref) s regs"
  "traces_enabled (read_reg C24_ref) s regs"
  "traces_enabled (read_reg C25_ref) s regs"
  "traces_enabled (read_reg C26_ref) s regs"
  "traces_enabled (read_reg C27_ref) s regs"
  "traces_enabled (read_reg C28_ref) s regs"
  "traces_enabled (read_reg C29_ref) s regs"
  "traces_enabled (read_reg C30_ref) s regs"
  "traces_enabled (read_reg C31_ref) s regs"
  "system_reg_access s \<or> ex_traces \<Longrightarrow> traces_enabled (read_reg CPLR_ref) s regs"
  "traces_enabled (read_reg CULR_ref) s regs"
  "traces_enabled (read_reg DDC_ref) s regs"
  "traces_enabled (read_reg DelayedPCC_ref) s regs"
  "system_reg_access s \<or> ex_traces \<Longrightarrow> traces_enabled (read_reg EPCC_ref) s regs"
  "system_reg_access s \<or> ex_traces \<Longrightarrow> traces_enabled (read_reg ErrorEPCC_ref) s regs"
  "system_reg_access s \<or> ex_traces \<Longrightarrow> traces_enabled (read_reg KCC_ref) s regs"
  "system_reg_access s \<or> ex_traces \<Longrightarrow> traces_enabled (read_reg KDC_ref) s regs"
  "system_reg_access s \<or> ex_traces \<Longrightarrow> traces_enabled (read_reg KR1C_ref) s regs"
  "system_reg_access s \<or> ex_traces \<Longrightarrow> traces_enabled (read_reg KR2C_ref) s regs"
  "system_reg_access s \<or> ex_traces \<Longrightarrow> traces_enabled (read_reg CapCause_ref) s regs"
  "traces_enabled (read_reg NextPCC_ref) s regs"
  "traces_enabled (read_reg PCC_ref) s regs"
  by (intro traces_enabled_read_reg; auto simp: register_defs)+

(*lemma preserves_invariant_init_cp2_state[preserves_invariantI]:
  shows "traces_preserve_invariant (init_cp2_state arg0)"
  unfolding init_cp2_state_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_cp2_next_pc[preserves_invariantI]:
  shows "traces_preserve_invariant (cp2_next_pc arg0)"
  unfolding cp2_next_pc_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_initialize_registers[preserves_invariantI]:
  shows "traces_preserve_invariant (initialize_registers arg0)"
  unfolding initialize_registers_def bind_assoc
  by (preserves_invariantI)*)

lemma read_cap_regs_derivable[derivable_capsE]:
  "\<And>t c regs s. Run_inv (read_reg C01_ref) t c regs \<Longrightarrow> {''C01''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C02_ref) t c regs \<Longrightarrow> {''C02''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C03_ref) t c regs \<Longrightarrow> {''C03''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C04_ref) t c regs \<Longrightarrow> {''C04''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C05_ref) t c regs \<Longrightarrow> {''C05''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C06_ref) t c regs \<Longrightarrow> {''C06''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C07_ref) t c regs \<Longrightarrow> {''C07''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C08_ref) t c regs \<Longrightarrow> {''C08''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C09_ref) t c regs \<Longrightarrow> {''C09''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C10_ref) t c regs \<Longrightarrow> {''C10''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C11_ref) t c regs \<Longrightarrow> {''C11''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C12_ref) t c regs \<Longrightarrow> {''C12''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C13_ref) t c regs \<Longrightarrow> {''C13''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C14_ref) t c regs \<Longrightarrow> {''C14''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C15_ref) t c regs \<Longrightarrow> {''C15''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C16_ref) t c regs \<Longrightarrow> {''C16''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C17_ref) t c regs \<Longrightarrow> {''C17''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C18_ref) t c regs \<Longrightarrow> {''C18''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C19_ref) t c regs \<Longrightarrow> {''C19''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C20_ref) t c regs \<Longrightarrow> {''C20''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C21_ref) t c regs \<Longrightarrow> {''C21''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C22_ref) t c regs \<Longrightarrow> {''C22''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C23_ref) t c regs \<Longrightarrow> {''C23''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C24_ref) t c regs \<Longrightarrow> {''C24''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C25_ref) t c regs \<Longrightarrow> {''C25''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C26_ref) t c regs \<Longrightarrow> {''C26''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C27_ref) t c regs \<Longrightarrow> {''C27''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C28_ref) t c regs \<Longrightarrow> {''C28''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C29_ref) t c regs \<Longrightarrow> {''C29''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C30_ref) t c regs \<Longrightarrow> {''C30''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg C31_ref) t c regs \<Longrightarrow> {''C31''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg CPLR_ref) t c regs \<Longrightarrow> {''CPLR''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg CULR_ref) t c regs \<Longrightarrow> {''CULR''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg DDC_ref) t c regs \<Longrightarrow> {''DDC''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg DelayedPCC_ref) t c regs \<Longrightarrow> {''DelayedPCC''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg EPCC_ref) t c regs \<Longrightarrow> {''EPCC''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg ErrorEPCC_ref) t c regs \<Longrightarrow> {''ErrorEPCC''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg KCC_ref) t c regs \<Longrightarrow> {''KCC''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg KDC_ref) t c regs \<Longrightarrow> {''KDC''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg KR1C_ref) t c regs \<Longrightarrow> {''KR1C''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg KR2C_ref) t c regs \<Longrightarrow> {''KR2C''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg NextPCC_ref) t c regs \<Longrightarrow> {''NextPCC''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  "\<And>t c regs s. Run_inv (read_reg PCC_ref) t c regs \<Longrightarrow> {''PCC''} \<subseteq> accessible_regs s \<Longrightarrow> c \<in> derivable_caps (run s t)"
  unfolding C01_ref_def C02_ref_def C03_ref_def C04_ref_def C05_ref_def
     C06_ref_def C07_ref_def C08_ref_def C09_ref_def C10_ref_def
     C11_ref_def C12_ref_def C13_ref_def C14_ref_def C15_ref_def
     C16_ref_def C17_ref_def C18_ref_def C19_ref_def C20_ref_def
     C21_ref_def C22_ref_def C23_ref_def C24_ref_def C25_ref_def
     C26_ref_def C27_ref_def C28_ref_def C29_ref_def C30_ref_def
     C31_ref_def CPLR_ref_def CULR_ref_def DDC_ref_def DelayedPCC_ref_def
     EPCC_ref_def ErrorEPCC_ref_def KCC_ref_def KDC_ref_def KR1C_ref_def
     KR2C_ref_def NextPCC_ref_def PCC_ref_def Run_inv_def derivable_caps_def
  by (auto elim!: Run_read_regE intro!: derivable.Copy)


end

context CHERI_MIPS_Reg_Automaton
begin

lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]


lemma traces_enabled_MIPS_write[traces_enabledI]:
  shows "traces_enabled (MIPS_write arg0 arg1 arg2) s regs"
  unfolding MIPS_write_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MIPS_read[traces_enabledI]:
  shows "traces_enabled (MIPS_read arg0 arg1) s regs"
  unfolding MIPS_read_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MEMr[traces_enabledI]:
  shows "traces_enabled (MEMr arg0 arg1) s regs"
  unfolding MEMr_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MEMr_reserve[traces_enabledI]:
  shows "traces_enabled (MEMr_reserve arg0 arg1) s regs"
  unfolding MEMr_reserve_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MEMea[traces_enabledI]:
  shows "traces_enabled (MEMea arg0 arg1) s regs"
  unfolding MEMea_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MEMea_conditional[traces_enabledI]:
  shows "traces_enabled (MEMea_conditional arg0 arg1) s regs"
  unfolding MEMea_conditional_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MEMval[traces_enabledI]:
  shows "traces_enabled (MEMval arg0 arg1 arg2) s regs"
  unfolding MEMval_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MEMval_conditional[traces_enabledI]:
  shows "traces_enabled (MEMval_conditional arg0 arg1 arg2) s regs"
  unfolding MEMval_conditional_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_set_next_pcc[traces_enabledI]:
  assumes "arg0 \<in> derivable_caps s"
  shows "traces_enabled (set_next_pcc arg0) s regs"
  unfolding set_next_pcc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma Run_inv_read_reg_PCC_not_sealed:
  assumes "Run_inv (read_reg PCC_ref) t c regs"
  shows "Capability_sealed c = False"
  using assms
  unfolding Run_inv_def
  by (auto elim!: Run_read_regE simp: PCC_ref_def get_regval_def regval_of_Capability_def)

lemma traces_enabled_SignalException[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SignalException arg0) s regs"
proof cases
  assume ex: "ex_traces"
  note [derivable_capsE] = read_reg_KCC_exception_targets
  show ?thesis
    unfolding SignalException_def bind_assoc
    by (traces_enabledI assms: assms intro: traces_enabled_set_next_pcc_ex ex simp: Run_inv_read_reg_PCC_not_sealed)
next
  assume "\<not>ex_traces"
  then show ?thesis
    unfolding traces_enabled_def finished_def isException_def
    by auto
qed

lemma traces_enabled_SignalExceptionBadAddr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SignalExceptionBadAddr arg0 arg1) s regs"
  unfolding SignalExceptionBadAddr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_SignalExceptionTLB[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (SignalExceptionTLB arg0 arg1) s regs"
  unfolding SignalExceptionTLB_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_pcc_access_system_regs[traces_enabledI]:
  shows "traces_enabled (pcc_access_system_regs arg0) s regs"
  unfolding pcc_access_system_regs_def bind_assoc
  by (traces_enabledI)

lemma Run_raise_c2_exception8_False[simp]: "Run (raise_c2_exception8 arg0 arg1) t a \<longleftrightarrow> False"
  unfolding raise_c2_exception8_def
  by (auto elim!: Run_bindE)

lemma traces_enabled_raise_c2_exception8[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (raise_c2_exception8 arg0 arg1) s regs"
proof cases
  assume ex: "ex_traces"
  have set_ExcCode: "traces_enabled (set_CapCauseReg_ExcCode CapCause_ref exc) s regs" for exc s regs
    unfolding set_CapCauseReg_ExcCode_def
    by (traces_enabledI intro: traces_enabled_read_reg traces_enabled_write_reg ex simp: CapCause_ref_def)
  have set_RegNum: "traces_enabled (set_CapCauseReg_RegNum CapCause_ref r) s regs" for r s regs
    unfolding set_CapCauseReg_RegNum_def
    by (traces_enabledI intro: traces_enabled_read_reg traces_enabled_write_reg ex simp: CapCause_ref_def)
  show ?thesis
    unfolding raise_c2_exception8_def bind_assoc
    by (traces_enabledI intro: set_ExcCode set_RegNum assms: assms simp: CapCause_ref_def)
next
  assume "\<not>ex_traces"
  then show ?thesis
    unfolding traces_enabled_def finished_def isException_def
    by auto
qed

lemma traces_enabled_raise_c2_exception_noreg[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (raise_c2_exception_noreg arg0) s regs"
  unfolding raise_c2_exception_noreg_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_checkCP0AccessHook[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (checkCP0AccessHook arg0) s regs"
  unfolding checkCP0AccessHook_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_checkCP0Access[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (checkCP0Access arg0) s regs"
  unfolding checkCP0Access_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_incrementCP0Count[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (incrementCP0Count arg0) s regs"
  unfolding incrementCP0Count_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr_wrapper[traces_enabledI]:
  shows "traces_enabled (MEMr_wrapper arg0 arg1) s regs"
  unfolding MEMr_wrapper_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MEMr_reserve_wrapper[traces_enabledI]:
  shows "traces_enabled (MEMr_reserve_wrapper arg0 arg1) s regs"
  unfolding MEMr_reserve_wrapper_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_TLBTranslate2[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TLBTranslate2 arg0 arg1) s regs"
  unfolding TLBTranslate2_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TLBTranslateC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TLBTranslateC arg0 arg1) s regs"
  unfolding TLBTranslateC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TLBTranslate[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TLBTranslate arg0 arg1) s regs"
  unfolding TLBTranslate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_branch_pcc[traces_enabledI]:
  assumes "arg0 \<in> derivable_caps s"
  shows "traces_enabled (execute_branch_pcc arg0) s regs"
  unfolding execute_branch_pcc_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_ERETHook[traces_enabledI]:
  assumes "{''EPCC'', ''ErrorEPCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (ERETHook arg0) s regs"
  unfolding ERETHook_def bind_assoc
  by (traces_enabledI assms: assms simp: accessible_regs_def)

lemma traces_enabled_raise_c2_exception[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (raise_c2_exception arg0 arg1) s regs"
  unfolding raise_c2_exception_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr_tagged[traces_enabledI]:
  shows "traces_enabled (MEMr_tagged arg0 arg1 arg2) s regs"
  unfolding MEMr_tagged_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MEMr_tagged_reserve[traces_enabledI]:
  shows "traces_enabled (MEMr_tagged_reserve arg0 arg1 arg2) s regs"
  unfolding MEMr_tagged_reserve_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MEMw_tagged[traces_enabledI]:
  assumes "memBitsToCapability tag (ucast v) \<in> derivable_caps s"
  shows "traces_enabled (MEMw_tagged addr sz tag v) s regs"
  unfolding MEMw_tagged_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMw_tagged_conditional[traces_enabledI]:
  assumes "memBitsToCapability tag (ucast v) \<in> derivable_caps s"
  shows "traces_enabled (MEMw_tagged_conditional addr sz tag v) s regs"
  unfolding MEMw_tagged_conditional_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMw_wrapper[traces_enabledI]:
  shows "traces_enabled (MEMw_wrapper arg0 arg1 arg2) s regs"
  unfolding MEMw_wrapper_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MEMw_conditional_wrapper[traces_enabledI]:
  shows "traces_enabled (MEMw_conditional_wrapper arg0 arg1 arg2) s regs"
  unfolding MEMw_conditional_wrapper_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_checkDDCPerms[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "arg0 \<in> derivable_caps s"
  shows "traces_enabled (checkDDCPerms arg0 arg1) s regs"
  unfolding checkDDCPerms_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_addrWrapper[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (addrWrapper arg0 arg1 arg2) s regs"
  unfolding addrWrapper_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_addrWrapperUnaligned[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (addrWrapperUnaligned arg0 arg1 arg2) s regs"
  unfolding addrWrapperUnaligned_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_branch[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_branch arg0) s regs"
  unfolding execute_branch_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_TranslatePC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TranslatePC arg0) s regs"
  unfolding TranslatePC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_checkCP2usable[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (checkCP2usable arg0) s regs"
  unfolding checkCP2usable_def bind_assoc
  by (traces_enabledI assms: assms)

(*lemma traces_enabled_init_cp2_state[traces_enabledI]:
  shows "traces_enabled (init_cp2_state arg0) s regs"
  unfolding init_cp2_state_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_cp2_next_pc[traces_enabledI]:
  assumes "{''DelayedPCC'', ''NextPCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (cp2_next_pc arg0) s regs"
  unfolding cp2_next_pc_def bind_assoc
  by (traces_enabledI assms: assms)*)

lemma traces_enabled_get_CP0EPC[traces_enabledI]:
  assumes "{''EPCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (get_CP0EPC arg0) s regs"
  unfolding get_CP0EPC_def bind_assoc
  by (traces_enabledI assms: assms simp: accessible_regs_def)

lemma if_derivable_caps[derivable_capsI]:
  assumes "c \<Longrightarrow> c1 \<in> derivable_caps s" and "\<not>c \<Longrightarrow> c2 \<in> derivable_caps s"
  shows "(if c then c1 else c2) \<in> derivable_caps s"
  using assms
  by auto

lemma traces_enabled_set_CP0EPC[traces_enabledI]:
  assumes "{''EPCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (set_CP0EPC arg0) s regs"
  unfolding set_CP0EPC_def bind_assoc
  by (traces_enabledI assms: assms simp: accessible_regs_def)

lemma traces_enabled_get_CP0ErrorEPC[traces_enabledI]:
  assumes "{''ErrorEPCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (get_CP0ErrorEPC arg0) s regs"
  unfolding get_CP0ErrorEPC_def bind_assoc
  by (traces_enabledI assms: assms simp: accessible_regs_def)

lemma traces_enabled_set_CP0ErrorEPC[traces_enabledI]:
  assumes "{''ErrorEPCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (set_CP0ErrorEPC arg0) s regs"
  unfolding set_CP0ErrorEPC_def bind_assoc
  by (traces_enabledI assms: assms simp: accessible_regs_def system_reg_access_run)

(*lemma traces_enabled_dump_cp2_state[traces_enabledI]:
  assumes "{''CPLR'', ''CULR'', ''DDC'', ''EPCC'', ''ErrorEPCC'', ''KCC'', ''KDC'', ''KR1C'', ''KR2C'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (dump_cp2_state arg0) s regs"
  unfolding dump_cp2_state_def bind_assoc
  by (traces_enabledI assms: assms)*)

lemma traces_enabled_TLBWriteEntry[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (TLBWriteEntry arg0) s regs"
  unfolding TLBWriteEntry_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_WAIT[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_WAIT arg0) s regs"
  unfolding execute_WAIT_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_TRAPREG[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_TRAPREG arg0 arg1 arg2) s regs"
  unfolding execute_TRAPREG_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_TRAPIMM[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_TRAPIMM arg0 arg1 arg2) s regs"
  unfolding execute_TRAPIMM_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_TLBWR[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_TLBWR arg0) s regs"
  unfolding execute_TLBWR_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_TLBWI[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_TLBWI arg0) s regs"
  unfolding execute_TLBWI_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_TLBR[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_TLBR arg0) s regs"
  unfolding execute_TLBR_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_TLBP[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_TLBP arg0) s regs"
  unfolding execute_TLBP_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_Store[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_Store arg0 arg1 arg2 arg3 arg4) s regs"
  unfolding execute_Store_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SYSCALL[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_SYSCALL arg0) s regs"
  unfolding execute_SYSCALL_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SWR[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_SWR arg0 arg1 arg2) s regs"
  unfolding execute_SWR_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SWL[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_SWL arg0 arg1 arg2) s regs"
  unfolding execute_SWL_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SUB[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_SUB arg0 arg1 arg2) s regs"
  unfolding execute_SUB_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SDR[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_SDR arg0 arg1 arg2) s regs"
  unfolding execute_SDR_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_SDL[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_SDL arg0 arg1 arg2) s regs"
  unfolding execute_SDL_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_RI[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_RI arg0) s regs"
  unfolding execute_RI_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_RDHWR[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_RDHWR arg0 arg1) s regs"
  unfolding execute_RDHWR_def bind_assoc
  by (traces_enabledI assms: assms)

lemma Run_inv_pcc_access_system_regs_accessible_regs:
  assumes "Run_inv (pcc_access_system_regs u) t a regs" and "a"
    and "Rs \<inter> written_regs s = {}" and "{''PCC''} \<subseteq> accessible_regs s"
  shows "Rs \<subseteq> accessible_regs (run s t)"
  using assms
  by (auto simp: accessible_regs_def system_reg_access_run pcc_access_system_regs_allows_system_reg_access
                 runs_no_reg_writes_written_regs_eq no_reg_writes_runs_no_reg_writes)

lemmas Run_inv_pcc_access_system_regs_privileged_regs_accessible[accessible_regsE] =
  Run_inv_pcc_access_system_regs_accessible_regs[where Rs = "{''KCC''}"]
  Run_inv_pcc_access_system_regs_accessible_regs[where Rs = "{''KDC''}"]
  Run_inv_pcc_access_system_regs_accessible_regs[where Rs = "{''EPCC''}"]
  Run_inv_pcc_access_system_regs_accessible_regs[where Rs = "{''ErrorEPCC''}"]
  Run_inv_pcc_access_system_regs_accessible_regs[where Rs = "{''KR1C''}"]
  Run_inv_pcc_access_system_regs_accessible_regs[where Rs = "{''KR2C''}"]
  Run_inv_pcc_access_system_regs_accessible_regs[where Rs = "{''CapCause''}"]
  Run_inv_pcc_access_system_regs_accessible_regs[where Rs = "{''CPLR''}"]

lemma Run_inv_SignalException_False[simp]: "Run_inv (SignalException exc) t a regs \<longleftrightarrow> False"
  unfolding Run_inv_def
  by auto

lemma Run_inv_checkCP0Access_accessible_regs:
  assumes "Run_inv (checkCP0Access u) t a regs"
    and "Rs \<inter> written_regs s = {}" and "{''PCC''} \<subseteq> accessible_regs s"
  shows "Rs \<subseteq> accessible_regs (run s t)"
  using assms
  unfolding checkCP0Access_def checkCP0AccessHook_def bind_assoc
  by (auto elim!: Run_inv_bindE intro!: preserves_invariantI traces_runs_preserve_invariantI split: if_splits simp: CP0Cause_ref_def)
     (auto simp: accessible_regs_def runs_no_reg_writes_written_regs_eq no_reg_writes_runs_no_reg_writes system_reg_access_run pcc_access_system_regs_allows_system_reg_access)

lemmas Run_inv_checkCP0Access_privileged_regs_accessible[accessible_regsE] =
  Run_inv_checkCP0Access_accessible_regs[where Rs = "{''KCC''}"]
  Run_inv_checkCP0Access_accessible_regs[where Rs = "{''KDC''}"]
  Run_inv_checkCP0Access_accessible_regs[where Rs = "{''EPCC''}"]
  Run_inv_checkCP0Access_accessible_regs[where Rs = "{''ErrorEPCC''}"]
  Run_inv_checkCP0Access_accessible_regs[where Rs = "{''KR1C''}"]
  Run_inv_checkCP0Access_accessible_regs[where Rs = "{''KR2C''}"]
  Run_inv_checkCP0Access_accessible_regs[where Rs = "{''CapCause''}"]
  Run_inv_checkCP0Access_accessible_regs[where Rs = "{''CPLR''}"]

lemma Run_inv_no_reg_writes_written_regs[accessible_regsE]:
  assumes "Run_inv m t a regs"
    and "runs_no_reg_writes_to Rs m" and "Rs \<inter> written_regs s = {}"
  shows "Rs \<inter> written_regs (run s t) = {}"
  using assms
  by (auto simp: runs_no_reg_writes_written_regs_eq runs_no_reg_writes_to_def)

lemma Run_inv_assert_exp_iff[iff]:
  "Run_inv (assert_exp c msg) t a regs \<longleftrightarrow> c \<and> t = [] \<and> invariant regs"
  unfolding Run_inv_def
  by auto

lemma throw_bind_eq[simp]: "(throw e \<bind> m) = throw e"
  by (auto simp: throw_def)

lemma SignalException_bind_eq[simp]: "(SignalException ex \<bind> m) = SignalException ex"
  unfolding SignalException_def Let_def bind_assoc throw_bind_eq ..

lemma runs_no_reg_writes_to_checkCP2usable[runs_no_reg_writes_toI, simp]:
  shows "runs_no_reg_writes_to Rs (checkCP2usable u)"
  unfolding checkCP2usable_def runs_no_reg_writes_to_def
  by (auto elim!: Run_bindE Run_read_regE split: if_splits)

lemma traces_enabled_execute_MTC0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "{''EPCC'', ''ErrorEPCC''} \<inter> written_regs s = {}"
  shows "traces_enabled (execute_MTC0 arg0 arg1 arg2 arg3) s regs"
  unfolding execute_MTC0_def bind_assoc
  by (intro traces_enabled_if_ignore_cond traces_enabledI preserves_invariantI traces_runs_preserve_invariantI; accessible_regsI assms: assms)

lemma traces_enabled_execute_MFC0[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "{''EPCC'', ''ErrorEPCC''} \<inter> written_regs s = {}"
  shows "traces_enabled (execute_MFC0 arg0 arg1 arg2 arg3) s regs"
  unfolding execute_MFC0_def bind_assoc
  by (intro traces_enabled_if_ignore_cond traces_enabledI preserves_invariantI traces_runs_preserve_invariantI conjI allI impI; accessible_regsI assms: assms)

lemma traces_enabled_execute_Load[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_Load arg0 arg1 arg2 arg3 arg4 arg5) s regs"
  unfolding execute_Load_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LWR[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_LWR arg0 arg1 arg2) s regs"
  unfolding execute_LWR_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LWL[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_LWL arg0 arg1 arg2) s regs"
  unfolding execute_LWL_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDR[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_LDR arg0 arg1 arg2) s regs"
  unfolding execute_LDR_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_LDL[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_LDL arg0 arg1 arg2) s regs"
  unfolding execute_LDL_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_JR[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_JR arg0) s regs"
  unfolding execute_JR_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_JALR[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_JALR arg0 arg1) s regs"
  unfolding execute_JALR_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_JAL[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_JAL arg0) s regs"
  unfolding execute_JAL_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_J[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_J arg0) s regs"
  unfolding execute_J_def bind_assoc
  by (traces_enabledI assms: assms)

lemma runs_no_reg_writes_to_checkCP0Access[runs_no_reg_writes_toI, simp]:
  "runs_no_reg_writes_to Rs (checkCP0Access u)"
  using no_reg_writes_to_pcc_access_system_regs no_reg_writes_to_getAccessLevel no_reg_writes_to_read_reg[where r = CP0Status_ref]
  unfolding checkCP0Access_def checkCP0AccessHook_def runs_no_reg_writes_to_def no_reg_writes_to_def and_boolM_def
  by (fastforce elim!: Run_bindE split: if_splits)

lemma traces_enabled_execute_ERET[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "{''EPCC'', ''ErrorEPCC''} \<inter> written_regs s = {}"
  shows "traces_enabled (execute_ERET arg0) s regs"
  unfolding execute_ERET_def bind_assoc
  by (traces_enabledI assms: assms checkCP0Access_system_reg_access simp: accessible_regs_def runs_no_reg_writes_written_regs_eq no_reg_writes_runs_no_reg_writes system_reg_access_run)

lemma traces_enabled_execute_DSUB[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_DSUB arg0 arg1 arg2) s regs"
  unfolding execute_DSUB_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_DADDI[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_DADDI arg0 arg1 arg2) s regs"
  unfolding execute_DADDI_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_DADD[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_DADD arg0 arg1 arg2) s regs"
  unfolding execute_DADD_def bind_assoc
  by (traces_enabledI assms: assms)

declare traces_enabled_foreachM_inv[where P = "\<lambda>_ _ _. True", traces_enabledI]

lemma traces_enabled_execute_ClearRegs[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_ClearRegs arg0 arg1) s regs"
  unfolding execute_ClearRegs_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CWriteHwr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CWriteHwr arg0 arg1) s regs"
  unfolding execute_CWriteHwr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma unsealCap_derivable_caps[derivable_capsI]:
  assumes "c \<in> derivable_caps s" and "c' \<in> derivable_caps s"
    and "Capability_tag c" and "Capability_tag c'"
    and "Capability_sealed c" and "\<not>Capability_sealed c'"
    and "Capability_permit_unseal c'"
    and "getCapCursor c' = uint (Capability_otype c)"
  shows "(unsealCap c)\<lparr>Capability_global := Capability_global c \<and> Capability_global c'\<rparr> \<in> derivable_caps s"
    (is "?unseal c c' \<in> derivable_caps s")
proof -
  have "unseal CC c (get_global_method CC c') \<in> derivable (accessed_caps s)"
    using assms
    by (intro derivable.Unseal) (auto simp: derivable_caps_def unat_def[symmetric] get_cap_perms_def)
  then have "?unseal c c' \<in> derivable (accessed_caps s)"
    by (elim derivable.Restrict)
       (auto simp: leq_cap_def unseal_def unsealCap_def getCapBase_def getCapTop_def get_cap_perms_def)
  then show ?thesis
    by (auto simp: derivable_caps_def)
qed

lemma traces_enabled_execute_CUnseal[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CUnseal arg0 arg1 arg2) s regs"
  unfolding execute_CUnseal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CToPtr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CToPtr arg0 arg1 arg2) s regs"
  unfolding execute_CToPtr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CTestSubset[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CTestSubset arg0 arg1 arg2) s regs"
  unfolding execute_CTestSubset_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CSub[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CSub arg0 arg1 arg2) s regs"
  unfolding execute_CSub_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CStoreConditional[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CStoreConditional arg0 arg1 arg2 arg3) s regs"
  unfolding execute_CStoreConditional_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CStore[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CStore arg0 arg1 arg2 arg3 arg4) s regs"
  unfolding execute_CStore_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CSetOffset[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CSetOffset arg0 arg1 arg2) s regs"
  unfolding execute_CSetOffset_def bind_assoc
  by (traces_enabledI assms: assms)

lemma setCapFlags_derivable_caps[derivable_capsI]:
  assumes "c \<in> derivable_caps s"
  shows "setCapFlags c f \<in> derivable_caps s"
  using assms
  by (auto simp: setCapFlags_def)

lemma traces_enabled_execute_CSetFlags[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CSetFlags arg0 arg1 arg2) s regs"
  unfolding execute_CSetFlags_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_set_CapCauseReg_ExcCode:
  assumes "system_reg_access s \<or> ex_traces"
  shows "traces_enabled (set_CapCauseReg_ExcCode CapCause_ref exc) s regs"
  unfolding set_CapCauseReg_ExcCode_def
  by (traces_enabledI intro: traces_enabled_read_reg traces_enabled_write_reg simp: CapCause_ref_def assms: assms)

lemma traces_enabled_set_CapCauseReg_RegNum:
  assumes "system_reg_access s \<or> ex_traces"
  shows "traces_enabled (set_CapCauseReg_RegNum CapCause_ref exc) s regs"
  unfolding set_CapCauseReg_RegNum_def
  by (traces_enabledI intro: traces_enabled_read_reg traces_enabled_write_reg simp: CapCause_ref_def assms: assms)

lemma system_reg_access_run_ex_tracesI[accessible_regsI]:
  assumes "\<not>trace_allows_system_reg_access (accessible_regs s) t \<Longrightarrow> system_reg_access s \<or> ex_traces"
  shows "system_reg_access (run s t) \<or> ex_traces"
  using assms
  by (auto simp: system_reg_access_run)

lemma pcc_access_system_regs_allows_system_reg_access_ex_tracesI[accessible_regsE]:
  assumes "Run_inv (pcc_access_system_regs u) t a regs" and "a" and "{''PCC''} \<subseteq> accessible_regs s"
  shows "system_reg_access (run s t) \<or> ex_traces"
  using assms
  by (auto simp: system_reg_access_run pcc_access_system_regs_allows_system_reg_access)

lemma traces_enabled_execute_CSetCause[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CSetCause arg0) s regs"
  unfolding execute_CSetCause_def bind_assoc
  by (traces_enabledI assms: assms intro: traces_enabled_set_CapCauseReg_ExcCode traces_enabled_set_CapCauseReg_RegNum simp: CapCause_ref_def)

lemma traces_enabled_execute_CSetCID[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CSetCID arg0) s regs"
  unfolding execute_CSetCID_def bind_assoc
  by (traces_enabledI assms: assms)

lemma unat_add_nat_uint_add: "unat a + unat b = nat (uint a + uint b)"
  by (auto simp: unat_def nat_add_distrib)

lemma [simp]: "0 \<le> i \<Longrightarrow> nat i \<le> unat j \<longleftrightarrow> i \<le> uint j"
  by (auto simp: unat_def nat_le_eq_zle)

lemma setCapBounds_derivable_caps[derivable_capsE]:
  assumes "setCapBounds c b t = (e, c')"
    and "c \<in> derivable_caps s" and "\<not>Capability_sealed c"
    and "getCapBase c \<le> uint b" and "uint b \<le> uint t" and "uint t \<le> getCapTop c"
  shows "c' \<in> derivable_caps s"
proof -
  have "getCapTop c' \<le> uint t"
    using assms Divides.mod_less_eq_dividend[where a = "uint (t - ucast b)" and b = "2 ^ 64"]
    unfolding setCapBounds_def getCapTop_def getCapBase_def
    by (auto simp: uint_and_mask uint_sub_if_size)
  then have "leq_cap CC c' c"
    using assms
    by (auto simp: leq_cap_def setCapBounds_def getCapBase_def getCapTop_def nat_le_eq_zle get_cap_perms_def)
  from derivable.Restrict[OF _ this]
  show ?thesis
    using assms
    by (auto simp: derivable_caps_def setCapBounds_def)
qed

lemma to_bits_uint_ucast[simp]:
  "n = int (LENGTH('a)) \<Longrightarrow> to_bits n (uint w) = (ucast w::'a::len word)"
  by (auto simp: to_bits_def of_bl_bin_word_of_int ucast_def)

lemma to_bits_add[simp]:
  "n = int (LENGTH('a)) \<Longrightarrow> to_bits n (a + b) = (to_bits n a + to_bits n b :: 'a::len word)"
  by (auto simp: to_bits_def of_bl_bin_word_of_int wi_hom_syms)

lemma to_bits_64_getCapCursor[simp]: "to_bits 64 (getCapCursor c) = Capability_address c"
  by (auto simp: getCapCursor_def)

lemma traces_enabled_execute_CSetBoundsImmediate[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CSetBoundsImmediate arg0 arg1 arg2) s regs"
  unfolding execute_CSetBoundsImmediate_def bind_assoc
  by (traces_enabledI assms: assms simp: getCapCursor_def getCapTop_def)

lemma traces_enabled_execute_CSetBoundsExact[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CSetBoundsExact arg0 arg1 arg2) s regs"
  unfolding execute_CSetBoundsExact_def bind_assoc
  by (traces_enabledI assms: assms simp: getCapCursor_def getCapTop_def)

lemma traces_enabled_execute_CSetBounds[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CSetBounds arg0 arg1 arg2) s regs"
  unfolding execute_CSetBounds_def bind_assoc
  by (traces_enabledI assms: assms simp: getCapCursor_def getCapTop_def)

lemma setCapAddr_derivable_caps[derivable_capsE]:
  assumes "setCapAddr c a' = (success, c')"
    and "c \<in> derivable_caps s"
    and "Capability_tag c \<longrightarrow> \<not>Capability_sealed c"
  shows "c' \<in> derivable_caps s"
proof -
  have "leq_cap CC c' c" and "Capability_tag c' \<longleftrightarrow> Capability_tag c"
    using assms
    by (auto simp: setCapAddr_def leq_cap_def getCapBase_def getCapTop_def get_cap_perms_def)
  then show ?thesis
    using assms
    by (auto simp: derivable_caps_def elim: derivable.Restrict)
qed

lemma traces_enabled_execute_CSetAddr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CSetAddr arg0 arg1 arg2) s regs"
  unfolding execute_CSetAddr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma sealCap_derivable_caps[derivable_capsE]:
  assumes "sealCap c (to_bits 24 (getCapCursor c')) = (success, c'')"
    and "c \<in> derivable_caps s" and "c' \<in> derivable_caps s"
    and "Capability_tag c" and "Capability_tag c'"
    and "\<not>Capability_sealed c" and "\<not>Capability_sealed c'"
    and "Capability_permit_seal c'"
  shows "c'' \<in> derivable_caps s"
proof -
  have "seal CC c (get_cursor_method CC c') \<in> derivable (accessed_caps s)"
    using assms
    by (intro derivable.Seal) (auto simp: derivable_caps_def get_cap_perms_def)
  moreover have "seal CC c (get_cursor_method CC c') = c''"
    using assms
    by (cases c)
       (auto simp: sealCap_def seal_def to_bits_def getCapCursor_def of_bl_bin_word_of_int word_of_int_nat)
  ultimately show ?thesis
    by (simp add: derivable_caps_def)
qed

lemma traces_enabled_execute_CSeal[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CSeal arg0 arg1 arg2) s regs"
  unfolding execute_CSeal_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CSCC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CSCC arg0 arg1 arg2) s regs"
  unfolding execute_CSCC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CSC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CSC arg0 arg1 arg2 arg3) s regs"
  unfolding execute_CSC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CReturn[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CReturn arg0) s regs"
  unfolding execute_CReturn_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CReadHwr[traces_enabledI]:
  assumes "{''CULR'', ''DDC'', ''PCC''} \<subseteq> accessible_regs s"
    and "privileged_regs ISA \<inter> written_regs s = {}"
  shows "traces_enabled (execute_CReadHwr arg0 arg1) s regs"
proof -
  have "uint arg1 \<in> {0..31}"
    by auto
  then show ?thesis
    unfolding upto_31_unfold execute_CReadHwr_def bind_assoc
    by (elim insertE; simp cong: if_cong; use nothing in \<open>traces_enabledI assms: assms\<close>)
qed

lemma traces_enabled_execute_CRAP[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CRAP arg0 arg1) s regs"
  unfolding execute_CRAP_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CRAM[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CRAM arg0 arg1) s regs"
  unfolding execute_CRAM_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CPtrCmp[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CPtrCmp arg0 arg1 arg2 arg3) s regs"
  unfolding execute_CPtrCmp_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CMove[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CMove arg0 arg1) s regs"
  unfolding execute_CMove_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CMOVX[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CMOVX arg0 arg1 arg2 arg3) s regs"
  unfolding execute_CMOVX_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CLoadTags[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CLoadTags arg0 arg1) s regs"
  unfolding execute_CLoadTags_def bind_assoc
  by (traces_enabledI intro: traces_enabled_foreachM_inv[where s = s and P = "\<lambda>vars s' regs'. {''PCC''} \<subseteq> accessible_regs s'" for s] assms: assms)

lemma traces_enabled_execute_CLoadLinked[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CLoadLinked arg0 arg1 arg2 arg3) s regs"
  unfolding execute_CLoadLinked_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CLoad[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CLoad arg0 arg1 arg2 arg3 arg4 arg5) s regs"
  unfolding execute_CLoad_def bind_assoc
  by (traces_enabledI assms: assms)

lemma Run_inv_read_memt_derivable_caps[derivable_capsE]:
  assumes "Run_inv (read_memt BCa BC_mword rk addr sz) t a regs"
    and "tag \<longrightarrow> a = (mem, B1)"
  shows "memBitsToCapability tag mem \<in> derivable_caps (run s t)"
  using assms
  unfolding Run_inv_def read_memt_def read_memt_bytes_def maybe_fail_def bind_assoc
  by (cases tag)
     (auto simp: derivable_caps_def BC_mword_defs memBitsToCapability_def capBitsToCapability_def
           elim!: Run_bindE intro!: derivable.Copy elim: Traces_cases split: option.splits)

lemma Run_inv_maybe_fail_iff[simp]:
  "Run_inv (maybe_fail msg x) t a regs \<longleftrightarrow> (x = Some a \<and> t = [] \<and> invariant regs)"
  by (auto simp: Run_inv_def maybe_fail_def split: option.splits)

lemma Run_inv_MEMr_tagged_reserve_derivable_caps[derivable_capsE]:
  assumes "Run_inv (MEMr_tagged_reserve addr sz allow_tag) t a regs"
    and "tag \<longrightarrow> a = (True, mem)"
  shows "memBitsToCapability tag mem \<in> derivable_caps (run s t)"
  using assms
  unfolding MEMr_tagged_reserve_def
  by (auto elim!: Run_inv_bindE Run_inv_read_memt_derivable_caps intro: preserves_invariantI traces_runs_preserve_invariantI
           split: option.splits bitU.splits if_splits simp: bool_of_bitU_def)

lemma Run_inv_MEMr_tagged_derivable_caps[derivable_capsE]:
  assumes "Run_inv (MEMr_tagged addr sz allow_tag) t a regs"
    and "tag \<longrightarrow> a = (True, mem)"
  shows "memBitsToCapability tag mem \<in> derivable_caps (run s t)"
  using assms
  unfolding MEMr_tagged_def
  by (auto elim!: Run_inv_bindE Run_inv_read_memt_derivable_caps intro: preserves_invariantI traces_runs_preserve_invariantI
           split: option.splits bitU.splits if_splits simp: bool_of_bitU_def)

lemma traces_enabled_execute_CLLC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CLLC arg0 arg1) s regs"
  unfolding execute_CLLC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CLCBI[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CLCBI arg0 arg1 arg2) s regs"
  unfolding execute_CLCBI_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CLC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CLC arg0 arg1 arg2 arg3) s regs"
  unfolding execute_CLC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CJALR[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CJALR arg0 arg1 arg2) s regs"
  unfolding execute_CJALR_def bind_assoc
  by (traces_enabledI assms: assms simp: Run_inv_read_reg_PCC_not_sealed)

lemma incCapOffset_derivable_caps[derivable_capsE]:
  assumes c': "incCapOffset c i = (success, c')"
    and c: "c \<in> derivable_caps s" and noseal: "Capability_tag c \<and> i \<noteq> 0 \<longrightarrow> \<not>Capability_sealed c"
  shows "c' \<in> derivable_caps s"
proof -
  have "leq_cap CC c' c" if "Capability_tag c"
    using that c'[symmetric] noseal
    by (auto simp: leq_cap_def incCapOffset_def getCapTop_def getCapBase_def get_cap_perms_def)
  moreover have "Capability_tag c' \<longleftrightarrow> Capability_tag c"
    using c'
    by (auto simp: incCapOffset_def)
  ultimately show ?thesis
    using c
    unfolding derivable_caps_def
    by (auto elim: derivable.Restrict)
qed

lemma traces_enabled_execute_CIncOffsetImmediate[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CIncOffsetImmediate arg0 arg1 arg2) s regs"
  unfolding execute_CIncOffsetImmediate_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CIncOffset[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CIncOffset arg0 arg1 arg2) s regs"
  unfolding execute_CIncOffset_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CGetType[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetType arg0 arg1) s regs"
  unfolding execute_CGetType_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CGetTag[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetTag arg0 arg1) s regs"
  unfolding execute_CGetTag_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CGetSealed[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetSealed arg0 arg1) s regs"
  unfolding execute_CGetSealed_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CGetPerm[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetPerm arg0 arg1) s regs"
  unfolding execute_CGetPerm_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CGetPCCSetOffset[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetPCCSetOffset arg0 arg1) s regs"
  unfolding execute_CGetPCCSetOffset_def bind_assoc
  by (traces_enabledI assms: assms simp: Run_inv_read_reg_PCC_not_sealed)

lemma traces_enabled_execute_CGetPCC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetPCC arg0) s regs"
  unfolding execute_CGetPCC_def bind_assoc
  by (traces_enabledI assms: assms simp: Run_inv_read_reg_PCC_not_sealed)

lemma traces_enabled_execute_CGetOffset[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetOffset arg0 arg1) s regs"
  unfolding execute_CGetOffset_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CGetLen[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetLen arg0 arg1) s regs"
  unfolding execute_CGetLen_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CGetFlags[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetFlags arg0 arg1) s regs"
  unfolding execute_CGetFlags_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CGetCause[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetCause arg0) s regs"
  unfolding execute_CGetCause_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CGetCID[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetCID arg0) s regs"
  unfolding execute_CGetCID_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CGetBase[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetBase arg0 arg1) s regs"
  unfolding execute_CGetBase_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CGetAndAddr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetAndAddr arg0 arg1 arg2) s regs"
  unfolding execute_CGetAndAddr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CGetAddr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CGetAddr arg0 arg1) s regs"
  unfolding execute_CGetAddr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CFromPtr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CFromPtr arg0 arg1 arg2) s regs"
  unfolding execute_CFromPtr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma update_Capability_address_derivable_caps[derivable_capsI]:
  assumes "c \<in> derivable_caps s" and "\<not>Capability_sealed c"
  shows "c\<lparr>Capability_address := a\<rparr> \<in> derivable_caps s"
proof -
  have "leq_cap CC (c\<lparr>Capability_address := a\<rparr>) c"
    using assms
    by (auto simp: leq_cap_def getCapBase_def getCapTop_def get_cap_perms_def)
  then show ?thesis
    using assms
    by (auto simp: derivable_caps_def elim: derivable.Restrict)
qed

lemma null_cap_not_sealed[simp, intro]: "\<not>Capability_sealed null_cap"
  by (auto simp: null_cap_def)

declare null_cap_derivable[derivable_capsI]

lemma traces_enabled_execute_CCopyType[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CCopyType arg0 arg1 arg2) s regs"
  unfolding execute_CCopyType_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CClearTag[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CClearTag arg0 arg1) s regs"
  unfolding execute_CClearTag_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CCheckType[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CCheckType arg0 arg1) s regs"
  unfolding execute_CCheckType_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CCheckTag[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CCheckTag arg0) s regs"
  unfolding execute_CCheckTag_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CCheckPerm[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CCheckPerm arg0 arg1) s regs"
  unfolding execute_CCheckPerm_def bind_assoc
  by (traces_enabledI assms: assms)

lemma set_next_pcc_invoked_caps:
  assumes "cc \<in> derivable_caps s"
    and "\<exists>cd. cd \<in> derivable_caps s \<and> invokable CC cc cd" and "invocation_traces"
  shows "traces_enabled (set_next_pcc (unsealCap cc)) s regs"
proof -
  have "leq_cap CC (unsealCap cc) (unseal CC cc True)"
    by (auto simp: leq_cap_def unsealCap_def unseal_def getCapBase_def getCapTop_def get_cap_perms_def)
  moreover obtain cd
    where cc: "cc \<in> derivable (accessed_caps s)" and cd: "cd \<in> derivable (accessed_caps s)"
      and "Capability_tag cc" and "Capability_tag cd" and "invokable CC cc cd"
    using assms
    by (auto simp: derivable_caps_def invokable_def get_cap_perms_def)
  moreover have "cc \<in> derivable (accessed_caps (run s t))" and "cd \<in> derivable (accessed_caps (run s t))" for t
    using cc cd derivable_mono[OF accessed_caps_run_mono]
    by auto
  ultimately show ?thesis
    unfolding set_next_pcc_def
    by (intro traces_enabled_write_reg traces_enabledI preserves_invariantI traces_runs_preserve_invariantI)
       (auto simp add: NextPCC_ref_def DelayedPCC_ref_def derivable_caps_def intro: \<open>invocation_traces\<close>)
qed

lemma write_reg_C26_invoked_caps:
  assumes "cd \<in> derivable_caps s"
    and "\<exists>cc. cc \<in> derivable_caps s \<and> invokable CC cc cd" and "invocation_traces"
  shows "traces_enabled (write_reg C26_ref (unsealCap cd)) s regs"
proof -
  have "leq_cap CC (unsealCap cd) (unseal CC cd True)"
    by (auto simp: leq_cap_def unsealCap_def unseal_def getCapBase_def getCapTop_def get_cap_perms_def)
  moreover obtain cc
    where cc: "cc \<in> derivable (accessed_caps s)" and cd: "cd \<in> derivable (accessed_caps s)"
      and "Capability_tag cc" and "Capability_tag cd" and "invokable CC cc cd"
    using assms
    by (auto simp: derivable_caps_def invokable_def get_cap_perms_def)
  ultimately show ?thesis
    by (intro traces_enabled_write_reg)
       (auto simp: C26_ref_def derivable_caps_def intro: \<open>invocation_traces\<close>)
qed

lemma getCapCursor_nonneg[simp]: "0 \<le> getCapCursor c"
  by (auto simp: getCapCursor_def)

lemma getCapTop_nonneg[simp]: "0 \<le> getCapTop c"
  by (auto simp: getCapTop_def)

lemma invokable_data_cap_derivable:
  assumes "\<not> Capability_permit_execute cd" and "Capability_permit_execute cc"
    and "Capability_tag cd" and "Capability_tag cc"
    and "Capability_sealed cd" and "Capability_sealed cc"
    and "Capability_permit_ccall cd" and "Capability_permit_ccall cc"
    and "Capability_otype cc = Capability_otype cd"
    and "getCapBase cc \<le> getCapCursor cc"
    and "getCapCursor cc < getCapTop cc"
    and "cd \<in> derivable_caps s"
  shows "\<exists>cd. cd \<in> derivable_caps s \<and> invokable CC cc cd"
  using assms getCapCursor_nonneg[of cc] getCapTop_nonneg[of cc]
  unfolding le_less
  by (auto simp: invokable_def nat_le_eq_zle get_cap_perms_def)

lemma invokable_code_cap_derivable:
  assumes "\<not>\<not> Capability_permit_execute cc" and "\<not>Capability_permit_execute cd"
    and "Capability_tag cd" and "Capability_tag cc"
    and "Capability_sealed cd" and "Capability_sealed cc"
    and "Capability_permit_ccall cd" and "Capability_permit_ccall cc"
    and "Capability_otype cc = Capability_otype cd"
    and "getCapBase cc \<le> getCapCursor cc"
    and "getCapCursor cc < getCapTop cc"
    and "cc \<in> derivable_caps s"
  shows "\<exists>cc. cc \<in> derivable_caps s \<and> invokable CC cc cd"
  using assms getCapCursor_nonneg[of cc] getCapTop_nonneg[of cc]
  unfolding le_less
  by (auto simp: invokable_def nat_le_eq_zle get_cap_perms_def)

lemma traces_enabled_execute_CCall[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
    and "invocation_traces"
  shows "traces_enabled (execute_CCall arg0 arg1 arg2) s regs"
  unfolding execute_CCall_def bind_assoc
  by (traces_enabledI assms: assms intro: set_next_pcc_invoked_caps write_reg_C26_invoked_caps
                      elim: invokable_data_cap_derivable invokable_code_cap_derivable)

lemma traces_enabled_execute_CCSeal[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CCSeal arg0 arg1 arg2) s regs"
  unfolding execute_CCSeal_def bind_assoc
  by (traces_enabledI assms: assms)

definition perms_of_bits :: "31 word \<Rightarrow> perms" where
  "perms_of_bits p =
     \<lparr>permit_ccall                  = p !! 8,
      permit_execute                = p !! 1,
      permit_load                   = p !! 2,
      permit_load_capability        = p !! 4,
      permit_seal                   = p !! 7,
      permit_store                  = p !! 3,
      permit_store_capability       = p !! 5,
      permit_store_local_capability = p !! 6,
      permit_system_access          = p !! 10,
      permit_unseal                 = p !! 9\<rparr>"

definition and_perms :: "perms \<Rightarrow> perms \<Rightarrow> perms" where
  "and_perms p1 p2 =
     \<lparr>permit_ccall                  = permit_ccall p1 \<and> permit_ccall p2,
      permit_execute                = permit_execute p1 \<and> permit_execute p2,
      permit_load                   = permit_load p1 \<and> permit_load p2,
      permit_load_capability        = permit_load_capability p1 \<and> permit_load_capability p2,
      permit_seal                   = permit_seal p1 \<and> permit_seal p2,
      permit_store                  = permit_store p1 \<and> permit_store p2,
      permit_store_capability       = permit_store_capability p1 \<and> permit_store_capability p2,
      permit_store_local_capability = permit_store_local_capability p1 \<and> permit_store_local_capability p2,
      permit_system_access          = permit_system_access p1 \<and> permit_system_access p2,
      permit_unseal                 = permit_unseal p1 \<and> permit_unseal p2\<rparr>"

lemma setCapPerms_derivable_caps[derivable_capsI]:
  assumes "c \<in> derivable_caps s" and "Capability_tag c \<longrightarrow> leq_perms (perms_of_bits p) (get_cap_perms c) \<and> \<not>Capability_sealed c \<and> (p !! 0 \<longrightarrow> Capability_global c)"
  shows "setCapPerms c p \<in> derivable_caps s"
proof -
  have "leq_cap CC (setCapPerms c p) c" and "Capability_tag (setCapPerms c p) = Capability_tag c"
    using assms
    by (auto simp: setCapPerms_def leq_cap_def getCapBase_def getCapTop_def perms_of_bits_def get_cap_perms_def)
  then show ?thesis
    using assms
    by (auto simp: derivable_caps_def elim!: derivable.Restrict)
qed

(*lemma setCapOffset_sealed_iff:
  assumes "setCapOffset c offset = (success, c')"
  shows "Capability_sealed c' \<longleftrightarrow> Capability_sealed c"
  using assms
  by (auto simp: setCapOffset_def)

lemma setCapBounds_sealed_iff:
  assumes "setCapBounds c b t = (success, c')"
  shows "Capability_sealed c' \<longleftrightarrow> Capability_sealed c"
  using assms
  by (auto simp: setCapBounds_def)

lemma setCapOffset_get_cap_perms_eq:
  assumes "setCapOffset c offset = (success, c')"
  shows "get_cap_perms c' = get_cap_perms c"
  using assms
  by (auto simp: setCapOffset_def get_cap_perms_def)

lemma setCapBounds_get_cap_perms_eq:
  assumes "setCapBounds c b t = (success, c')"
  shows "get_cap_perms c' = get_cap_perms c"
  using assms
  by (auto simp: setCapBounds_def get_cap_perms_def)*)

lemma bool_to_bits_nth[simp]: "bool_to_bits b !! n \<longleftrightarrow> b \<and> n = 0"
  by (auto simp: bool_to_bits_def)

lemma perms_of_bits_getCapPerms_get_cap_perms[simp]:
  "perms_of_bits (getCapPerms c) = get_cap_perms c"
  by (auto simp: perms_of_bits_def getCapPerms_def getCapHardPerms_def get_cap_perms_def test_bit_cat nth_ucast)

lemma getCapPerms_0th_iff_global[simp]:
  "getCapPerms c !! 0 = Capability_global c"
  by (auto simp: getCapPerms_def getCapHardPerms_def test_bit_cat nth_ucast)

lemma perms_of_bits_AND_and_perms[simp]:
  "perms_of_bits (x AND y) = and_perms (perms_of_bits x) (perms_of_bits y)"
  by (auto simp: perms_of_bits_def and_perms_def word_ao_nth)

lemma leq_perms_and_perms[simp, intro]:
  "leq_perms (and_perms p1 p2) p1"
  by (auto simp: leq_perms_def and_perms_def)

lemma traces_enabled_execute_CBuildCap[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CBuildCap arg0 arg1 arg2) s regs"
proof -
  have [simp]:
    "Capability_global c' = Capability_global c"
    "Capability_sealed c' \<longleftrightarrow> Capability_sealed c"
    "get_cap_perms c' = get_cap_perms c"
    if "setCapOffset c offset = (success, c')" for c c' offset success
    using that
    by (auto simp: setCapOffset_def get_cap_perms_def)
  have [simp]:
    "Capability_global c' = Capability_global c"
    "Capability_sealed c' \<longleftrightarrow> Capability_sealed c"
    "get_cap_perms c' = get_cap_perms c"
    if "setCapBounds c t b = (success, c')" for c c' t b success
    using that
    by (auto simp: setCapBounds_def get_cap_perms_def)
  have [simp]: "Capability_global c \<longrightarrow> Capability_global c'"
    if "getCapPerms c AND getCapPerms c' = getCapPerms c" for c c'
    unfolding getCapPerms_0th_iff_global[symmetric]
    by (subst that[symmetric]) (auto simp add: word_ao_nth simp del: getCapPerms_0th_iff_global)
  have [elim]: "leq_perms (get_cap_perms c) (get_cap_perms c')"
    if "getCapPerms c AND getCapPerms c' = getCapPerms c" for c c'
    unfolding perms_of_bits_getCapPerms_get_cap_perms[symmetric]
    by (subst that[symmetric]) (auto simp add: leq_perms_def perms_of_bits_def word_ao_nth)
  show ?thesis
    unfolding execute_CBuildCap_def bind_assoc
    by (traces_enabledI assms: assms simp: getCapBase_def getCapTop_def)
qed

lemma traces_enabled_execute_CBZ[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CBZ arg0 arg1 arg2) s regs"
  unfolding execute_CBZ_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CBX[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CBX arg0 arg1 arg2) s regs"
  unfolding execute_CBX_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CAndPerm[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CAndPerm arg0 arg1 arg2) s regs"
  unfolding execute_CAndPerm_def bind_assoc
  by (traces_enabledI assms: assms simp: word_ao_nth)

lemma traces_enabled_execute_CAndAddr[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CAndAddr arg0 arg1 arg2) s regs"
  unfolding execute_CAndAddr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CACHE[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CACHE arg0 arg1 arg2) s regs"
  unfolding execute_CACHE_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BREAK[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_BREAK arg0) s regs"
  unfolding execute_BREAK_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BEQ[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_BEQ arg0 arg1 arg2 arg3 arg4) s regs"
  unfolding execute_BEQ_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_BCMPZ[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_BCMPZ arg0 arg1 arg2 arg3 arg4) s regs"
  unfolding execute_BCMPZ_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ADDI[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_ADDI arg0 arg1 arg2) s regs"
  unfolding execute_ADDI_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_ADD[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_ADD arg0 arg1 arg2) s regs"
  unfolding execute_ADD_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_instr_sem[traces_enabledI]:
  assumes "{''CULR'', ''DDC'', ''PCC''} \<subseteq> accessible_regs s"
    and "CapRegs_names \<subseteq> accessible_regs s"
    and "privileged_regs ISA \<inter> written_regs s = {}"
    and "invokes_caps ISA instr [] \<longrightarrow> invocation_traces"
  shows "traces_enabled (instr_sem ISA instr) s regs"
  by (cases instr rule: execute.cases; simp; use nothing in \<open>traces_enabledI assms: assms\<close>)

lemma hasTrace_reg_axioms:
  assumes "hasTrace t (instr_sem ISA instr)"
    and "reads_regs_from inv_regs t regs" and "invariant regs"
    and "hasException t (instr_sem ISA instr) \<or> hasFailure t (instr_sem ISA instr) \<longrightarrow> ex_traces"
    and "invokes_caps ISA instr t \<longrightarrow> invocation_traces"
  shows "store_cap_reg_axiom CC ISA ex_traces invocation_traces t"
    and "store_cap_mem_axiom CC ISA t"
    and "read_reg_axiom CC ISA ex_traces t"
  using assms
  by (intro traces_enabled_store_cap_reg_read_reg_axioms traces_enabled_instr_sem; auto)+

end

end
