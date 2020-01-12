theory CHERI_MIPS_Mem_Axioms
imports CHERI_MIPS_Gen_Lemmas
begin

context CHERI_MIPS_Mem_Automaton
begin

lemma preserves_invariant_write_non_inv_regs[preserves_invariantI]:
  "\<And>v. traces_preserve_invariant (write_reg BranchPending_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg C26_ref v)"
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
  (*"\<And>v. traces_preserve_invariant (write_reg PCC_ref v)"*)
  "\<And>v. traces_preserve_invariant (write_reg TLBEntryLo0_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBEntryLo1_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBIndex_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBPageMask_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBProbe_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBRandom_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg TLBWired_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg UART_RDATA_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg UART_RVALID_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg UART_WDATA_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg UART_WRITTEN_ref v)"
  "\<And>v. traces_preserve_invariant (write_reg InstCount_ref v)"
  unfolding BranchPending_ref_def C26_ref_def CID_ref_def CP0BadInstr_ref_def CP0BadInstrP_ref_def
     CP0BadVAddr_ref_def CP0Cause_ref_def CP0Compare_ref_def CP0ConfigK0_ref_def CP0Count_ref_def
     CP0HWREna_ref_def CP0LLAddr_ref_def CP0LLBit_ref_def CP0UserLocal_ref_def CPLR_ref_def
     CULR_ref_def CapCause_ref_def CurrentInstrBits_ref_def DDC_ref_def DelayedPC_ref_def
     DelayedPCC_ref_def EPCC_ref_def ErrorEPCC_ref_def GPR_ref_def HI_ref_def
     InBranchDelay_ref_def KCC_ref_def KDC_ref_def KR1C_ref_def KR2C_ref_def
     LO_ref_def LastInstrBits_ref_def NextInBranchDelay_ref_def NextPC_ref_def NextPCC_ref_def
     PC_ref_def PCC_ref_def TLBEntryLo0_ref_def TLBEntryLo1_ref_def TLBIndex_ref_def
     TLBPageMask_ref_def TLBProbe_ref_def TLBRandom_ref_def TLBWired_ref_def UART_RDATA_ref_def
     UART_RVALID_ref_def UART_WDATA_ref_def UART_WRITTEN_ref_def InstCount_ref_def
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg; simp add: trans_regs_def)+

declare MemAccessType.split[where P = "\<lambda>m. runs_preserve_invariant m", THEN iffD2, preserves_invariantI]

lemma preserves_invariant_no_writes_to_inv_regs[preserves_invariantI]:
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MIPS_write arg0 arg1 arg2)"
  "\<And>arg0 arg1. traces_preserve_invariant (MIPS_read arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_BD arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_CE arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_IV arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_IP arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_ExcCode arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_bits arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_CapS arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_CapL arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_PFN arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_C arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_D arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_V arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryLoReg_G arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryHiReg_R arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryHiReg_VPN2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryHiReg_ASID arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_ContextReg_PTEBase arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_ContextReg_BadVPN2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_XContextReg_XPTEBase arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_XContextReg_XR arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_XContextReg_XBadVPN2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_pagemask arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_r arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_vpn2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_asid arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_g arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_valid arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_caps1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_capl1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_pfn1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_c1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_d1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_v1 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_caps0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_capl0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_pfn0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_c0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_d0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntry_v0 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_CU arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_BEV arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_IM arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_KX arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_SX arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_UX arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_KSU arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_ERL arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_EXL arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_IE arg0 arg1)"
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
  "\<And>arg0. traces_preserve_invariant (getAccessLevel arg0)"
  "\<And>arg0. traces_preserve_invariant (pcc_access_system_regs arg0)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_CapCauseReg_ExcCode arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> trans_regs \<Longrightarrow> traces_preserve_invariant (set_CapCauseReg_RegNum arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr_wrapper arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr_reserve_wrapper arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (tlbSearch arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (capToString arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (execute_branch_pcc arg0)"
  "\<And>arg0. traces_preserve_invariant (ERETHook arg0)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMr_tagged arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMr_tagged_reserve arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2 arg3. traces_preserve_invariant (MEMw_tagged arg0 arg1 arg2 arg3)"
  "\<And>arg0 arg1 arg2 arg3. traces_preserve_invariant (MEMw_tagged_conditional arg0 arg1 arg2 arg3)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMw_wrapper arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMw_conditional_wrapper arg0 arg1 arg2)"
  "\<And>arg0. traces_preserve_invariant (get_CP0EPC arg0)"
  "\<And>arg0. traces_preserve_invariant (set_CP0EPC arg0)"
  "\<And>arg0. traces_preserve_invariant (get_CP0ErrorEPC arg0)"
  "\<And>arg0. traces_preserve_invariant (set_CP0ErrorEPC arg0)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_toI; simp add: trans_regs_def)+

lemma preserves_invariant_undefined_option[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_option arg0)"
  unfolding undefined_option_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_exception[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_exception arg0)"
  unfolding undefined_exception_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_CauseReg[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_CauseReg arg0)"
  unfolding undefined_CauseReg_def bind_assoc
  by (preserves_invariantI)

(*lemma preserves_invariant_set_CauseReg_bits[preserves_invariantI]:
  shows "runs_preserve_invariant (set_CauseReg_bits arg0 arg1)"
  unfolding set_CauseReg_bits_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_set_CauseReg_WP[preserves_invariantI]:
  shows "runs_preserve_invariant (set_CauseReg_WP arg0 arg1)"
  unfolding set_CauseReg_WP_def bind_assoc
  by (preserves_invariantI)*)

lemma preserves_invariant_undefined_TLBEntryLoReg[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_TLBEntryLoReg arg0)"
  unfolding undefined_TLBEntryLoReg_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_TLBEntryHiReg[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_TLBEntryHiReg arg0)"
  unfolding undefined_TLBEntryHiReg_def bind_assoc
  by (preserves_invariantI)

(*lemma preserves_invariant_set_TLBEntryHiReg_bits[preserves_invariantI]:
  shows "runs_preserve_invariant (set_TLBEntryHiReg_bits arg0 arg1)"
  unfolding set_TLBEntryHiReg_bits_def bind_assoc
  by (preserves_invariantI)*)

lemma preserves_invariant_undefined_ContextReg[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_ContextReg arg0)"
  unfolding undefined_ContextReg_def bind_assoc
  by (preserves_invariantI)

(*lemma preserves_invariant_set_ContextReg_bits[preserves_invariantI]:
  shows "runs_preserve_invariant (set_ContextReg_bits arg0 arg1)"
  unfolding set_ContextReg_bits_def bind_assoc
  by (preserves_invariantI)*)

lemma preserves_invariant_undefined_XContextReg[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_XContextReg arg0)"
  unfolding undefined_XContextReg_def bind_assoc
  by (preserves_invariantI)

(*lemma preserves_invariant_set_XContextReg_bits[preserves_invariantI]:
  shows "runs_preserve_invariant (set_XContextReg_bits arg0 arg1)"
  unfolding set_XContextReg_bits_def bind_assoc
  by (preserves_invariantI)*)

lemma preserves_invariant_undefined_TLBEntry[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_TLBEntry arg0)"
  unfolding undefined_TLBEntry_def bind_assoc
  by (preserves_invariantI)

(*lemma preserves_invariant_set_TLBEntry_bits[preserves_invariantI]:
  shows "runs_preserve_invariant (set_TLBEntry_bits arg0 arg1)"
  unfolding set_TLBEntry_bits_def bind_assoc
  by (preserves_invariantI)*)

lemma preserves_invariant_undefined_StatusReg[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_StatusReg arg0)"
  unfolding undefined_StatusReg_def bind_assoc
  by (preserves_invariantI)

(*lemma preserves_invariant_set_StatusReg_bits[preserves_invariantI]:
  shows "runs_preserve_invariant (set_StatusReg_bits arg0 arg1)"
  unfolding set_StatusReg_bits_def bind_assoc
  by (preserves_invariantI)*)

lemma preserves_invariant_undefined_Exception[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_Exception arg0)"
  unfolding undefined_Exception_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_Capability[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_Capability arg0)"
  unfolding undefined_Capability_def bind_assoc
  by (preserves_invariantI)

(*lemma preserves_invariant_SignalException[preserves_invariantI]:
  shows "runs_preserve_invariant (SignalException arg0)"
  unfolding SignalException_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_SignalExceptionBadAddr[preserves_invariantI]:
  shows "runs_preserve_invariant (SignalExceptionBadAddr arg0 arg1)"
  unfolding SignalExceptionBadAddr_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_SignalExceptionTLB[preserves_invariantI]:
  shows "runs_preserve_invariant (SignalExceptionTLB arg0 arg1)"
  unfolding SignalExceptionTLB_def bind_assoc
  by (preserves_invariantI)*)

lemma preserves_invariant_undefined_MemAccessType[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_MemAccessType arg0)"
  unfolding undefined_MemAccessType_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_AccessLevel[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_AccessLevel arg0)"
  unfolding undefined_AccessLevel_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_CapCauseReg[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_CapCauseReg arg0)"
  unfolding undefined_CapCauseReg_def bind_assoc
  by (preserves_invariantI)

(*lemma preserves_invariant_raise_c2_exception8[preserves_invariantI]:
  shows "runs_preserve_invariant (raise_c2_exception8 arg0 arg1)"
  unfolding raise_c2_exception8_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_raise_c2_exception_noreg[preserves_invariantI]:
  shows "runs_preserve_invariant (raise_c2_exception_noreg arg0)"
  unfolding raise_c2_exception_noreg_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_checkCP0AccessHook[preserves_invariantI]:
  shows "runs_preserve_invariant (checkCP0AccessHook arg0)"
  unfolding checkCP0AccessHook_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_checkCP0Access[preserves_invariantI]:
  shows "runs_preserve_invariant (checkCP0Access arg0)"
  unfolding checkCP0Access_def bind_assoc
  by (preserves_invariantI)*)

lemma trans_regs_non_members[simp]:
  "name CP0Cause_ref \<notin> trans_regs"
  "name CapCause_ref \<notin> trans_regs"
  by (auto simp: trans_regs_def CP0Cause_ref_def CapCause_ref_def)

lemma preserves_invariant_incrementCP0Count[preserves_invariantI]:
  shows "runs_preserve_invariant (incrementCP0Count arg0)"
  unfolding incrementCP0Count_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_decode_failure[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_decode_failure arg0)"
  unfolding undefined_decode_failure_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_Comparison[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_Comparison arg0)"
  unfolding undefined_Comparison_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_WordType[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_WordType arg0)"
  unfolding undefined_WordType_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_WordTypeUnaligned[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_WordTypeUnaligned arg0)"
  unfolding undefined_WordTypeUnaligned_def bind_assoc
  by (preserves_invariantI)

(*lemma preserves_invariant_init_cp0_state[preserves_invariantI]:
  shows "runs_preserve_invariant (init_cp0_state arg0)"
  unfolding init_cp0_state_def bind_assoc
  by (preserves_invariantI)*)

lemma preserves_invariant_TLBTranslate2[preserves_invariantI]:
  shows "runs_preserve_invariant (TLBTranslate2 arg0 arg1)"
  unfolding TLBTranslate2_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_TLBTranslateC[preserves_invariantI]:
  shows "runs_preserve_invariant (TLBTranslateC arg0 arg1)"
  unfolding TLBTranslateC_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_TLBTranslate[preserves_invariantI]:
  shows "runs_preserve_invariant (TLBTranslate arg0 arg1)"
  unfolding TLBTranslate_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_CPtrCmpOp[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_CPtrCmpOp arg0)"
  unfolding undefined_CPtrCmpOp_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_ClearRegSet[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_ClearRegSet arg0)"
  unfolding undefined_ClearRegSet_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_undefined_CapEx[preserves_invariantI]:
  shows "runs_preserve_invariant (undefined_CapEx arg0)"
  unfolding undefined_CapEx_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_set_CapCauseReg_bits[preserves_invariantI]:
  assumes "name arg0 \<notin> trans_regs"
  shows "runs_preserve_invariant (set_CapCauseReg_bits arg0 arg1)"
  using assms
  unfolding set_CapCauseReg_bits_def bind_assoc
  by (preserves_invariantI; intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg)

lemma preserves_invariant_raise_c2_exception[preserves_invariantI]:
  shows "runs_preserve_invariant (raise_c2_exception arg0 arg1)"
  unfolding raise_c2_exception_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_checkDDCPerms[preserves_invariantI]:
  shows "runs_preserve_invariant (checkDDCPerms arg0 arg1)"
  unfolding checkDDCPerms_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_addrWrapper[preserves_invariantI]:
  shows "runs_preserve_invariant (addrWrapper arg0 arg1 arg2)"
  unfolding addrWrapper_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_addrWrapperUnaligned[preserves_invariantI]:
  shows "runs_preserve_invariant (addrWrapperUnaligned arg0 arg1 arg2)"
  unfolding addrWrapperUnaligned_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_branch[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_branch arg0)"
  unfolding execute_branch_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_TranslatePC[preserves_invariantI]:
  shows "runs_preserve_invariant (TranslatePC arg0)"
  unfolding TranslatePC_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_checkCP2usable[preserves_invariantI]:
  shows "runs_preserve_invariant (checkCP2usable arg0)"
  unfolding checkCP2usable_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_dump_cp2_state[preserves_invariantI]:
  shows "runs_preserve_invariant (dump_cp2_state arg0)"
  unfolding dump_cp2_state_def bind_assoc
  by (preserves_invariantI)

(*lemma preserves_invariant_TLBWriteEntry[preserves_invariantI]:
  shows "runs_preserve_invariant (TLBWriteEntry arg0)"
  unfolding TLBWriteEntry_def bind_assoc
  by (preserves_invariantI)*)

lemma preserves_invariant_execute_XORI[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_XORI arg0 arg1 arg2)"
  unfolding execute_XORI_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_XOR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_XOR arg0 arg1 arg2)"
  unfolding execute_XOR_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_WAIT[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_WAIT arg0)"
  unfolding execute_WAIT_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_TRAPREG[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_TRAPREG arg0 arg1 arg2)"
  unfolding execute_TRAPREG_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_TRAPIMM[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_TRAPIMM arg0 arg1 arg2)"
  unfolding execute_TRAPIMM_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_bind_checkCP0Access:
  "runs_preserve_invariant (checkCP0Access u \<then> m)"
  using Run_inv_checkCP0Access_False
  unfolding Run_inv_def runs_preserve_invariant_def trace_preserves_invariant_def
  by (auto simp: regstate_simp elim!: Run_bindE)

lemma preserves_invariant_execute_TLBWR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_TLBWR arg0)"
  unfolding execute_TLBWR_def bind_assoc
  by (intro preserves_invariant_bind_checkCP0Access)

lemma preserves_invariant_execute_TLBWI[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_TLBWI arg0)"
  unfolding execute_TLBWI_def bind_assoc
  by (intro preserves_invariant_bind_checkCP0Access)

lemma preserves_invariant_execute_TLBR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_TLBR arg0)"
  unfolding execute_TLBR_def bind_assoc
  by (intro preserves_invariant_bind_checkCP0Access)

lemma preserves_invariant_execute_TLBP[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_TLBP arg0)"
  unfolding execute_TLBP_def bind_assoc
  by (intro preserves_invariant_bind_checkCP0Access)

lemma preserves_invariant_execute_Store[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_Store arg0 arg1 arg2 arg3 arg4)"
  unfolding execute_Store_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SYSCALL[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SYSCALL arg0)"
  unfolding execute_SYSCALL_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SYNC[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SYNC arg0)"
  unfolding execute_SYNC_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SWR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SWR arg0 arg1 arg2)"
  unfolding execute_SWR_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SWL[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SWL arg0 arg1 arg2)"
  unfolding execute_SWL_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SUBU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SUBU arg0 arg1 arg2)"
  unfolding execute_SUBU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SUB[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SUB arg0 arg1 arg2)"
  unfolding execute_SUB_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SRLV[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SRLV arg0 arg1 arg2)"
  unfolding execute_SRLV_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SRL[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SRL arg0 arg1 arg2)"
  unfolding execute_SRL_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SRAV[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SRAV arg0 arg1 arg2)"
  unfolding execute_SRAV_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SRA[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SRA arg0 arg1 arg2)"
  unfolding execute_SRA_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SLTU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SLTU arg0 arg1 arg2)"
  unfolding execute_SLTU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SLTIU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SLTIU arg0 arg1 arg2)"
  unfolding execute_SLTIU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SLTI[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SLTI arg0 arg1 arg2)"
  unfolding execute_SLTI_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SLT[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SLT arg0 arg1 arg2)"
  unfolding execute_SLT_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SLLV[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SLLV arg0 arg1 arg2)"
  unfolding execute_SLLV_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SLL[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SLL arg0 arg1 arg2)"
  unfolding execute_SLL_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SDR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SDR arg0 arg1 arg2)"
  unfolding execute_SDR_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_SDL[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_SDL arg0 arg1 arg2)"
  unfolding execute_SDL_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_RI[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_RI arg0)"
  unfolding execute_RI_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_RDHWR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_RDHWR arg0 arg1)"
  unfolding execute_RDHWR_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_ORI[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_ORI arg0 arg1 arg2)"
  unfolding execute_ORI_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_OR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_OR arg0 arg1 arg2)"
  unfolding execute_OR_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_NOR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_NOR arg0 arg1 arg2)"
  unfolding execute_NOR_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MULTU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MULTU arg0 arg1)"
  unfolding execute_MULTU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MULT[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MULT arg0 arg1)"
  unfolding execute_MULT_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MUL[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MUL arg0 arg1 arg2)"
  unfolding execute_MUL_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MTLO[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MTLO arg0)"
  unfolding execute_MTLO_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MTHI[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MTHI arg0)"
  unfolding execute_MTHI_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MTC0[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MTC0 arg0 arg1 arg2 arg3)"
  unfolding execute_MTC0_def bind_assoc
  by (intro preserves_invariant_bind_checkCP0Access)

lemma preserves_invariant_execute_MSUBU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MSUBU arg0 arg1)"
  unfolding execute_MSUBU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MSUB[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MSUB arg0 arg1)"
  unfolding execute_MSUB_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MOVZ[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MOVZ arg0 arg1 arg2)"
  unfolding execute_MOVZ_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MOVN[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MOVN arg0 arg1 arg2)"
  unfolding execute_MOVN_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MFLO[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MFLO arg0)"
  unfolding execute_MFLO_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MFHI[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MFHI arg0)"
  unfolding execute_MFHI_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MFC0[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MFC0 arg0 arg1 arg2 arg3)"
  unfolding execute_MFC0_def bind_assoc
  by (intro preserves_invariant_bind_checkCP0Access)

lemma preserves_invariant_execute_MADDU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MADDU arg0 arg1)"
  unfolding execute_MADDU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_MADD[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_MADD arg0 arg1)"
  unfolding execute_MADD_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_Load[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_Load arg0 arg1 arg2 arg3 arg4 arg5)"
  unfolding execute_Load_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_LWR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_LWR arg0 arg1 arg2)"
  unfolding execute_LWR_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_LWL[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_LWL arg0 arg1 arg2)"
  unfolding execute_LWL_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_LUI[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_LUI arg0 arg1)"
  unfolding execute_LUI_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_LDR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_LDR arg0 arg1 arg2)"
  unfolding execute_LDR_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_LDL[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_LDL arg0 arg1 arg2)"
  unfolding execute_LDL_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_JR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_JR arg0)"
  unfolding execute_JR_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_JALR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_JALR arg0 arg1)"
  unfolding execute_JALR_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_JAL[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_JAL arg0)"
  unfolding execute_JAL_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_J[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_J arg0)"
  unfolding execute_J_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_ERET[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_ERET arg0)"
  unfolding execute_ERET_def bind_assoc
  by (intro preserves_invariant_bind_checkCP0Access)

lemma preserves_invariant_execute_DSUBU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DSUBU arg0 arg1 arg2)"
  unfolding execute_DSUBU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DSUB[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DSUB arg0 arg1 arg2)"
  unfolding execute_DSUB_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DSRLV[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DSRLV arg0 arg1 arg2)"
  unfolding execute_DSRLV_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DSRL32[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DSRL32 arg0 arg1 arg2)"
  unfolding execute_DSRL32_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DSRL[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DSRL arg0 arg1 arg2)"
  unfolding execute_DSRL_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DSRAV[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DSRAV arg0 arg1 arg2)"
  unfolding execute_DSRAV_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DSRA32[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DSRA32 arg0 arg1 arg2)"
  unfolding execute_DSRA32_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DSRA[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DSRA arg0 arg1 arg2)"
  unfolding execute_DSRA_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DSLLV[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DSLLV arg0 arg1 arg2)"
  unfolding execute_DSLLV_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DSLL32[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DSLL32 arg0 arg1 arg2)"
  unfolding execute_DSLL32_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DSLL[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DSLL arg0 arg1 arg2)"
  unfolding execute_DSLL_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DMULTU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DMULTU arg0 arg1)"
  unfolding execute_DMULTU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DMULT[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DMULT arg0 arg1)"
  unfolding execute_DMULT_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DIVU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DIVU arg0 arg1)"
  unfolding execute_DIVU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DIV[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DIV arg0 arg1)"
  unfolding execute_DIV_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DDIVU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DDIVU arg0 arg1)"
  unfolding execute_DDIVU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DDIV[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DDIV arg0 arg1)"
  unfolding execute_DDIV_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DADDU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DADDU arg0 arg1 arg2)"
  unfolding execute_DADDU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DADDIU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DADDIU arg0 arg1 arg2)"
  unfolding execute_DADDIU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DADDI[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DADDI arg0 arg1 arg2)"
  unfolding execute_DADDI_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_DADD[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_DADD arg0 arg1 arg2)"
  unfolding execute_DADD_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_writeCapReg[preserves_invariantI]:
  shows "traces_preserve_invariant (writeCapReg n v)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_writeCapReg)
     (simp add: CapRegs_names_def trans_regs_def)

lemma preserves_invariant_execute_ClearRegs[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_ClearRegs arg0 arg1)"
  unfolding execute_ClearRegs_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CWriteHwr[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CWriteHwr arg0 arg1)"
  unfolding execute_CWriteHwr_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CUnseal[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CUnseal arg0 arg1 arg2)"
  unfolding execute_CUnseal_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CToPtr[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CToPtr arg0 arg1 arg2)"
  unfolding execute_CToPtr_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CTestSubset[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CTestSubset arg0 arg1 arg2)"
  unfolding execute_CTestSubset_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CSub[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CSub arg0 arg1 arg2)"
  unfolding execute_CSub_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CStoreConditional[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CStoreConditional arg0 arg1 arg2 arg3)"
  unfolding execute_CStoreConditional_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CStore[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CStore arg0 arg1 arg2 arg3 arg4)"
  unfolding execute_CStore_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CSetOffset[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CSetOffset arg0 arg1 arg2)"
  unfolding execute_CSetOffset_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CSetFlags[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CSetFlags arg0 arg1 arg2)"
  unfolding execute_CSetFlags_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CSetCause[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CSetCause arg0)"
  unfolding execute_CSetCause_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CSetCID[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CSetCID arg0)"
  unfolding execute_CSetCID_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CSetBoundsImmediate[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CSetBoundsImmediate arg0 arg1 arg2)"
  unfolding execute_CSetBoundsImmediate_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CSetBoundsExact[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CSetBoundsExact arg0 arg1 arg2)"
  unfolding execute_CSetBoundsExact_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CSetBounds[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CSetBounds arg0 arg1 arg2)"
  unfolding execute_CSetBounds_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CSetAddr[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CSetAddr arg0 arg1 arg2)"
  unfolding execute_CSetAddr_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CSeal[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CSeal arg0 arg1 arg2)"
  unfolding execute_CSeal_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CSCC[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CSCC arg0 arg1 arg2)"
  unfolding execute_CSCC_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CSC[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CSC arg0 arg1 arg2 arg3)"
  unfolding execute_CSC_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CReturn[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CReturn arg0)"
  unfolding execute_CReturn_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CReadHwr[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CReadHwr arg0 arg1)"
  unfolding execute_CReadHwr_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CRAP[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CRAP arg0 arg1)"
  unfolding execute_CRAP_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CRAM[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CRAM arg0 arg1)"
  unfolding execute_CRAM_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CPtrCmp[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CPtrCmp arg0 arg1 arg2 arg3)"
  unfolding execute_CPtrCmp_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CMove[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CMove arg0 arg1)"
  unfolding execute_CMove_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CMOVX[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CMOVX arg0 arg1 arg2 arg3)"
  unfolding execute_CMOVX_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CLoadTags[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CLoadTags arg0 arg1)"
  unfolding execute_CLoadTags_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CLoadLinked[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CLoadLinked arg0 arg1 arg2 arg3)"
  unfolding execute_CLoadLinked_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CLoad[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CLoad arg0 arg1 arg2 arg3 arg4 arg5)"
  unfolding execute_CLoad_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CLLC[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CLLC arg0 arg1)"
  unfolding execute_CLLC_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CCLC[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CCLC arg0 arg1)"
  unfolding execute_CCLC_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CClearTags[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CClearTags arg0)"
  unfolding execute_CClearTags_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CLCBI[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CLCBI arg0 arg1 arg2)"
  unfolding execute_CLCBI_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CLC[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CLC arg0 arg1 arg2 arg3)"
  unfolding execute_CLC_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CJALR[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CJALR arg0 arg1 arg2)"
  unfolding execute_CJALR_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CIncOffsetImmediate[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CIncOffsetImmediate arg0 arg1 arg2)"
  unfolding execute_CIncOffsetImmediate_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CIncOffset[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CIncOffset arg0 arg1 arg2)"
  unfolding execute_CIncOffset_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetType[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetType arg0 arg1)"
  unfolding execute_CGetType_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetTag[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetTag arg0 arg1)"
  unfolding execute_CGetTag_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetSealed[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetSealed arg0 arg1)"
  unfolding execute_CGetSealed_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetPerm[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetPerm arg0 arg1)"
  unfolding execute_CGetPerm_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetPCCSetOffset[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetPCCSetOffset arg0 arg1)"
  unfolding execute_CGetPCCSetOffset_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetPCC[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetPCC arg0)"
  unfolding execute_CGetPCC_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetOffset[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetOffset arg0 arg1)"
  unfolding execute_CGetOffset_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetLen[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetLen arg0 arg1)"
  unfolding execute_CGetLen_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetFlags[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetFlags arg0 arg1)"
  unfolding execute_CGetFlags_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetCause[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetCause arg0)"
  unfolding execute_CGetCause_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetCID[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetCID arg0)"
  unfolding execute_CGetCID_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetBase[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetBase arg0 arg1)"
  unfolding execute_CGetBase_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetAndAddr[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetAndAddr arg0 arg1 arg2)"
  unfolding execute_CGetAndAddr_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CGetAddr[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CGetAddr arg0 arg1)"
  unfolding execute_CGetAddr_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CFromPtr[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CFromPtr arg0 arg1 arg2)"
  unfolding execute_CFromPtr_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CCopyType[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CCopyType arg0 arg1 arg2)"
  unfolding execute_CCopyType_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CClearTag[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CClearTag arg0 arg1)"
  unfolding execute_CClearTag_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CCheckType[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CCheckType arg0 arg1)"
  unfolding execute_CCheckType_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CCheckTag[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CCheckTag arg0)"
  unfolding execute_CCheckTag_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CCheckPerm[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CCheckPerm arg0 arg1)"
  unfolding execute_CCheckPerm_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CCall[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CCall arg0 arg1 arg2)"
  unfolding execute_CCall_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CCSeal[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CCSeal arg0 arg1 arg2)"
  unfolding execute_CCSeal_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CBuildCap[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CBuildCap arg0 arg1 arg2)"
  unfolding execute_CBuildCap_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CBZ[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CBZ arg0 arg1 arg2)"
  unfolding execute_CBZ_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CBX[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CBX arg0 arg1 arg2)"
  unfolding execute_CBX_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CAndPerm[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CAndPerm arg0 arg1 arg2)"
  unfolding execute_CAndPerm_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_CAndAddr[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CAndAddr arg0 arg1 arg2)"
  unfolding execute_CAndAddr_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_checkCP0Access[preserves_invariantI]:
  shows "runs_preserve_invariant (checkCP0Access u)"
  using Run_inv_checkCP0Access_False
  unfolding runs_preserve_invariant_def trace_preserves_invariant_def Run_inv_def
  by auto

lemma preserves_invariant_execute_CACHE[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_CACHE arg0 arg1 arg2)"
  unfolding execute_CACHE_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_BREAK[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_BREAK arg0)"
  unfolding execute_BREAK_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_BEQ[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_BEQ arg0 arg1 arg2 arg3 arg4)"
  unfolding execute_BEQ_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_BCMPZ[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_BCMPZ arg0 arg1 arg2 arg3 arg4)"
  unfolding execute_BCMPZ_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_ANDI[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_ANDI arg0 arg1 arg2)"
  unfolding execute_ANDI_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_AND[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_AND arg0 arg1 arg2)"
  unfolding execute_AND_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_ADDU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_ADDU arg0 arg1 arg2)"
  unfolding execute_ADDU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_ADDIU[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_ADDIU arg0 arg1 arg2)"
  unfolding execute_ADDIU_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_ADDI[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_ADDI arg0 arg1 arg2)"
  unfolding execute_ADDI_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute_ADD[preserves_invariantI]:
  shows "runs_preserve_invariant (execute_ADD arg0 arg1 arg2)"
  unfolding execute_ADD_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_execute[preserves_invariantI]:
  shows "runs_preserve_invariant (execute instr)"
  by (cases instr rule: execute.cases; simp; preserves_invariantI)

lemma preserves_invariant_write_reg_PCC[preserves_invariantI]:
  "traces_preserve_invariant (write_reg PCC_ref v)"
  by (auto simp: write_reg_def traces_preserve_invariant_def elim!: Write_reg_TracesE)
     (auto simp: trace_preserves_invariant_def trans_inv_def register_defs split: option.splits)

lemma preserves_invariant_cp2_next_pc[preserves_invariantI]:
  shows "runs_preserve_invariant (cp2_next_pc u)"
  unfolding cp2_next_pc_def
  by (preserves_invariantI)

lemma preserves_invariant_fetch[preserves_invariantI]:
  shows "runs_preserve_invariant (fetch u)"
  unfolding fetch_def
  by (preserves_invariantI)

end

context CHERI_MIPS_Mem_Instr_Automaton
begin

lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]

lemmas non_mem_exp_traces_enabled[traces_enabledI] = non_mem_expI[THEN non_mem_exp_traces_enabledI]

(* *)
lemma notnotE[derivable_capsE]:
  assumes "\<not>\<not>P"
  obtains "P"
  using assms
  by blast

lemma getCapCursor_mod_pow2_64[simp]:
  "getCapCursor c mod 18446744073709551616 = getCapCursor c"
  using uint_idem[of "Capability_address c"]
  by (auto simp: getCapCursor_def)

lemma mem_val_is_local_cap_Capability_global[simp]:
  "mem_val_is_local_cap CC ISA (mem_bytes_of_word (capToMemBits c)) tag \<longleftrightarrow> \<not>Capability_global c \<and> tag \<noteq> BU"
  by (cases tag) (auto simp: mem_val_is_local_cap_def bind_eq_Some_conv)

declare cap_size_def[simp]

lemma access_enabled_Store[derivable_capsE]:
  assumes "Capability_permit_store c"
    and "tag \<noteq> B0 \<longrightarrow> Capability_permit_store_cap c"
    and "mem_val_is_local_cap CC ISA v tag \<and> tag = B1 \<longrightarrow> Capability_permit_store_local_cap c"
    and "Capability_tag c" and "\<not>Capability_sealed c"
    and "paddr_in_mem_region c Store paddr sz"
    and "c \<in> derivable_caps s"
    and "tag = B0 \<or> tag = B1" and "length v = sz"
    and "tag \<noteq> B0 \<longrightarrow> address_tag_aligned ISA paddr \<and> sz = tag_granule ISA"
  shows "access_enabled s Store paddr sz v tag"
  using assms
  unfolding access_enabled_def authorises_access_def has_access_permission_def
  by (auto simp: get_cap_perms_def derivable_caps_def)

lemma access_enabled_Load[derivable_capsE]:
  assumes "Capability_permit_load c"
    and "tag \<noteq> B0 \<longrightarrow> Capability_permit_load_cap c"
    and "Capability_tag c" and "\<not>Capability_sealed c"
    and "paddr_in_mem_region c Load paddr sz"
    and "c \<in> derivable_caps s"
    and "tag \<noteq> B0 \<longrightarrow> address_tag_aligned ISA paddr \<and> sz = tag_granule ISA"
  shows "access_enabled s Load paddr sz v tag"
  using assms
  unfolding access_enabled_def authorises_access_def has_access_permission_def
  by (auto simp: get_cap_perms_def derivable_caps_def)

lemma [simp]: "isa.translate_address ISA = translate_address"
  by (auto simp: ISA_def)

fun acctype_of_bool where
  "acctype_of_bool True = LoadData"
| "acctype_of_bool False = StoreData"

lemma Run_raise_c2_exception_False[simp]:
  "Run (raise_c2_exception ex r) t a \<longleftrightarrow> False"
  "Run_inv (raise_c2_exception ex r) t a regs \<longleftrightarrow> False"
  unfolding Run_inv_def
  by (auto simp: raise_c2_exception_def raise_c2_exception8_def elim!: Run_bindE)

lemma Run_if_then_raise_c2_exception_else[simp]:
  "Run (if c then raise_c2_exception ex r else m) t a \<longleftrightarrow> \<not>c \<and> Run m t a"
  "Run_inv (if c then raise_c2_exception ex r else m) t a regs \<longleftrightarrow> \<not>c \<and> Run_inv m t a regs"
  by auto

lemma no_translation_tables[simp]: "translation_tables ISA t = {}"
  by (auto simp: ISA_def)

lemma Run_read_reg_DDC_derivable_caps:
  assumes "Run (read_reg DDC_ref) t c" and "{''DDC''} \<subseteq> accessible_regs s"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  by (auto elim!: Run_read_regE simp: DDC_ref_def derivable_caps_def intro!: derivable.Copy)

abbreviation empty_trace :: "register_value trace" where "empty_trace \<equiv> []"

lemma Run_inv_addrWrapper_access_enabled[derivable_capsE]:
  assumes "Run_inv (addrWrapper addr acctype width) t vaddr regs"
    and "translate_address (unat vaddr) acctype' empty_trace = Some paddr"
    and "{''DDC''} \<subseteq> accessible_regs s"
    and "acctype = MemAccessType_of_acctype acctype'"
    and "acctype' = Store \<longrightarrow> length v = nat sz"
    and "sz = wordWidthBytes width"
  shows "access_enabled (run s t) acctype' paddr (nat sz) v B0"
  using assms
  unfolding Run_inv_def addrWrapper_def checkDDCPerms_def Let_def
  unfolding access_enabled_def authorises_access_def has_access_permission_def paddr_in_mem_region_def
  apply (cases acctype')
    apply (auto elim!: Run_bindE simp: get_cap_perms_def getCapBounds_def address_range_def derivable_caps_def dest!: Run_read_reg_DDC_derivable_caps)
  subgoal for c
    apply (rule bexI[where x = c])
     apply (clarify)
     apply (rule exI[where x = "unat vaddr"])
    by auto
  subgoal for c
    apply (rule bexI[where x = c])
     apply (clarify)
     apply (rule exI[where x = "unat vaddr"])
    by auto
  done

lemma Run_read_reg_DDC_access_enabled:
  assumes "Run (read_reg DDC_ref) t c"
    and "{''DDC''} \<subseteq> accessible_regs s"
    and "Capability_tag c" and "\<not>Capability_sealed c"
    and "paddr_in_mem_region c acctype paddr sz"
    and "acctype = Store \<longrightarrow> length v = nat sz"
    and "acctype = Load \<and> Capability_permit_load c \<or> acctype = Store \<and> Capability_permit_store c"
  shows "access_enabled (run s t) acctype paddr sz v B0"
  using assms
  unfolding access_enabled_def authorises_access_def has_access_permission_def
  by (auto simp: get_cap_perms_def derivable_caps_def dest!: Run_read_reg_DDC_derivable_caps)

lemma translate_address_paddr_in_mem_region:
  assumes "translate_address (nat vaddr) is_load empty_trace = Some paddr"
    and "getCapBase c \<le> vaddr" and "vaddr + sz \<le> getCapTop c"
    and "0 \<le> vaddr"
  shows "paddr_in_mem_region c is_load paddr (nat sz)"
  using assms
  unfolding paddr_in_mem_region_def
  by (intro exI[where x = "nat vaddr"])
     (auto simp: paddr_in_mem_region_def address_range_def simp flip: nat_add_distrib)

lemma pos_mod_le[simp]:
  "0 < b \<Longrightarrow> a mod b \<le> (b :: int)"
  by (auto simp: le_less)

lemma mod_diff_mod_eq:
  fixes a b c :: int
  assumes "c dvd b" and "0 < b" and "0 < c"
  shows "(a mod b - a mod c) mod b = a mod b - a mod c"
  using assms
  apply (auto simp: dvd_def)
  by (smt Divides.pos_mod_bound assms(1) int_mod_eq' mod_mod_cancel unique_euclidean_semiring_numeral_class.pos_mod_sign)

lemma mod_le_dvd_divisor:
  fixes a b c :: int
  assumes "c dvd b" and "0 < b" and "0 < c"
  shows "a mod c \<le> a mod b"
  using assms
  apply (auto simp: dvd_def)
  by (metis assms(1) assms(2) mod_mod_cancel pos_mod_conj zmod_le_nonneg_dividend)

lemma Run_inv_addrWrapperUnaligned_access_enabled[derivable_capsE]:
  assumes "Run_inv (addrWrapperUnaligned addr acctype width) t (vaddr, sz) regs"
    and "translate_address (unat vaddr) acctype' empty_trace = Some paddr"
    and "{''DDC''} \<subseteq> accessible_regs s"
    and "acctype = MemAccessType_of_acctype acctype'"
    and "acctype' = Store \<longrightarrow> length v = nat sz"
  shows "access_enabled (run s t) acctype' paddr (nat sz) v B0"
  using assms
  unfolding Run_inv_def addrWrapperUnaligned_def unalignedBytesTouched_def checkDDCPerms_def Let_def
  by (cases width; cases acctype';
      auto elim!: Run_bindE Run_read_reg_DDC_access_enabled translate_address_paddr_in_mem_region
           simp: getCapBounds_def mod_mod_cancel mod_diff_mod_eq mod_le_dvd_divisor)


(*fun mask_unaligned :: "WordTypeUnaligned \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "mask_unaligned WR addr = addr AND NOT mask 2"
| "mask_unaligned DR addr = addr AND NOT mask 3"
| "mask_unaligned _ addr = addr"

fun size_unaligned :: "WordTypeUnaligned \<Rightarrow> 64 word \<Rightarrow> nat" where
  "size_unaligned WL addr = 4 - (unat addr mod 4)"
| "size_unaligned WR addr = unat addr mod 4 + 1"
| "size_unaligned DL addr = 8 - (unat addr mod 8)"
| "size_unaligned DR addr = unat addr mod 8 + 1"

lemma Run_inv_addrWrapperUnaligned_access_enabled:
  assumes "Run_inv (addrWrapperUnaligned addr acctype unaligned_width) t vaddr regs"
    and "\<exists>paddr. translate_address (unat vaddr) is_load [] = Some (unat paddr) \<and> mask_unaligned unaligned_width paddr = paddr_unaligned"
    and "{''DDC''} \<subseteq> accessible_regs s"
    and "acctype = acctype_of_bool is_load"
    and "is_load \<or> length v = nat sz"
    and "sz = size_unaligned unaligned_width vaddr"
  shows "access_enabled (run s t) is_load (unat paddr_unaligned) (nat sz) v B0"
  sorry*)

lemma access_enabled_run_mono:
  assumes "access_enabled s is_load paddr sz v tag"
  shows "access_enabled (run s t) is_load paddr sz v tag"
  using assms derivable_mono[OF accessed_caps_run_mono[where s = s and t = t]]
  unfolding access_enabled_def
  by blast

declare Run_inv_addrWrapperUnaligned_access_enabled[THEN access_enabled_run_mono, derivable_capsE]

lemma TLBTranslateC_translate_address_eq[simp]:
  assumes "Run_inv (TLBTranslateC vaddr acctype) t (paddr, noStoreCap) regs" (*and "\<not>is_fetch"*)
    and "acctype = MemAccessType_of_acctype acctype'"
  shows "translate_address (unat vaddr) acctype' t' = Some (unat paddr)"
proof -
  from assms have "Run_inv (translate_addressM (unat vaddr) acctype') t (unat paddr) regs"
    unfolding translate_addressM_def TLBTranslate_def bind_assoc Run_inv_def
    by (auto simp flip: uint_nat intro: Traces_bindI[of _ t _ _ "[]", simplified])
  then show ?thesis
    using determ_runs_translate_addressM
    by (auto simp: translate_address_def determ_the_result_eq)
qed

lemma TLBTranslate_translate_address_eq[simp]:
  assumes "Run_inv (TLBTranslate vaddr acctype) t paddr regs" (*and "\<not>is_fetch"*)
    and "acctype = MemAccessType_of_acctype acctype'"
  shows "translate_address (unat vaddr) acctype' t' = Some (unat paddr)"
proof -
  from assms have "Run_inv (translate_addressM (unat vaddr) acctype') t (unat paddr) regs"
    unfolding translate_addressM_def bind_assoc Run_inv_def
    by (auto simp flip: uint_nat intro: Traces_bindI[of _ t _ _ "[]", simplified])
  then show ?thesis
    using determ_runs_translate_addressM
    by (auto simp: translate_address_def determ_the_result_eq)
qed

(*lemma TLBTranslateC_LoadData_translate_address_eq[simp]:
  assumes "Run_inv (TLBTranslateC vaddr LoadData) t (paddr, noStoreCap) regs" (*and "\<not>is_fetch"*)
  shows "translate_address (unat vaddr) True t' = Some (unat paddr)"
proof -
  from assms have "Run_inv (translate_addressM (unat vaddr) True) t (unat paddr) regs"
    unfolding translate_addressM_def TLBTranslate_def bind_assoc Run_inv_def
    by (auto simp flip: uint_nat intro: Traces_bindI[of _ t _ _ "[]", simplified])
  then show ?thesis
    using determ_runs_translate_addressM
    by (auto simp: translate_address_def determ_the_result_eq)
qed*)

lemma traces_enabled_bind_prod_split[traces_enabled_combinatorI]:
  assumes "\<And>t a b. Run_inv m t (a, b) regs \<Longrightarrow> traces_enabled (f a b) (run s t) (the (updates_regs trans_regs t regs))"
    and "runs_preserve_invariant m" and "traces_enabled m s regs"
  shows "traces_enabled (m \<bind> (\<lambda>vars. let (a, b) = vars in f a b)) s regs"
  using assms
  by (auto intro: traces_enabled_bind)

lemma TLBTranslate_paddr_in_mem_region[derivable_capsE]:
  assumes "Run_inv (TLBTranslate vaddr acctype) t paddr regs"
    and "getCapBase c \<le> uint vaddr" and "uint vaddr + sz \<le> getCapTop c" and "0 \<le> sz"
    and "acctype = MemAccessType_of_acctype acctype'"
  shows "paddr_in_mem_region c acctype' (unat paddr) (nat sz)"
  using assms TLBTranslate_translate_address_eq[OF assms(1), where t' = "[]"]
  unfolding paddr_in_mem_region_def
  by (intro exI[where x = "unat vaddr"])
     (auto simp add: address_range_def unat_def simp flip: nat_add_distrib)

lemma TLBTranslateC_paddr_in_mem_region[derivable_capsE]:
  assumes "Run_inv (TLBTranslateC vaddr acctype) t (paddr, noStoreCap) regs"
    and "getCapBase c \<le> uint vaddr" and "uint vaddr + sz \<le> getCapTop c" and "0 \<le> sz"
    and "acctype = MemAccessType_of_acctype acctype'"
  shows "paddr_in_mem_region c acctype' (unat paddr) (nat sz)"
  using assms TLBTranslateC_translate_address_eq[OF assms(1), where t' = "[]"]
  unfolding paddr_in_mem_region_def
  by (intro exI[where x = "unat vaddr"])
     (auto simp add: address_range_def unat_def simp flip: nat_add_distrib)

(*lemma TLBTranslate_paddr_in_mem_region_add_vec_int:
  assumes "Run_inv (TLBTranslate vaddr acctype) t paddr regs"
    and "getCapBase c \<le> uint vaddr + offset"
    and "uint vaddr + offset + sz \<le> getCapTop c"
    and "0 \<le> sz" and "0 \<le> offset"
    and "uint vaddr mod 2^12 + offset < 2^12"
    (* and "getCapTop c < 2 ^ 64" *) and "uint (vaddr + word_of_int offset) = uint vaddr + offset"  and "uint (paddr + word_of_int offset) = uint paddr + offset"
    and "acctype = acctype_of_bool is_load"
  shows "paddr_in_mem_region c is_load (unat (add_vec_int paddr offset)) (nat sz)"
  using assms TLBTranslate_translate_address_eq[OF assms(1), where t' = "[]"]
  unfolding paddr_in_mem_region_def
  apply (intro exI[where x = "unat (add_vec_int vaddr offset)"])
  apply (auto simp add: address_range_def unat_def simp flip: nat_add_distrib (*uint_word_ariths uint_word_of_int simp flip: nat_add_distrib intro!: nat_mono*)) find_theorems uint "(+)" find_theorems "(mod)" "(<)" find_theorems "uint (word_of_int _)"
  find_theorems "(div)" "(mod)"
  find_theorems "(div)" "(>>)"
  find_theorems "_ div _ < _"
  find_theorems "(<<)" "2 ^ _"
  oops*)

(*lemma TLBTranslate_Load_paddr_in_mem_region[derivable_capsE]:
  assumes "Run_inv (TLBTranslate vaddr LoadData) t paddr regs"
    and "getCapBase c \<le> uint vaddr" and "uint vaddr + sz \<le> getCapTop c" and "0 \<le> sz"
  shows "paddr_in_mem_region c True (unat paddr) (nat sz)"
  using assms TLBTranslate_LoadData_translate_address_eq[OF assms(1), where t' = "[]"]
  unfolding paddr_in_mem_region_def
  by (intro exI[where x = "unat vaddr"])
     (auto simp add: address_range_def unat_def simp flip: nat_add_distrib)

lemma TLBTranslateC_Load_paddr_in_mem_region[derivable_capsE]:
  assumes "Run_inv (TLBTranslateC vaddr LoadData) t (paddr, noStoreCap) regs"
    and "getCapBase c \<le> uint vaddr" and "uint vaddr + sz \<le> getCapTop c" and "0 \<le> sz"
  shows "paddr_in_mem_region c True (unat paddr) (nat sz)"
  using assms TLBTranslateC_LoadData_translate_address_eq[OF assms(1), where t' = "[]"]
  unfolding paddr_in_mem_region_def
  by (intro exI[where x = "unat vaddr"])
     (auto simp add: address_range_def unat_def simp flip: nat_add_distrib)*)

lemma non_cap_exp_MEMea[non_cap_expI]:
  "non_cap_exp (MEMea addr sz)"
  unfolding MEMea_def write_mem_ea_def maybe_fail_def
  by (auto simp: non_cap_exp_def elim: Traces_cases)

lemma non_cap_exp_MEMea_conditional[non_cap_expI]:
  "non_cap_exp (MEMea_conditional addr sz)"
  unfolding MEMea_conditional_def write_mem_ea_def maybe_fail_def
  by (auto simp: non_cap_exp_def elim: Traces_cases)

lemma traces_enabled_write_mem_ea[traces_enabledI]:
  shows "traces_enabled (write_mem_ea BC_mword wk addr_sz addr sz) s regs"
  by (auto simp: write_mem_ea_def maybe_fail_def traces_enabled_def split: option.splits elim: Traces_cases)

lemma traces_enabled_write_mem[traces_enabledI]:
  assumes "access_enabled s Store (unat addr) (nat sz) (mem_bytes_of_word v) B0"
  shows "traces_enabled (write_mem BC_mword BC_mword wk addr_sz addr sz v) s regs"
  using assms
  by (auto simp: write_mem_def traces_enabled_def split: option.splits elim: Traces_cases)

lemma traces_enabled_write_memt[traces_enabledI]:
  assumes "access_enabled s Store (unat addr) (nat sz) (mem_bytes_of_word v) tag"
  shows "traces_enabled (write_memt BC_mword BC_mword wk addr sz v tag) s regs"
  using assms
  by (auto simp: write_memt_def traces_enabled_def split: option.splits elim: Traces_cases)

lemma traces_enabled_read_mem_bytes[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s Load (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (read_mem_bytes BC_mword BC_mword rk addr sz) s regs"
  using assms
  by (auto simp: read_mem_bytes_def maybe_fail_def traces_enabled_def split: option.splits elim: Traces_cases)

lemma traces_enabled_read_mem[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s Load (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (read_mem BC_mword BC_mword rk addr_sz addr sz) s regs"
  unfolding read_mem_def
  by (traces_enabledI assms: assms)

lemma traces_enabled_read_memt_bytes[traces_enabledI]:
  assumes "\<And>bytes tag. access_enabled s Load (unat addr) (nat sz) bytes tag"
  shows "traces_enabled (read_memt_bytes BC_mword BC_mword rk addr sz) s regs"
  using assms
  by (auto simp: read_memt_bytes_def maybe_fail_def traces_enabled_def split: option.splits elim: Traces_cases)

lemma traces_enabled_read_memt[traces_enabledI]:
  assumes "\<And>bytes tag. access_enabled s Load (unat addr) (nat sz) bytes tag"
  shows "traces_enabled (read_memt BC_mword BC_mword rk addr sz) s regs"
  unfolding read_memt_def
  by (traces_enabledI assms: assms)
(* *)

lemma traces_enabled_MEMea[traces_enabledI]:
  shows "traces_enabled (MEMea arg0 arg1) s regs"
  unfolding MEMea_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MEMea_conditional[traces_enabledI]:
  shows "traces_enabled (MEMea_conditional arg0 arg1) s regs"
  unfolding MEMea_conditional_def bind_assoc
  by (traces_enabledI)

lemma traces_enabled_MEMval[traces_enabledI]:
  assumes "access_enabled s Store (unat addr) (nat sz) (mem_bytes_of_word v) B0"
  shows "traces_enabled (MEMval addr sz v) s regs"
  unfolding MEMval_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s Load (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (MEMr addr sz) s regs"
  unfolding MEMr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MIPS_write[traces_enabledI]:
  assumes "access_enabled s Store (unat addr) (nat sz) (mem_bytes_of_word v) B0"
  shows "traces_enabled (MIPS_write addr sz v) s regs"
  unfolding MIPS_write_def write_ram_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MIPS_read[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s Load (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (MIPS_read addr sz) s regs"
  unfolding MIPS_read_def read_ram_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr_reserve[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s Load (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (MEMr_reserve addr sz) s regs"
  unfolding MEMr_reserve_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMval_conditional[traces_enabledI]:
  assumes "access_enabled s Store (unat addr) (nat sz) (mem_bytes_of_word v) B0"
  shows "traces_enabled (MEMval_conditional addr sz v) s regs"
  unfolding MEMval_conditional_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr_wrapper[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s Load (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (MEMr_wrapper addr sz) s regs"
  unfolding MEMr_wrapper_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr_reserve_wrapper[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s Load (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (MEMr_reserve_wrapper addr sz) s regs"
  unfolding MEMr_reserve_wrapper_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr_tagged[traces_enabledI]:
  assumes "\<And>bytes tag. tag \<noteq> B0 \<longrightarrow> allow_tag \<Longrightarrow> access_enabled s Load (unat addr) (nat sz) bytes tag"
  shows "traces_enabled (MEMr_tagged addr sz allow_tag) s regs"
  unfolding MEMr_tagged_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr_tagged_reserve[traces_enabledI]:
  assumes "\<And>bytes tag. tag \<noteq> B0 \<longrightarrow> allow_tag \<Longrightarrow> access_enabled s Load (unat addr) (nat sz) bytes tag"
  shows "traces_enabled (MEMr_tagged_reserve addr sz allow_tag) s regs"
  unfolding MEMr_tagged_reserve_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMw_tagged[traces_enabledI]:
  assumes "access_enabled s Store (unat addr) (nat sz) (mem_bytes_of_word v) (bitU_of_bool tag)"
  shows "traces_enabled (MEMw_tagged addr sz tag v) s regs"
  unfolding MEMw_tagged_def MEMval_tagged_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMw_tagged_conditional[traces_enabledI]:
  assumes "access_enabled s Store (unat addr) (nat sz) (mem_bytes_of_word v) (bitU_of_bool tag)"
  shows "traces_enabled (MEMw_tagged_conditional addr sz tag v) s regs"
  unfolding MEMw_tagged_conditional_def MEMval_tagged_conditional_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMw_wrapper[traces_enabledI]:
  assumes "access_enabled s Store (unat addr) (nat sz) (mem_bytes_of_word v) B0"
  shows "traces_enabled (MEMw_wrapper addr sz v) s regs"
  unfolding MEMw_wrapper_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMw_conditional_wrapper[traces_enabledI]:
  assumes "access_enabled s Store (unat addr) (nat sz) (mem_bytes_of_word v) B0"
  shows "traces_enabled (MEMw_conditional_wrapper addr sz v) s regs"
  unfolding MEMw_conditional_wrapper_def bind_assoc
  by (traces_enabledI assms: assms)

declare Run_inv_addrWrapper_access_enabled[THEN access_enabled_run_mono, derivable_capsE]
(* declare Run_inv_addrWrapperUnaligned_access_enabled[THEN access_enabled_run_mono, derivable_capsE] *)

lemma traces_enabled_execute_Store[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_Store arg0 arg1 arg2 arg3 arg4) s regs"
  unfolding execute_Store_def bind_assoc
  by (traces_enabledI assms: assms)

(*lemma uint_mod4_ucast:
  fixes w :: "'a::len word"
  assumes "LENGTH('a) \<ge> 2"
  shows "uint w mod 4 = uint (ucast w :: 2 word)"
  using assms
  by (auto simp: uint_and_mask min_def)

lemma unat_mod4_ucast:
  fixes w :: "'a::len word"
  assumes "LENGTH('a) \<ge> 2"
  shows "unat w mod 4 = unat (ucast w :: 2 word)"
  using assms
  by (auto simp: unat_def uint_and_mask min_def nat_mod_distrib)

lemma uint_mod8_ucast:
  fixes w :: "'a::len word"
  assumes "LENGTH('a) \<ge> 3"
  shows "uint w mod 8 = uint (ucast w :: 3 word)"
  using assms
  by (auto simp: uint_and_mask min_def)

lemma unat_mod8_ucast:
  fixes w :: "'a::len word"
  assumes "LENGTH('a) \<ge> 3"
  shows "unat w mod 8 = unat (ucast w :: 3 word)"
  using assms
  by (auto simp: unat_def uint_and_mask min_def nat_mod_distrib)*)

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

declare traces_enabled_foreachM_inv[where P = "\<lambda>vars s regs. True", simplified, traces_enabledI]
thm traces_enabled_foreachM_inv[where s = s and P = "\<lambda>vars s' regs'. derivable_caps s \<subseteq> derivable_caps s'" for s]

lemma uint_cacheline_plus_cap_size:
  assumes "getCapCursor c = 128 * q" and "0 \<le> x" and "x \<le> 3"
  shows "uint (to_bits 64 128 * to_bits 64 q + (word_of_int (x * 32) :: 64 word)) = 128 * q + x * 32"
proof -
  have "128 * q < 2^64" and *: "0 \<le> 128 * q"
    using uint_bounded[of "Capability_address c"]
    unfolding assms(1)[symmetric] getCapCursor_def
    by (auto)
  moreover have "0 \<le> q"
    using *
    by auto
  ultimately show ?thesis
    using assms
    by (auto simp: uint_word_ariths getCapCursor_def uint_word_of_int)
qed

lemma traces_enabled_execute_CLoadTags[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CLoadTags arg0 arg1) s regs"
  unfolding execute_CLoadTags_def bind_assoc
  apply (traces_enabledI_with \<open>-\<close> intro: traces_enabled_foreachM_inv[where s = s and P = "\<lambda>vars s' regs'. derivable_caps s \<subseteq> derivable_caps s'" for s])
  apply (derivable_caps_step)
  apply (derivable_caps_step)
  apply (derivable_caps_step)
  apply (derivable_caps_step)
  apply (derivable_caps_step)
  apply (auto)[]
  apply (auto)[]
  apply (auto)[]
  (*apply (erule TLBTranslate_paddr_in_mem_region_add_vec_int)*)
  apply (derivable_caps_step)
  apply (auto simp: caps_per_cacheline_def uint_cacheline_plus_cap_size)[]
  apply (auto simp: caps_per_cacheline_def uint_cacheline_plus_cap_size)[]
  apply (auto simp: caps_per_cacheline_def)[]
  apply (auto simp: caps_per_cacheline_def)[]
  (* apply (auto simp: caps_per_cacheline_def)[] *)
  (* apply (auto simp: caps_per_cacheline_def)[] *)
  (* defer *)
  (* apply (auto simp: caps_per_cacheline_def)[] *)
  apply (derivable_caps_step)
  apply (elim set_mp)
  apply (derivable_capsI assms: assms)[]
  apply (auto simp: caps_per_cacheline_def)[]
  (* apply (auto simp: caps_per_cacheline_def)[] *)
  apply (elim subset_trans)
  apply (intro derivable_caps_run_mono)
  apply (auto simp: caps_per_cacheline_def)[]
  done

lemma traces_enabled_execute_CLoadLinked[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CLoadLinked arg0 arg1 arg2 arg3) s regs"
  unfolding execute_CLoadLinked_def bind_assoc
  by (traces_enabledI assms: assms)

lemma [simp]: "integerOfString ''18446744073709551616'' = 18446744073709551616"
  by eval

lemma traces_enabled_execute_CLoad[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CLoad arg0 arg1 arg2 arg3 arg4 arg5) s regs"
  unfolding execute_CLoad_def bind_assoc
  by (traces_enabledI assms: assms)

(*lemma preserves_invariant_write_reg_CapRegs[preserves_invariantI]:
  assumes "i \<in> {0..31}"
  shows "traces_preserve_invariant (write_reg (access_list_dec CapRegs i) c)"
  using assms
  unfolding upto_31_unfold
  by (elim insertE; intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg)
     (auto simp: CapRegs_def register_defs inv_regs_def)

lemma preserves_invariant_writeCapReg[preserves_invariantI]:
  "traces_preserve_invariant (writeCapReg n c)"
  unfolding writeCapReg_def capToString_def
  by (preserves_invariantI)*)

lemma traces_enabled_execute_CLLC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CLLC arg0 arg1) s regs"
  unfolding execute_CLLC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CCLC[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CCLC arg0 arg1) s regs"
  unfolding execute_CCLC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_execute_CClearTags[traces_enabledI]:
  assumes "{''PCC''} \<subseteq> accessible_regs s" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (execute_CClearTags arg0) s regs"
  unfolding execute_CClearTags_def bind_assoc
  (* by (traces_enabledI assms: assms) *)
  apply (traces_enabledI_with \<open>-\<close>)
  apply (derivable_caps_step)
  apply (derivable_caps_step)
  apply (derivable_caps_step)
  apply (derivable_caps_step)
  apply (auto)[]
  apply (auto)[]
  apply (auto)[]
  apply (auto)[]
  defer
  defer
  apply (auto)[]
  apply (auto)[]
  apply (auto)[]
  apply (derivable_caps_step)
  apply (derivable_caps_step)
  apply (derivable_caps_step)
  sorry

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

lemma traces_enabled_instr_sem[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
    and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (instr_sem ISA instr) s regs"
  by (cases instr rule: execute.cases; simp; use nothing in \<open>traces_enabledI assms: assms\<close>)

lemma hasTrace_instr_mem_axioms:
  assumes "hasTrace t (instr_sem ISA instr)"
    and "reads_regs_from trans_regs t regs" and "trans_inv regs"
    and "instr_raises_ex ISA instr t \<longrightarrow> ex_traces"
  shows "store_mem_axiom CC ISA t"
    and "store_tag_axiom CC ISA t"
    and "load_mem_axiom CC ISA False t"
  using assms
  by (intro traces_enabled_mem_axioms[where m = "instr_sem ISA instr" and regs = regs] traces_enabled_instr_sem;
      auto)+

end

context CHERI_MIPS_Mem_Fetch_Automaton
begin

lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]

lemmas non_mem_exp_traces_enabled[traces_enabledI] = non_mem_expI[THEN non_mem_exp_traces_enabledI]

(*lemma
  shows "traces_enabled (fetch u) s regs"
  unfolding fetch_def bind_assoc
  apply (traces_enabledI_with \<open>-\<close>)
  oops*)

thm Run_bind_trace_enabled traces_enabled_bind

lemma Run_inv_bind_trace_enabled:
  assumes "Run_inv (m \<bind> f) t a regs" and "runs_preserve_invariant m"
    and "\<And>tm tf am. t = tm @ tf \<Longrightarrow> Run_inv m tm am regs \<Longrightarrow> trace_enabled s tm"
    and "\<And>tm tf am. t = tm @ tf \<Longrightarrow> Run_inv m tm am regs \<Longrightarrow> Run_inv (f am) tf a (the (updates_regs trans_regs tm regs)) \<Longrightarrow> trace_enabled (run s tm) tf"
  shows "trace_enabled s t"
  using assms
  by (elim Run_inv_bindE) (auto simp: trace_enabled_append_iff)

lemma traces_enabled_read_mem_bytes[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s Fetch (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (read_mem_bytes BC_mword BC_mword rk addr sz) s regs"
  using assms
  by (auto simp: read_mem_bytes_def maybe_fail_def traces_enabled_def split: option.splits elim: Traces_cases)

lemma traces_enabled_MEMr_wrapper[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s Fetch (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (MEMr_wrapper addr sz) s regs"
  unfolding MEMr_wrapper_def MEMr_def read_mem_def
  by (traces_enabledI assms: assms)

(*lemma Run_inv_traces_enabled_trace_enabled:
  assumes "Run_inv m t a regs" and "traces_enabled m s regs"
  shows "trace_enabled s t"
  using assms
  unfolding Run_inv_def traces_enabled_def
  by blast*)

lemma [simp]: "translation_tables ISA t = {}"
  by (auto simp: ISA_def)

lemma [simp]: "isa.translate_address ISA vaddr Fetch t = translate_address vaddr Fetch t"
  by (auto simp: ISA_def)

lemma access_enabled_FetchI:
  assumes "c \<in> derivable_caps s" and "Capability_tag c" and "\<not>Capability_sealed c"
    and "translate_address vaddr Fetch ([] :: register_value trace) = Some paddr"
    and "vaddr \<ge> nat (getCapBase c)" and "vaddr + sz \<le> nat (getCapTop c)"
    and "Capability_permit_execute c" and "sz > 0"
  shows "access_enabled s Fetch paddr sz bytes B0"
  using assms
  by (auto simp: access_enabled_defs derivable_caps_def address_range_def get_cap_perms_def)

lemma Run_inv_no_reg_writes_to_updates_regs_inv[simp]:
  assumes "Run_inv m t a regs" and "no_reg_writes_to Rs m"
  shows "updates_regs Rs t regs' = Some regs'"
  using assms
  unfolding Run_inv_def
  by auto

lemma Run_inv_read_regE:
  assumes "Run_inv (read_reg r) t v regs"
  obtains rv where "t = [E_read_reg (name r) rv]" and "of_regval r rv = Some v"
  using assms
  unfolding Run_inv_def
  by (auto elim!: Run_read_regE)

lemma [simp]: "Run_inv (SignalExceptionBadAddr ex badAddr) t a regs \<longleftrightarrow> False"
  by (auto simp: Run_inv_def)

lemma [simp]: "''PCC'' \<in> trans_regs"
  by (auto simp: trans_regs_def)

lemma runs_no_reg_writes_to_incrementCP0Count[runs_no_reg_writes_toI, simp]:
  assumes "{''TLBRandom'', ''CP0Count'', ''CP0Cause''} \<inter> Rs = {}"
  shows "runs_no_reg_writes_to Rs (incrementCP0Count u)"
  using assms
  unfolding incrementCP0Count_def Let_def bind_assoc
  by (no_reg_writes_toI simp: register_defs)

lemma [simp]: "runs_no_reg_writes_to trans_regs (incrementCP0Count u)"
  by (auto simp: trans_regs_def)
find_theorems updates_regs no_reg_writes_to

lemma Run_inv_runs_no_reg_writes_to_updates_regs_inv[simp]:
  assumes "Run_inv m t a regs"
    and "runs_no_reg_writes_to trans_regs m"
  shows "updates_regs trans_regs t regs = Some regs"
  using assms
proof -
  have "\<forall>r \<in> trans_regs. \<forall>v. E_write_reg r v \<notin> set t"
    using assms
    by (auto simp: runs_no_reg_writes_to_def Run_inv_def)
  then show "updates_regs trans_regs t regs = Some regs"
    by (induction trans_regs t regs rule: updates_regs.induct) auto
qed

lemma Run_inv_read_reg_PCC[simp]:
  assumes "Run_inv (read_reg PCC_ref) t c regs"
  shows "regstate.PCC regs = c"
  using assms
  by (auto simp: Run_inv_def register_defs regval_of_Capability_def elim!: Run_read_regE)

lemma foo:
  assumes "\<not> getCapTop c < getCapBase c + uint vaddr + 4" and "getCapTop c \<le> pow2 64"
  shows "unat (to_bits 64 (getCapBase c + uint vaddr) :: 64 word) = nat (getCapBase c + uint vaddr) \<and> nat (getCapBase c) \<le> nat (getCapBase c + uint vaddr) \<and> nat (getCapBase c + uint vaddr) + 4 = nat (getCapBase c + uint vaddr + 4)"
  using assms
  by (auto simp: nat_add_distrib getCapBase_def)

lemma Run_inv_TranslatePC_access_enabled_Fetch:
  assumes "Run_inv (TranslatePC vaddr) t paddr regs" (*and "reads_regs_from {''PCC''} t pcc_state"*)
    and "regstate.PCC regs \<in> derivable_caps s"
  shows "access_enabled (run s t) Fetch (unat paddr) (nat 4) bytes B0"
proof -
  { fix c
    assume "\<not> getCapTop c < getCapBase c + uint vaddr + 4" and "getCapTop c \<le> pow2 64"
    then have "unat (to_bits 64 (getCapBase c + uint vaddr) :: 64 word) = nat (getCapBase c + uint vaddr) \<and> nat (getCapBase c) \<le> nat (getCapBase c + uint vaddr) \<and> nat (getCapBase c + uint vaddr) + 4 = nat (getCapBase c + uint vaddr + 4)"
      by (auto simp: nat_add_distrib getCapBase_def)
  }
  from this[of "regstate.PCC regs"]
  show ?thesis
    using assms
    unfolding TranslatePC_def bind_assoc Let_def
    by (intro access_enabled_FetchI[where c = "regstate.PCC regs" and vaddr = "unat (to_bits 64 (getCapBase (regstate.PCC regs) + uint vaddr) :: 64 word)"])
       (auto elim!: Run_inv_bindE Run_inv_ifE intro: preserves_invariantI traces_runs_preserve_invariantI derivable_caps_run_imp simp add: getCapBounds_def simp del: unat_to_bits dest!: TLBTranslate_Instruction_translate_address_eq[where t' = "[] :: register_value trace"])
qed

lemma [simp]:
  "name UART_WRITTEN_ref \<notin> trans_regs"
  "name InstCount_ref  \<notin> trans_regs"
  "name NextPCC_ref  \<notin> trans_regs"
  by (auto simp: trans_regs_def register_defs)

lemma Run_write_regE:
  assumes "Run (write_reg r v) t a"
  obtains "t = [E_write_reg (name r) (regval_of r v)]"
  using assms
  by (auto simp: write_reg_def elim!: Write_reg_TracesE)

lemma Run_inv_write_reg_PCC_updates_regs[simp]:
  assumes "Run_inv (write_reg PCC_ref c) t a regs"
  shows "updates_regs trans_regs t regs' = Some (regs'\<lparr>regstate.PCC := c\<rparr>)"
  using assms
  unfolding Run_inv_def
  by (auto simp: register_defs elim: Run_write_regE)

lemma Run_inv_read_reg_NextPCC_derivable_caps[derivable_capsE]:
  assumes "Run_inv (read_reg NextPCC_ref) t c regs"
    and "{''NextPCC''} \<subseteq> accessible_regs s"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  by (auto simp: step_defs register_defs derivable_caps_def intro: derivable.Copy elim!: Run_inv_read_regE)

lemma Run_inv_cp2_next_pc_PCC_derivable:
  assumes "Run_inv (cp2_next_pc ()) t a regs"
    and "{''NextPCC''} \<subseteq> accessible_regs s"
  shows "regstate.PCC (the (updates_regs trans_regs t regs)) \<in> derivable_caps (run s t)"
  using assms(1)
  unfolding cp2_next_pc_def
  by (auto elim!: Run_inv_bindE Run_inv_ifE intro: preserves_invariantI traces_runs_preserve_invariantI simp: regstate_simp)
     (derivable_capsI assms: assms(2))+

lemma traces_enabled_fetch[traces_enabledI]:
  assumes "{''NextPCC''} \<subseteq> accessible_regs s"
  shows  "traces_enabled (fetch u) s regs"
  unfolding fetch_def bind_assoc
  by (traces_enabledI elim: Run_inv_TranslatePC_access_enabled_Fetch Run_inv_cp2_next_pc_PCC_derivable assms: assms)

lemma traces_enabled_instr_fetch[traces_enabledI]:
  assumes "{''NextPCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (instr_fetch ISA) s regs"
  unfolding ISA_simps
  by (traces_enabledI assms: assms)

lemma hasTrace_fetch_mem_axioms:
  assumes "hasTrace t (instr_fetch ISA)"
    and "reads_regs_from trans_regs t regs" and "trans_inv regs"
    and "fetch_raises_ex ISA t \<longrightarrow> ex_traces"
  shows "store_mem_axiom CC ISA t"
    and "store_tag_axiom CC ISA t"
    and "load_mem_axiom CC ISA True t"
  using assms
  by (intro traces_enabled_mem_axioms[where m = "instr_fetch ISA" and regs = regs] traces_enabled_instr_fetch; auto)+

(* sublocale Reg_Automaton: CHERI_MIPS_Reg_Fetch_Automaton trans_regstate ex_traces .. *)

end

locale CHERI_MIPS_Reg_Fetch_Automaton = CHERI_MIPS_Fixed_Trans +
  fixes ex_traces :: bool
begin

sublocale Reg_Automaton?: Write_Cap_Inv_Automaton CC ISA ex_traces False get_regval set_regval trans_inv trans_regs ..

sublocale CHERI_MIPS_Axiom_Inv_Automaton where enabled = enabled and invariant = trans_inv and inv_regs = trans_regs and translate_address = translate_address ..

sublocale Mem_Automaton: CHERI_MIPS_Mem_Fetch_Automaton trans_regstate ex_traces ..

lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]

definition "PCC_accessible s regs \<equiv> ''PCC'' \<in> accessible_regs s \<or> regstate.PCC regs \<in> derivable_caps s"

lemma
  assumes "Run_inv (read_reg PCC_ref) t c regs" and "PCC_accessible s regs"
  shows "c \<in> derivable_caps (run s t)"
  using assms derivable_mono[where C = C and C' = "C \<union> C'" for C C']
  unfolding Run_inv_def PCC_accessible_def derivable_caps_def
  by (fastforce simp: register_defs regval_of_Capability_def elim!: Run_read_regE intro: derivable.Copy)

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
    and "traces_enabled (write_reg NextPCC_ref c) s regs"
    and "traces_enabled (write_reg PCC_ref c) s regs"
  using assms
  by (intro traces_enabled_write_reg; auto simp: register_defs derivable_caps_def)+

lemma traces_enabled_write_reg_CapCause[traces_enabledI]:
  "traces_enabled (write_reg CapCause_ref c) s regs"
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

lemma traces_enabled_cp2_next_pc[traces_enabledI]:
  assumes "{''DelayedPCC'', ''NextPCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (cp2_next_pc u) s regs"
  unfolding cp2_next_pc_def bind_assoc
  by (traces_enabledI assms: assms simp: register_defs)

lemma traces_enabled_set_next_pcc_ex:
  assumes arg0: "arg0 \<in> exception_targets ISA (read_from_KCC s)" and ex: "ex_traces"
  shows "traces_enabled (set_next_pcc arg0) s regs"
  unfolding set_next_pcc_def bind_assoc
  by (traces_enabledI intro: traces_enabled_write_reg assms exception_targets_run_imp simp: register_defs)

lemma read_reg_PCC_from_iff:
  assumes "reads_regs_from trans_regs t regs"
  defines "pcc \<equiv> regstate.PCC regs"
    and "e \<equiv> E_read_reg ''PCC'' (Regval_Capability (regstate.PCC regs))"
  shows "Run (read_reg PCC_ref) t c \<longleftrightarrow> (c = pcc \<and> t = [e])"
  using assms
  by (auto simp: read_reg_def register_defs regval_of_Capability_def elim!: Read_reg_TracesE)

lemma read_reg_PCC_from_bind_iff:
  assumes "reads_regs_from trans_regs t regs"
  defines "pcc \<equiv> regstate.PCC regs"
    and "e \<equiv> E_read_reg ''PCC'' (Regval_Capability (regstate.PCC regs))"
  shows "Run (read_reg PCC_ref \<bind> f) t a \<longleftrightarrow> (\<exists>tf. t = e # tf \<and> Run (f pcc) tf a)"
  using assms
  by (auto elim!: Run_bindE simp: read_reg_PCC_from_iff regstate_simp
           intro!: Traces_bindI[of "read_reg PCC_ref" "[e]", unfolded e_def, simplified])

lemmas read_reg_PCC_from_iffs = read_reg_PCC_from_iff read_reg_PCC_from_bind_iff

lemma Run_read_accessible_PCC_derivable:
  assumes "Run (read_reg PCC_ref) t c" and "reads_regs_from trans_regs t regs" and "PCC_accessible s regs"
  shows "c \<in> derivable_caps (run s t)"
  using assms derivable_mono[OF Un_upper1, THEN in_mono]
  by (auto simp: register_defs regval_of_Capability_def derivable_caps_def PCC_accessible_def
           elim!: Run_read_regE intro: derivable.Copy)

lemma Run_write_derivable_PCC_accessible:
  assumes "Run (write_reg PCC_ref c) t a" and "reads_regs_from Rs t regs" and "''PCC'' \<in> Rs"
    and "c \<in> derivable_caps s"
  shows "PCC_accessible (run s t) (the (updates_regs Rs t regs))"
  using assms
  by (auto simp: PCC_accessible_def register_defs derivable_caps_def elim!: Mem_Automaton.Run_write_regE) 

lemma Run_PCC_accessible_run:
  assumes "Run m t a" and "runs_no_reg_writes_to {''PCC''} m" and "PCC_accessible s regs"
  shows "PCC_accessible (run s t) regs"
  using assms derivable_caps_run_mono[of s t]
  by (auto simp: PCC_accessible_def accessible_regs_def Run_runs_no_reg_writes_written_regs_eq)

lemmas Run_inv_PCC_accessible_run = Run_inv_RunI[THEN Run_PCC_accessible_run]

lemma Run_runs_no_reg_writes_to_updates_regs_inv[simp]:
  assumes "Run m t a" and "reads_regs_from Rs t regs" and "runs_no_reg_writes_to Rs m"
  shows "updates_regs Rs t regs = Some regs"
proof -
  have "\<forall>r \<in> Rs. \<forall>v. E_write_reg r v \<notin> set t"
    using assms
    by (auto simp: runs_no_reg_writes_to_def Run_inv_def)
  then show "updates_regs Rs t regs = Some regs"
    by (induction Rs t regs rule: updates_regs.induct) auto
qed

lemma Run_runs_no_reg_writes_to_get_regval_eq[simp]:
  assumes "Run m t a" and "reads_regs_from Rs t regs" and "runs_no_reg_writes_to {r} m"
  shows "get_regval r (the (updates_regs Rs t regs)) = get_regval r regs"
proof -
  have "\<forall>v. E_write_reg r v \<notin> set t"
    using assms
    by (auto simp: runs_no_reg_writes_to_def Run_inv_def)
  then show ?thesis
    using assms(2)
    by (induction Rs t regs rule: updates_regs.induct)
       (auto split: Option.bind_splits if_splits simp: get_ignore_set_regval)
qed

lemma Run_PCC_accessible_update:
  assumes "Run m t a" and "reads_regs_from Rs t regs" and "runs_no_reg_writes_to {''PCC''} m"
    and "PCC_accessible s regs"
  shows "PCC_accessible s (the (updates_regs Rs t regs))"
proof -
  have "get_regval ''PCC'' (the (updates_regs Rs t regs)) = get_regval ''PCC'' regs"
    using assms
    by auto
  then show ?thesis
    using \<open>PCC_accessible s regs\<close>
    by (auto simp: PCC_accessible_def register_defs regval_of_Capability_def)
qed

lemma Run_inv_PCC_accessible_update:
  assumes "Run_inv m t a regs" and "runs_no_reg_writes_to {''PCC''} m"
    and "PCC_accessible s regs"
  shows "PCC_accessible s (the (updates_regs trans_regs t regs))"
  using assms
  by (intro Run_PCC_accessible_update) (auto simp: Run_inv_def)

lemma Run_PCC_accessible_run_update:
  assumes "Run m t a" and "reads_regs_from Rs t regs" and "runs_no_reg_writes_to {''PCC''} m"
    and "PCC_accessible s regs"
  shows "PCC_accessible (run s t) (the (updates_regs Rs t regs))"
  using assms
  by (blast intro: Run_PCC_accessible_run Run_PCC_accessible_update)

lemma Run_inv_PCC_accessible_run_update:
  assumes "Run_inv m t a regs" and "runs_no_reg_writes_to {''PCC''} m"
    and "PCC_accessible s regs"
  shows "PCC_accessible (run s t) (the (updates_regs trans_regs t regs))"
  using assms
  by (blast intro: Run_inv_PCC_accessible_update Run_inv_PCC_accessible_run)

lemmas Run_PCC_accessibleE[derivable_capsE] =
  Run_PCC_accessible_run_update Run_PCC_accessible_update Run_PCC_accessible_run
  Run_inv_PCC_accessible_run_update Run_inv_PCC_accessible_update Run_inv_PCC_accessible_run

lemma (in Register_State) reads_regs_bind_updates_regs_the[simp]:
  assumes "reads_regs_from R t s"
  shows "Option.bind (updates_regs R t s) f = f (the (updates_regs R t s))"
  using assms
  by (elim reads_regs_from_updates_regs_Some) auto

find_theorems NextPCC_ref derivable_caps

lemma Run_inv_cp2_next_pc_PCC_accessible:
  assumes "Run_inv (cp2_next_pc u) t a regs" and "{''NextPCC''} \<subseteq> accessible_regs s"
  shows "PCC_accessible (run s t) (the (updates_regs trans_regs t regs))"
proof -
  have *: "PCC_accessible s (regs\<lparr>regstate.PCC := c\<rparr>)" if "c \<in> derivable_caps s" for s c and regs :: regstate
    using that
    by (auto simp: PCC_accessible_def)
  show ?thesis
    using assms
    unfolding cp2_next_pc_def bind_assoc
    by (auto elim!: Run_inv_bindE Run_inv_ifE intro: preserves_invariantI traces_runs_preserve_invariantI intro!: * simp: regstate_simp)
       (derivable_capsI)+
qed

lemma SignalException_trace_enabled:
  assumes "(SignalException arg0, t, m') \<in> Traces" and "reads_regs_from trans_regs t regs"
    and "PCC_accessible s regs" and ex: "ex_traces"
  shows "trace_enabled s t"
proof -
  note [trace_elim] = non_cap_expI[THEN non_cap_exp_trace_enabledI]
  have [trace_elim]: "(read_reg PCC_ref, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t" for s t and m' :: "Capability M"
    by (elim read_reg_trace_enabled; auto simp: register_defs)
  have [trace_elim]: "(read_reg KCC_ref, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t" for s t and m' :: "Capability M"
    by (elim read_reg_trace_enabled; auto simp: register_defs intro: ex)
  have [trace_elim]: "(write_reg EPCC_ref c, t, m') \<in> Traces \<Longrightarrow> c \<in> derivable_caps s \<Longrightarrow> trace_enabled s t" for s t c and m' :: "unit M"
    by (elim write_reg_trace_enabled) (auto simp: derivable_caps_def register_defs)
  have [trace_elim]: "(set_next_pcc c, t, m') \<in> Traces \<Longrightarrow> c \<in> exception_targets ISA (read_from_KCC s) \<Longrightarrow> trace_enabled s t" for s t c and m' :: "unit M"
    unfolding set_next_pcc_def
    by (elim trace_elim write_reg_trace_enabled)
       (auto simp: register_defs intro: ex exception_targets_run_imp)
  have [trace_elim]: "(set_CauseReg_BD CP0Cause_ref x, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t" for s t x m'
    unfolding set_CauseReg_BD_def
    by (elim trace_elim)
  have [trace_elim]: "(set_CauseReg_ExcCode CP0Cause_ref x, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t" for s t x m'
    unfolding set_CauseReg_ExcCode_def
    by (elim trace_elim)
  have [trace_elim]: "(set_StatusReg_EXL CP0Status_ref x, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t" for s t x m'
    unfolding set_StatusReg_EXL_def
    by (elim trace_elim)
  have read_KCC_ex_target: "c \<in> exception_targets ISA (read_from_KCC (Mem_Automaton.run s t))"
    if "Run (read_reg KCC_ref) t c" for s t c
    using that
    by (auto elim!: Run_read_regE simp: register_defs)
  note [derivable_capsE] = Run_read_accessible_PCC_derivable[where regs = regs]
  show ?thesis
    using assms(1-3)
    unfolding SignalException_def bind_assoc
    by (elim trace_elim read_KCC_ex_target)
       (derivable_capsI simp: regstate_simp read_reg_PCC_from_iffs)
qed

lemma traces_enabled_SignalException[traces_enabledI]:
  assumes "PCC_accessible s regs"
  shows "traces_enabled (SignalException arg0 :: 'a M) s regs"
proof cases
  assume ex: "ex_traces"
  then show ?thesis
    using assms SignalException_trace_enabled
    unfolding traces_enabled_def
    by blast
next
  assume "\<not> ex_traces"
  then show ?thesis
    unfolding traces_enabled_def finished_def isException_def
    by auto
qed

lemma [simp]:
  "name CP0Count_ref = ''CP0Count''"
  "name TLBRandom_ref = ''TLBRandom''"
  "name CP0BadVAddr_ref = ''CP0BadVAddr''"
  "name CapCause_ref = ''CapCause''"
  "name BranchPending_ref = ''BranchPending''"
  "name NextInBranchDelay_ref = ''NextInBranchDelay''"
  "name InBranchDelay_ref = ''InBranchDelay''"
  "name PC_ref = ''PC''"
  "name NextPC_ref = ''NextPC''"
  "name InstCount_ref = ''InstCount''"
  "name CurrentInstrBits_ref = ''CurrentInstrBits''"
  by (auto simp: register_defs)

lemma [simp]:
  "''CP0Count'' \<notin> trans_regs"
  "''TLBRandom'' \<notin> trans_regs"
  "''CP0BadVAddr'' \<notin> trans_regs"
  "''CapCause'' \<notin> trans_regs"
  "''BranchPending'' \<notin> trans_regs"
  "''NextInBranchDelay'' \<notin> trans_regs"
  "''InBranchDelay'' \<notin> trans_regs"
  "''PC'' \<notin> trans_regs"
  "''NextPC'' \<notin> trans_regs"
  "''InstCount'' \<notin> trans_regs"
  "''CurrentInstrBits'' \<notin> trans_regs"
  by (auto simp: trans_regs_def)

lemma traces_enabled_SignalExceptionBadAddr[traces_enabledI]:
  assumes "PCC_accessible s regs"
  shows "traces_enabled (SignalExceptionBadAddr arg0 arg1) s regs"
  unfolding SignalExceptionBadAddr_def
  by (traces_enabledI assms: assms)

lemma SignalExceptionTLB_trace_enabled:
  assumes "(SignalExceptionTLB arg0 arg1 :: 'a M, t, m') \<in> Traces" and "reads_regs_from trans_regs t regs"
    and "PCC_accessible s regs" and ex: "ex_traces"
  shows "trace_enabled s t"
proof -
  have [trace_elim]: "(write_reg CP0BadVAddr_ref v, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t" for s t v and m' :: "unit M"
    by (auto elim!: write_reg_trace_enabled simp: register_defs)
  have [trace_elim]: "(set_ContextReg_BadVPN2 TLBContext_ref v, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t" for s t v and m' :: "unit M"
    by (auto elim!: trace_elim read_reg_trace_enabled write_reg_trace_enabled simp: set_ContextReg_BadVPN2_def register_defs)
  have [trace_elim]: "(set_XContextReg_XBadVPN2 TLBXContext_ref v, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t" for s t v and m' :: "unit M"
    by (auto elim!: trace_elim read_reg_trace_enabled write_reg_trace_enabled simp: set_XContextReg_XBadVPN2_def register_defs)
  have [trace_elim]: "(set_XContextReg_XR TLBXContext_ref v, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t" for s t v and m' :: "unit M"
    by (auto elim!: trace_elim read_reg_trace_enabled write_reg_trace_enabled simp: set_XContextReg_XR_def register_defs)
  have [trace_elim]: "(set_TLBEntryHiReg_R TLBEntryHi_ref v, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t" for s t v and m' :: "unit M"
    by (auto elim!: trace_elim read_reg_trace_enabled write_reg_trace_enabled simp: set_TLBEntryHiReg_R_def register_defs)
  have [trace_elim]: "(set_TLBEntryHiReg_VPN2 TLBEntryHi_ref v, t, m') \<in> Traces \<Longrightarrow> trace_enabled s t" for s t v and m' :: "unit M"
    by (auto elim!: trace_elim read_reg_trace_enabled write_reg_trace_enabled simp: set_TLBEntryHiReg_VPN2_def register_defs)
  note [derivable_capsI] = ex
  show ?thesis
  using assms(1-3)
  unfolding SignalExceptionTLB_def bind_assoc
  by (elim trace_elim SignalException_trace_enabled)
     (derivable_capsI simp: regstate_simp)+
qed

lemma traces_enabled_SignalExceptionTLB[traces_enabledI]:
  assumes "PCC_accessible s regs"
  shows "traces_enabled (SignalExceptionTLB arg0 arg1) s regs"
proof cases
  assume ex: "ex_traces"
  show ?thesis
    unfolding traces_enabled_def
    using assms
    by (auto elim!: SignalExceptionTLB_trace_enabled intro: ex)
next
  assume "\<not>ex_traces"
  then show ?thesis
    unfolding traces_enabled_def finished_def isException_def
    by auto
qed

lemma traces_enabled_incrementCP0Count[traces_enabledI]:
  assumes "PCC_accessible s regs"
  shows "traces_enabled (incrementCP0Count u) s regs"
  unfolding incrementCP0Count_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_raise_c2_exception8[traces_enabledI]:
  assumes "PCC_accessible s regs"
  shows "traces_enabled (raise_c2_exception8 arg0 arg1) s regs"
proof cases
  assume ex: "ex_traces"
  have 1: "traces_enabled (set_CapCauseReg_ExcCode CapCause_ref x) s regs" for x s regs
    unfolding set_CapCauseReg_ExcCode_def
    by (traces_enabledI assms: ex)
  have 2: "traces_enabled (set_CapCauseReg_RegNum CapCause_ref x) s regs" for x s regs
    unfolding set_CapCauseReg_RegNum_def
    by (traces_enabledI assms: ex)
  show ?thesis
    unfolding raise_c2_exception8_def bind_assoc
    by (traces_enabledI assms: assms intro: 1 2)
next
  assume "\<not> ex_traces"
  then show ?thesis
    unfolding traces_enabled_def finished_def isException_def
    by auto
qed

lemma traces_enabled_raise_c2_exception_noreg[traces_enabledI]:
  assumes "PCC_accessible s regs"
  shows "traces_enabled (raise_c2_exception_noreg arg0) s regs"
  unfolding raise_c2_exception_noreg_def
  by (traces_enabledI assms: assms)

lemma traces_enabled_TLBTranslate2[traces_enabledI]:
  assumes "PCC_accessible s regs"
  shows "traces_enabled (TLBTranslate2 arg0 arg1) s regs"
  unfolding TLBTranslate2_def
  by (traces_enabledI assms: assms)

lemma traces_enabled_TLBTranslateC[traces_enabledI]:
  assumes "PCC_accessible s regs"
  shows "traces_enabled (TLBTranslateC arg0 arg1) s regs"
  unfolding TLBTranslateC_def
  by (traces_enabledI assms: assms)

lemma traces_enabled_TLBTranslate[traces_enabledI]:
  assumes "PCC_accessible s regs"
  shows "traces_enabled (TLBTranslate arg0 arg1) s regs"
  unfolding TLBTranslate_def
  by (traces_enabledI assms: assms)

lemma traces_enabled_TranslatePC[traces_enabledI]:
  assumes "PCC_accessible s regs"
  shows "traces_enabled (TranslatePC vaddr) s regs"
  unfolding TranslatePC_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr[traces_enabledI]:
  shows "traces_enabled (MEMr arg0 arg1) s regs"
  unfolding MEMr_def read_mem_def read_mem_bytes_def maybe_fail_def bind_assoc
  by (auto simp: traces_enabled_def elim!: bind_Traces_cases split: option.splits elim: Traces_cases)

lemma traces_enabled_MEMr_wrapper[traces_enabledI]:
  shows "traces_enabled (MEMr_wrapper arg0 arg1) s regs"
  unfolding MEMr_wrapper_def bind_assoc
  by (traces_enabledI_with \<open>-\<close>)

lemma traces_enabled_fetch[traces_enabledI]:
  assumes "{''DelayedPCC'', ''NextPCC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (fetch u) s regs"
  unfolding fetch_def bind_assoc
  by (traces_enabledI elim: Run_inv_cp2_next_pc_PCC_accessible assms: assms simp: register_defs)

lemma traces_enabled_instr_fetch[traces_enabledI]:
  assumes "{''DelayedPCC'', ''NextPCC'', ''PCC''} \<subseteq> accessible_regs s"
  shows "traces_enabled (instr_fetch ISA) s regs"
  unfolding ISA_simps
  by (traces_enabledI assms: assms)

lemma hasTrace_fetch_reg_axioms:
  assumes "hasTrace t (instr_fetch ISA)"
    and "reads_regs_from trans_regs t regs" and "trans_inv regs"
    and "fetch_raises_ex ISA t \<longrightarrow> ex_traces"
  shows "store_cap_reg_axiom CC ISA ex_traces False t"
    and "store_cap_mem_axiom CC ISA t"
    and "read_reg_axiom CC ISA ex_traces t"
  using assms
  by (intro traces_enabled_reg_axioms[where m = "instr_fetch ISA" and regs = regs] traces_enabled_instr_fetch; auto)+

end

end
