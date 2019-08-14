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
  "\<And>v. traces_preserve_invariant (write_reg PCC_ref v)"
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
  unfolding BranchPending_ref_def C26_ref_def CID_ref_def CP0BadInstr_ref_def CP0BadInstrP_ref_def
     CP0BadVAddr_ref_def CP0Cause_ref_def CP0Compare_ref_def CP0ConfigK0_ref_def CP0Count_ref_def
     CP0HWREna_ref_def CP0LLAddr_ref_def CP0LLBit_ref_def CP0UserLocal_ref_def CPLR_ref_def
     CULR_ref_def CapCause_ref_def CurrentInstrBits_ref_def DDC_ref_def DelayedPC_ref_def
     DelayedPCC_ref_def EPCC_ref_def ErrorEPCC_ref_def GPR_ref_def HI_ref_def
     InBranchDelay_ref_def KCC_ref_def KDC_ref_def KR1C_ref_def KR2C_ref_def
     LO_ref_def LastInstrBits_ref_def NextInBranchDelay_ref_def NextPC_ref_def NextPCC_ref_def
     PC_ref_def PCC_ref_def TLBEntryLo0_ref_def TLBEntryLo1_ref_def TLBIndex_ref_def
     TLBPageMask_ref_def TLBProbe_ref_def TLBRandom_ref_def TLBWired_ref_def UART_RDATA_ref_def
     UART_RVALID_ref_def UART_WDATA_ref_def UART_WRITTEN_ref_def
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg; simp add: inv_regs_def)+

lemma preserves_invariant_no_writes_to_inv_regs[preserves_invariantI]:
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MIPS_write arg0 arg1 arg2)"
  "\<And>arg0 arg1. traces_preserve_invariant (MIPS_read arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_BD arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_CE arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CauseReg_ExcCode arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryHiReg_R arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_TLBEntryHiReg_VPN2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_ContextReg_BadVPN2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_XContextReg_XR arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_XContextReg_XBadVPN2 arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_StatusReg_EXL arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (rGPR arg0)"
  "\<And>arg0 arg1. traces_preserve_invariant (wGPR arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr_reserve arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMea arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMea_conditional arg0 arg1)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMval arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMval_conditional arg0 arg1 arg2)"
  "\<And>arg0. traces_preserve_invariant (exceptionVectorOffset arg0)"
  "\<And>arg0. traces_preserve_invariant (exceptionVectorBase arg0)"
  "\<And>arg0. traces_preserve_invariant (updateBadInstr arg0)"
  "\<And>arg0. traces_preserve_invariant (set_next_pcc arg0)"
  "\<And>arg0. traces_preserve_invariant (getAccessLevel arg0)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CapCauseReg_ExcCode arg0 arg1)"
  "\<And>arg0 arg1. name arg0 \<notin> inv_regs \<Longrightarrow> traces_preserve_invariant (set_CapCauseReg_RegNum arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr_wrapper arg0 arg1)"
  "\<And>arg0 arg1. traces_preserve_invariant (MEMr_reserve_wrapper arg0 arg1)"
  "\<And>arg0. traces_preserve_invariant (tlbSearch arg0)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMr_tagged arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMr_tagged_reserve arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2 arg3. traces_preserve_invariant (MEMw_tagged arg0 arg1 arg2 arg3)"
  "\<And>arg0 arg1 arg2 arg3. traces_preserve_invariant (MEMw_tagged_conditional arg0 arg1 arg2 arg3)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMw_wrapper arg0 arg1 arg2)"
  "\<And>arg0 arg1 arg2. traces_preserve_invariant (MEMw_conditional_wrapper arg0 arg1 arg2)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_toI; simp add: inv_regs_def)+

lemma preserves_invariant_SignalException[preserves_invariantI]:
  shows "runs_preserve_invariant (SignalException arg0)"
  by (auto simp: runs_preserve_invariant_def)

lemma preserves_invariant_SignalExceptionBadAddr[preserves_invariantI]:
  shows "runs_preserve_invariant (SignalExceptionBadAddr arg0 arg1)"
  unfolding SignalExceptionBadAddr_def bind_assoc
  by (preserves_invariantI)

lemma preserves_invariant_SignalExceptionTLB[preserves_invariantI]:
  shows "runs_preserve_invariant (SignalExceptionTLB arg0 arg1)"
  unfolding SignalExceptionTLB_def bind_assoc
  by (auto simp: runs_preserve_invariant_def elim!: Run_bindE)

lemma preserves_invariant_raise_c2_exception8[preserves_invariantI]:
  shows "runs_preserve_invariant (raise_c2_exception8 arg0 arg1)"
  unfolding raise_c2_exception8_def bind_assoc
  by (auto simp: runs_preserve_invariant_def elim!: Run_bindE)

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

lemma preserves_invariant_raise_c2_exception[preserves_invariantI]:
  shows "runs_preserve_invariant (raise_c2_exception arg0 arg1)"
  unfolding raise_c2_exception_def bind_assoc
  by (preserves_invariantI)

declare MemAccessType.split[where P = "\<lambda>m. runs_preserve_invariant m", THEN iffD2, preserves_invariantI]

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

(* *)
lemma [simp]: "name CP0Cause_ref \<notin> inv_regs"
  by (auto simp: register_defs inv_regs_def)
(* *)

lemma preserves_invariant_checkCP2usable[preserves_invariantI]:
  shows "runs_preserve_invariant (checkCP2usable arg0)"
  unfolding checkCP2usable_def bind_assoc
  by (preserves_invariantI)

lemmas non_cap_exp_traces_enabled[traces_enabledI] = non_cap_expI[THEN non_cap_exp_traces_enabledI]

lemmas non_mem_exp_traces_enabled[traces_enabledI] = non_mem_expI[THEN non_mem_exp_traces_enabledI]

(* *)
lemma notnotE[derivable_capsE]:
  assumes "\<not>\<not>P"
  obtains "P"
  using assms
  by blast

lemma pow2_simp[simp]: "pow2 n = 2 ^ nat n"
  by (auto simp: pow2_def pow_def)

lemma getCapCursor_mod_pow2_64[simp]:
  "getCapCursor c mod 18446744073709551616 = getCapCursor c"
  using uint_idem[of "Capability_address c"]
  by (auto simp: getCapCursor_def)

lemma mem_val_is_local_cap_Capability_global[simp]:
  "mem_val_is_local_cap CC ISA (mem_bytes_of_word (capToMemBits c)) tag \<longleftrightarrow> \<not>Capability_global c \<and> tag \<noteq> BU"
  by (cases tag) (auto simp: mem_val_is_local_cap_def bind_eq_Some_conv)

declare cap_size_def[simp]
lemma [simp]: "tag_granule ISA = 32" by (auto simp: ISA_def)

lemma to_bits_mult[simp]:
  "n = int (LENGTH('a)) \<Longrightarrow> to_bits n (a * b) = (to_bits n a * to_bits n b :: 'a::len word)"
  by (auto simp: to_bits_def of_bl_bin_word_of_int wi_hom_syms)

lemma to_bits_64_32[simp]: "to_bits 64 32 = (32 :: 64 word)"
  by eval

lemma mult_32_shiftl_5[simp]: "32 * (w :: 'a::len word) = w << 5"
  by (auto simp: shiftl_t2n)

lemma shiftl_AND_mask_0[simp]: "(w << n) AND mask n = 0"
  by (intro word_eqI) (auto simp: word_ao_nth nth_shiftl)

lemma unat_to_bits[simp]:
  "len = int (LENGTH('a)) \<Longrightarrow> unat (to_bits len i :: 'a::len word) = nat (i mod 2 ^ LENGTH('a))"
  by (auto simp: to_bits_def of_bl_bin_word_of_int unat_def uint_word_of_int)

lemma uint_to_bits[simp]:
  "len = int (LENGTH('a)) \<Longrightarrow> uint (to_bits len i :: 'a::len word) = i mod 2 ^ LENGTH('a)"
  by (auto simp: to_bits_def of_bl_bin_word_of_int uint_word_of_int)

lemma length_take_chunks[simp]:
  "n dvd length xs \<Longrightarrow> length (take_chunks n xs) = length xs div n"
  by (induction n xs rule: take_chunks.induct) (auto simp: le_div_geq[symmetric] dvd_imp_le)

lemma length_mem_bytes_of_word[simp]:
  fixes w :: "'a::len word"
  assumes "8 dvd LENGTH('a)"
  shows "length (mem_bytes_of_word w) = LENGTH('a) div 8"
  using assms
  by (auto simp add: mem_bytes_of_word_def simp del: take_chunks.simps)

lemma access_enabled_Store[derivable_capsE]:
  assumes "Capability_permit_store c"
    and "tag \<noteq> B0 \<longrightarrow> Capability_permit_store_cap c"
    and "mem_val_is_local_cap CC ISA v tag \<and> tag = B1 \<longrightarrow> Capability_permit_store_local_cap c"
    and "Capability_tag c" and "\<not>Capability_sealed c"
    and "paddr_in_mem_region c False paddr sz"
    and "c \<in> derivable_caps s"
    and "tag = B0 \<or> tag = B1" and "length v = sz"
    and "tag \<noteq> B0 \<longrightarrow> address_tag_aligned ISA paddr \<and> sz = tag_granule ISA"
  shows "access_enabled s False paddr sz v tag"
  using assms
  unfolding access_enabled_def authorises_access_def has_access_permission_def
  by (auto simp: get_cap_perms_def derivable_caps_def)

lemma access_enabled_Load[derivable_capsE]:
  assumes "Capability_permit_load c"
    and "tag \<noteq> B0 \<longrightarrow> Capability_permit_load_cap c"
    and "Capability_tag c" and "\<not>Capability_sealed c"
    and "paddr_in_mem_region c True paddr sz"
    and "c \<in> derivable_caps s"
    and "tag \<noteq> B0 \<longrightarrow> address_tag_aligned ISA paddr \<and> sz = tag_granule ISA"
  shows "access_enabled s True paddr sz v tag"
  using assms
  unfolding access_enabled_def authorises_access_def has_access_permission_def
  by (auto simp: get_cap_perms_def derivable_caps_def)

thm addrWrapper_def checkDDCPerms_def

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

lemma Run_inv_addrWrapper_access_enabled[derivable_capsE]:
  assumes "Run_inv (addrWrapper addr acctype width) t vaddr regs"
    and "translate_address (unat vaddr) is_load [] = Some paddr"
    and "{''DDC''} \<subseteq> accessible_regs s"
    and "acctype = acctype_of_bool is_load"
    and "is_load \<or> length v = nat sz"
    and "sz = wordWidthBytes width"
  shows "access_enabled (run s t) is_load paddr (nat sz) v B0"
  using assms
  unfolding Run_inv_def addrWrapper_def checkDDCPerms_def Let_def
  unfolding access_enabled_def authorises_access_def has_access_permission_def paddr_in_mem_region_def
  apply (cases is_load)
   apply (auto elim!: Run_bindE simp: get_cap_perms_def getCapBounds_def)
  subgoal for c
    apply (rule bexI[where x = c])
     apply (clarify)
     apply (rule exI[where x = "unat vaddr"])
     apply (auto simp: address_range_def derivable_caps_def dest!: Run_read_reg_DDC_derivable_caps)
    done
  subgoal for c
    apply (rule bexI[where x = c])
     apply (clarify)
     apply (rule exI[where x = "unat vaddr"])
     apply (auto simp: address_range_def derivable_caps_def dest!: Run_read_reg_DDC_derivable_caps)
    done
  done

lemma Run_read_reg_DDC_access_enabled:
  assumes "Run (read_reg DDC_ref) t c"
    and "{''DDC''} \<subseteq> accessible_regs s"
    and "Capability_tag c" and "\<not>Capability_sealed c"
    and "paddr_in_mem_region c is_load paddr sz"
    and "is_load \<or> length v = nat sz"
    and "if is_load then Capability_permit_load c else Capability_permit_store c"
  shows "access_enabled (run s t) is_load paddr sz v B0"
  using assms
  unfolding access_enabled_def authorises_access_def has_access_permission_def
  by (auto simp: get_cap_perms_def derivable_caps_def dest!: Run_read_reg_DDC_derivable_caps)

lemma translate_address_paddr_in_mem_region:
  assumes "translate_address (nat vaddr) is_load [] = Some paddr"
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
    and "translate_address (unat vaddr) is_load [] = Some paddr"
    and "{''DDC''} \<subseteq> accessible_regs s"
    and "acctype = acctype_of_bool is_load"
    and "is_load \<or> length v = nat sz"
  shows "access_enabled (run s t) is_load paddr (nat sz) v B0"
  using assms
  unfolding Run_inv_def addrWrapperUnaligned_def unalignedBytesTouched_def checkDDCPerms_def Let_def
  by (cases width; cases is_load;
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
    and "acctype = acctype_of_bool is_load"
  shows "translate_address (unat vaddr) is_load t' = Some (unat paddr)"
proof -
  from assms have "Run_inv (translate_addressM (unat vaddr) is_load) t (unat paddr) regs"
    unfolding translate_addressM_def TLBTranslate_def bind_assoc Run_inv_def
    by (auto simp flip: uint_nat intro: Traces_bindI[of _ t _ _ "[]", simplified])
  then show ?thesis
    using determ_runs_translate_addressM
    by (auto simp: translate_address_def determ_the_result_eq)
qed

lemma TLBTranslate_translate_address_eq[simp]:
  assumes "Run_inv (TLBTranslate vaddr acctype) t paddr regs" (*and "\<not>is_fetch"*)
    and "acctype = acctype_of_bool is_load"
  shows "translate_address (unat vaddr) is_load t' = Some (unat paddr)"
proof -
  from assms have "Run_inv (translate_addressM (unat vaddr) is_load) t (unat paddr) regs"
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
  assumes "\<And>t a b. Run_inv m t (a, b) regs \<Longrightarrow> traces_enabled (f a b) (run s t) (the (updates_regs inv_regs t regs))"
    and "runs_preserve_invariant m" and "traces_enabled m s regs"
  shows "traces_enabled (m \<bind> (\<lambda>vars. let (a, b) = vars in f a b)) s regs"
  using assms
  by (auto intro: traces_enabled_bind)

lemma TLBTranslate_paddr_in_mem_region[derivable_capsE]:
  assumes "Run_inv (TLBTranslate vaddr acctype) t paddr regs"
    and "getCapBase c \<le> uint vaddr" and "uint vaddr + sz \<le> getCapTop c" and "0 \<le> sz"
    and "acctype = acctype_of_bool is_load"
  shows "paddr_in_mem_region c is_load (unat paddr) (nat sz)"
  using assms TLBTranslate_translate_address_eq[OF assms(1), where t' = "[]"]
  unfolding paddr_in_mem_region_def
  by (intro exI[where x = "unat vaddr"])
     (auto simp add: address_range_def unat_def simp flip: nat_add_distrib)

lemma TLBTranslateC_paddr_in_mem_region[derivable_capsE]:
  assumes "Run_inv (TLBTranslateC vaddr acctype) t (paddr, noStoreCap) regs"
    and "getCapBase c \<le> uint vaddr" and "uint vaddr + sz \<le> getCapTop c" and "0 \<le> sz"
    and "acctype = acctype_of_bool is_load"
  shows "paddr_in_mem_region c is_load (unat paddr) (nat sz)"
  using assms TLBTranslateC_translate_address_eq[OF assms(1), where t' = "[]"]
  unfolding paddr_in_mem_region_def
  by (intro exI[where x = "unat vaddr"])
     (auto simp add: address_range_def unat_def simp flip: nat_add_distrib)

lemma mult_mod_plus_less:
  assumes "n dvd m" and "n > 0" and "m > 0" and "0 \<le> i" and "i < n"
  shows "n * q mod m + i < (m :: int)"
  using assms
  by (auto simp: dvd_def)
     (metis assms(2-5) mult.commute zero_less_mult_pos2 zmult2_lemma_aux4)

lemma dvd_nat_iff_int_dvd:
  assumes "0 \<le> i"
  shows "n dvd nat i \<longleftrightarrow> int n dvd i"
  using assms
  by (auto simp: dvd_def nat_mult_distrib) (use nat_0_le in \<open>fastforce\<close>)

lemma address_tag_aligned_plus_iff[simp]:
  fixes addr :: "64 word"
  assumes "int (tag_granule ISA) dvd i" and "0 \<le> i"
  shows "address_tag_aligned ISA (unat (addr + word_of_int i)) \<longleftrightarrow> address_tag_aligned ISA (unat addr)"
  using assms
  unfolding address_tag_aligned_def unat_def mod_eq_0_iff_dvd uint_ge_0[THEN dvd_nat_iff_int_dvd]
  by (auto simp: uint_word_ariths uint_word_of_int mod_add_right_eq dvd_mod_iff dvd_add_left_iff)

lemma sail_ones_max_word[simp]: "sail_ones n = max_word"
  by (intro word_eqI) (auto simp: sail_ones_def zeros_def)

lemma sail_mask_ucast[simp]: "sail_mask n w = ucast w"
  by (auto simp: sail_mask_def vector_truncate_def zero_extend_def)

lemma mod2_minus_one_mask:
  "(2 ^ n - 1) = (mask n :: 'a::len word)"
  by (auto simp: mask_def)

lemma slice_mask_nth:
  fixes n i l :: int and j :: nat
  defines "w \<equiv> slice_mask n i l :: 'n::len word"
  assumes "n = LENGTH('n)"
  shows "w !! j \<longleftrightarrow> j < nat n \<and> nat i \<le> j \<and> j < nat i + nat l"
  using assms
  by (auto simp: slice_mask_def nth_shiftl Let_def mod2_minus_one_mask)

lemma subrange_subrange_concat_ucast_right:
  fixes w1 :: "'a::len word" and w2 :: "'b::len word"
  fixes c i1 j1 i2 :: int
  defines "w \<equiv> subrange_subrange_concat c w1 i1 j1 w2 i2 0 :: 'c::len word"
  defines "d \<equiv> ucast w2 :: 'd::len word"
  assumes "int LENGTH('d) \<le> i2 + 1" and "0 \<le> i2" "LENGTH('b) \<ge> LENGTH('d)" "LENGTH('c) \<ge> LENGTH('d)"
  shows "ucast w = d"
  using assms
  by (intro word_eqI)
     (auto simp: subrange_subrange_concat_def nth_ucast word_ao_nth nth_shiftl nth_shiftr nat_add_distrib slice_mask_nth)

lemma TLBTranslate2_ucast_paddr_eq:
  assumes "Run (TLBTranslate2 vaddr acctype) t (paddr, flag)"
  shows "(ucast paddr :: 12 word) = (ucast vaddr :: 12 word)"
  using assms
  unfolding TLBTranslate2_def Let_def undefined_range_def
  by (auto elim!: Run_bindE Run_ifE split: option.splits
           simp: subrange_subrange_concat_ucast_right)

lemma TLBTranslateC_ucast_paddr_eq:
  assumes "Run (TLBTranslateC vaddr acctype) t (paddr, flag)"
  shows "(ucast paddr :: 12 word) = (ucast vaddr :: 12 word)"
  using assms
  unfolding TLBTranslateC_def Let_def
  by (fastforce elim!: Run_bindE Run_ifE simp: TLBTranslate2_ucast_paddr_eq split: option.splits bool.splits prod.splits if_splits)

lemma TLBTranslate_ucast_paddr_eq:
  assumes "Run (TLBTranslate vaddr acctype) t paddr"
  shows "(ucast paddr :: 12 word) = (ucast vaddr :: 12 word)"
  using assms
  unfolding TLBTranslate_def
  by (auto elim!: Run_bindE simp: TLBTranslateC_ucast_paddr_eq)

lemma address_tag_aligned_ucast5:
  fixes addr :: "'a::len word"
  assumes "LENGTH('a) \<ge> 5"
  shows "address_tag_aligned ISA (unat addr) \<longleftrightarrow> (ucast addr :: 5 word) = 0"
  using assms
  unfolding unat_arith_simps(3)
  by (auto simp: address_tag_aligned_def unat_and_mask min_def)

lemma address_tag_aligned_paddr_iff_vaddr[simp]:
  assumes "Run_inv (TLBTranslate vaddr acctype) t paddr regs"
  shows "address_tag_aligned ISA (unat paddr) \<longleftrightarrow> address_tag_aligned ISA (unat vaddr)"
proof -
  have paddr_vaddr: "ucast paddr = (ucast vaddr :: 12 word)"
    using assms
    by (auto simp: Run_inv_def TLBTranslate_ucast_paddr_eq)
  have "address_tag_aligned ISA (unat paddr) \<longleftrightarrow> (ucast (ucast paddr :: 12 word) :: 5 word) = 0"
    by (auto simp: address_tag_aligned_ucast5)
  also have "\<dots> \<longleftrightarrow> address_tag_aligned ISA (unat vaddr)"
    unfolding paddr_vaddr
    by (auto simp: address_tag_aligned_ucast5)
  finally show ?thesis .
qed

lemma TLBTranslateC_address_tag_aligned[simp]:
  assumes "Run_inv (TLBTranslateC vaddr acctype) t (paddr, noStoreCap) regs"
  shows "address_tag_aligned ISA (unat paddr) \<longleftrightarrow> address_tag_aligned ISA (unat vaddr)"
proof -
  have paddr_vaddr: "ucast paddr = (ucast vaddr :: 12 word)"
    using assms
    by (auto simp: Run_inv_def TLBTranslateC_ucast_paddr_eq)
  have "address_tag_aligned ISA (unat paddr) \<longleftrightarrow> (ucast (ucast paddr :: 12 word) :: 5 word) = 0"
    by (auto simp: address_tag_aligned_ucast5)
  also have "\<dots> \<longleftrightarrow> address_tag_aligned ISA (unat vaddr)"
    unfolding paddr_vaddr
    by (auto simp: address_tag_aligned_ucast5)
  finally show ?thesis .
qed

lemma address_tag_aligned_mult_dvd[intro, simp]:
  assumes "int (tag_granule ISA) dvd k" and "0 \<le> k"
  shows "address_tag_aligned ISA (nat (k * n))"
  using assms
  by (auto simp: address_tag_aligned_def nat_mult_distrib)

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

lemma bitU_of_bool_simps[simp]: "bitU_of_bool True = B1" "bitU_of_bool False = B0"
  by (auto simp: bitU_of_bool_def)

lemma nat_of_mword_unat[simp]: "nat_of_bv BC_mword w = Some (unat w)"
  by (auto simp: nat_of_bv_def unat_def)

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
  assumes "access_enabled s False (unat addr) (nat sz) (mem_bytes_of_word v) B0"
  shows "traces_enabled (write_mem BC_mword BC_mword wk addr_sz addr sz v) s regs"
  using assms
  by (auto simp: write_mem_def traces_enabled_def split: option.splits elim: Traces_cases)

lemma traces_enabled_write_memt[traces_enabledI]:
  assumes "access_enabled s False (unat addr) (nat sz) (mem_bytes_of_word v) tag"
  shows "traces_enabled (write_memt BC_mword BC_mword wk addr sz v tag) s regs"
  using assms
  by (auto simp: write_memt_def traces_enabled_def split: option.splits elim: Traces_cases)

lemma traces_enabled_read_mem_bytes[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s True (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (read_mem_bytes BC_mword BC_mword rk addr sz) s regs"
  using assms
  by (auto simp: read_mem_bytes_def maybe_fail_def traces_enabled_def split: option.splits elim: Traces_cases)

lemma traces_enabled_read_mem[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s True (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (read_mem BC_mword BC_mword rk addr_sz addr sz) s regs"
  unfolding read_mem_def
  by (traces_enabledI assms: assms)

lemma traces_enabled_read_memt_bytes[traces_enabledI]:
  assumes "\<And>bytes tag. access_enabled s True (unat addr) (nat sz) bytes tag"
  shows "traces_enabled (read_memt_bytes BC_mword BC_mword rk addr sz) s regs"
  using assms
  by (auto simp: read_memt_bytes_def maybe_fail_def traces_enabled_def split: option.splits elim: Traces_cases)

lemma traces_enabled_read_memt[traces_enabledI]:
  assumes "\<And>bytes tag. access_enabled s True (unat addr) (nat sz) bytes tag"
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
  assumes "access_enabled s False (unat addr) (nat sz) (mem_bytes_of_word v) B0"
  shows "traces_enabled (MEMval addr sz v) s regs"
  unfolding MEMval_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s True (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (MEMr addr sz) s regs"
  unfolding MEMr_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MIPS_write[traces_enabledI]:
  assumes "access_enabled s False (unat addr) (nat sz) (mem_bytes_of_word v) B0"
  shows "traces_enabled (MIPS_write addr sz v) s regs"
  unfolding MIPS_write_def write_ram_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MIPS_read[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s True (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (MIPS_read addr sz) s regs"
  unfolding MIPS_read_def read_ram_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr_reserve[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s True (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (MEMr_reserve addr sz) s regs"
  unfolding MEMr_reserve_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMval_conditional[traces_enabledI]:
  assumes "access_enabled s False (unat addr) (nat sz) (mem_bytes_of_word v) B0"
  shows "traces_enabled (MEMval_conditional addr sz v) s regs"
  unfolding MEMval_conditional_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr_wrapper[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s True (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (MEMr_wrapper addr sz) s regs"
  unfolding MEMr_wrapper_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr_reserve_wrapper[traces_enabledI]:
  assumes "\<And>bytes. access_enabled s True (unat addr) (nat sz) bytes B0"
  shows "traces_enabled (MEMr_reserve_wrapper addr sz) s regs"
  unfolding MEMr_reserve_wrapper_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr_tagged[traces_enabledI]:
  assumes "\<And>bytes tag. tag \<noteq> B0 \<longrightarrow> allow_tag \<Longrightarrow> access_enabled s True (unat addr) (nat sz) bytes tag"
  shows "traces_enabled (MEMr_tagged addr sz allow_tag) s regs"
  unfolding MEMr_tagged_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMr_tagged_reserve[traces_enabledI]:
  assumes "\<And>bytes tag. tag \<noteq> B0 \<longrightarrow> allow_tag \<Longrightarrow> access_enabled s True (unat addr) (nat sz) bytes tag"
  shows "traces_enabled (MEMr_tagged_reserve addr sz allow_tag) s regs"
  unfolding MEMr_tagged_reserve_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMw_tagged[traces_enabledI]:
  assumes "access_enabled s False (unat addr) (nat sz) (mem_bytes_of_word v) (bitU_of_bool tag)"
  shows "traces_enabled (MEMw_tagged addr sz tag v) s regs"
  unfolding MEMw_tagged_def MEMval_tagged_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMw_tagged_conditional[traces_enabledI]:
  assumes "access_enabled s False (unat addr) (nat sz) (mem_bytes_of_word v) (bitU_of_bool tag)"
  shows "traces_enabled (MEMw_tagged_conditional addr sz tag v) s regs"
  unfolding MEMw_tagged_conditional_def MEMval_tagged_conditional_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMw_wrapper[traces_enabledI]:
  assumes "access_enabled s False (unat addr) (nat sz) (mem_bytes_of_word v) B0"
  shows "traces_enabled (MEMw_wrapper addr sz v) s regs"
  unfolding MEMw_wrapper_def bind_assoc
  by (traces_enabledI assms: assms)

lemma traces_enabled_MEMw_conditional_wrapper[traces_enabledI]:
  assumes "access_enabled s False (unat addr) (nat sz) (mem_bytes_of_word v) B0"
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

lemma preserves_invariant_write_reg_CapRegs[preserves_invariantI]:
  assumes "i \<in> {0..31}"
  shows "traces_preserve_invariant (write_reg (access_list_dec CapRegs i) c)"
  using assms
  unfolding upto_31_unfold
  by (elim insertE; intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg)
     (auto simp: CapRegs_def register_defs inv_regs_def)

lemma preserves_invariant_writeCapReg[preserves_invariantI]:
  "traces_preserve_invariant (writeCapReg n c)"
  unfolding writeCapReg_def capToString_def
  by (preserves_invariantI)

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

lemma traces_enabled_instr_sem[traces_enabledI]:
  assumes "{''DDC'', ''PCC''} \<subseteq> accessible_regs s"
    and "CapRegs_names \<subseteq> accessible_regs s"
  shows "traces_enabled (instr_sem ISA instr) s regs"
  by (cases instr rule: execute.cases; simp; use nothing in \<open>traces_enabledI assms: assms\<close>)

lemma hasTrace_mem_axioms:
  assumes "hasTrace t (instr_sem ISA instr)"
    and "reads_regs_from inv_regs t trans_regstate"
  shows "store_mem_axiom CC ISA t"
    and "store_tag_axiom CC ISA t"
    and "load_mem_axiom CC ISA False t"
  using assms
  by (intro traces_enabled_mem_axioms[where instr = instr and regs = trans_regstate] traces_enabled_instr_sem;
      auto simp: invariant_def)+

end

end
