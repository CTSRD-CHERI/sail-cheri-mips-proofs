theory CHERI_MIPS_Instantiation
imports "Sail-CHERI-MIPS.Cheri_lemmas" Cheri_reg_lemmas Recognising_Automata Sail.Sail2_operators_mwords_lemmas Word_Extra
begin

section \<open>General lemmas (TODO: Add to Sail library)\<close>

lemma more_and_or_boolM_simps[simp]:
  "and_boolM (return True) m = m"
  "and_boolM (return False) m = return False"
  "or_boolM (return True) m = return True"
  "or_boolM (return False) m = m"
  by (auto simp: and_boolM_def or_boolM_def)

lemma final_Done[intro, simp]: "final (Done a)"
  by (auto simp: final_def)

lemma bitU_of_bool_simps[simp]: "bitU_of_bool True = B1" "bitU_of_bool False = B0"
  by (auto simp: bitU_of_bool_def)

lemma nat_of_mword_unat[simp]: "nat_of_bv BC_mword w = Some (unat w)"
  by (auto simp: nat_of_bv_def unat_def)

lemma pow2_simp[simp]: "pow2 n = 2 ^ nat n"
  by (auto simp: pow2_def pow_def)

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

lemma (in State_Invariant) Run_inv_assert_exp_iff[iff]:
  "Run_inv (assert_exp c msg) t a regs \<longleftrightarrow> c \<and> t = [] \<and> invariant regs"
  unfolding Run_inv_def
  by auto

lemma (in Cap_Axiom_Automaton) Run_runs_no_reg_writes_written_regs_eq:
  assumes "Run m t a" and "runs_no_reg_writes_to {r} m"
  shows "r \<in> written_regs (run s t) \<longleftrightarrow> r \<in> written_regs s"
proof -
  from assms have "E_write_reg r v \<notin> set t" for v
    unfolding runs_no_reg_writes_to_def
    by auto
  then show ?thesis
    by (induction t arbitrary: s) auto
qed

section \<open>Instantiation of the abstract model for CHERI-MIPS\<close>

definition get_cap_perms :: "Capability \<Rightarrow> perms" where
  "get_cap_perms c =
     \<lparr>permit_ccall                  = Capability_permit_ccall c,
      permit_execute                = Capability_permit_execute c,
      permit_load                   = Capability_permit_load c,
      permit_load_capability        = Capability_permit_load_cap c,
      permit_seal                   = Capability_permit_seal c,
      permit_store                  = Capability_permit_store c,
      permit_store_capability       = Capability_permit_store_cap c,
      permit_store_local_capability = Capability_permit_store_local_cap c,
      permit_system_access          = Capability_access_system_regs c,
      permit_unseal                 = Capability_permit_unseal c\<rparr>"

definition set_cap_perms :: "Capability \<Rightarrow> perms \<Rightarrow> Capability" where
  "set_cap_perms c p =
     c\<lparr>Capability_permit_ccall           := permit_ccall p,
       Capability_permit_execute         := permit_execute p,
       Capability_permit_load            := permit_load p,
       Capability_permit_load_cap        := permit_load_capability p,
       Capability_permit_seal            := permit_seal p,
       Capability_permit_store           := permit_store p,
       Capability_permit_store_cap       := permit_store_capability p,
       Capability_permit_store_local_cap := permit_store_local_capability p,
       Capability_access_system_regs     := permit_system_access p,
       Capability_permit_unseal          := permit_unseal p\<rparr>"

fun cap_of_mem_bytes :: "memory_byte list \<Rightarrow> bitU \<Rightarrow> Capability option" where
  "cap_of_mem_bytes bs t =
     Option.bind (bool_of_bitU t) (\<lambda>t.
     map_option (\<lambda>bs. memBitsToCapability t bs) (of_bits_method BC_mword (bits_of_mem_bytes bs)))"

abbreviation
  "CC \<equiv>
     \<lparr>is_tagged_method = (\<lambda>c. Capability_tag c),
      is_sealed_method = (\<lambda>c. Capability_sealed c),
      get_mem_region_method = (\<lambda>c. {nat (getCapBase c) ..< nat (getCapTop c)}),
      get_obj_type_method = (\<lambda>c. unat (Capability_otype c)),
      get_perms_method = get_cap_perms,
      get_cursor_method = (\<lambda>c. nat (getCapCursor c)),
      get_global_method = (\<lambda>c. Capability_global c),
      set_tag_method = (\<lambda>c t. c\<lparr>Capability_tag := t\<rparr>),
      set_seal_method = (\<lambda>c s. c\<lparr>Capability_sealed := s\<rparr>),
      set_obj_type_method = (\<lambda>c t. c\<lparr>Capability_otype := of_nat t\<rparr>),
      set_perms_method = set_cap_perms,
      set_global_method = (\<lambda>c g. c\<lparr>Capability_global := g\<rparr>),
      cap_of_mem_bytes_method = cap_of_mem_bytes\<rparr>"

interpretation Capabilities CC
  by unfold_locales
     (auto simp: bool_of_bitU_def memBitsToCapability_def capBitsToCapability_def get_cap_perms_def set_cap_perms_def split: bitU.splits)

abbreviation "privileged_CHERI_regs \<equiv> {''EPCC'', ''ErrorEPCC'', ''KDC'', ''KCC'', ''KR1C'', ''KR2C'', ''CapCause'', ''CPLR''}"

definition "TLBEntries_names \<equiv> name ` (set TLBEntries)"

locale CHERI_MIPS_ISA =
  fixes translate_address :: "nat \<Rightarrow> acctype \<Rightarrow> register_value trace \<Rightarrow> nat option"
begin

abbreviation "fetch_and_decode \<equiv> (fetch () \<bind> (\<lambda>res. case res of Some ast \<Rightarrow> return ast | None \<Rightarrow> Fail ''decode''))"

definition
  "ISA \<equiv>
     \<lparr>instr_sem = execute,
      instr_fetch = fetch_and_decode,
      tag_granule = 32,
      PCC = {''PCC'', ''NextPCC'', ''DelayedPCC''},
      KCC = {''KCC''},
      IDC = {''C26''},
      caps_of_regval = (\<lambda>rv. case rv of Regval_Capability c \<Rightarrow> {c} | _ \<Rightarrow> {}),
      invokes_caps = (\<lambda>instr t. case instr of CCall _ \<Rightarrow> True | _ \<Rightarrow> False),
      instr_raises_ex = (\<lambda>instr t. hasException t (execute instr) \<or> hasFailure t (execute instr)),
      fetch_raises_ex = (\<lambda>t. hasException t (fetch_and_decode) \<or> hasFailure t (fetch_and_decode)),
      exception_targets = (\<lambda>rvs. \<Union>rv \<in> rvs. case rv of Regval_Capability c \<Rightarrow> {c} | _ \<Rightarrow> {}),
      privileged_regs = privileged_CHERI_regs,
      translation_tables = (\<lambda>t. {}),
      translate_address = translate_address\<rparr>"

interpretation Capability_ISA CC ISA by unfold_locales

sublocale Register_State get_regval set_regval .

lemma ISA_simps[simp]:
  "PCC ISA = {''PCC'', ''NextPCC'', ''DelayedPCC''}"
  "KCC ISA = {''KCC''}"
  "IDC ISA = {''C26''}"
  "privileged_regs ISA = privileged_CHERI_regs"
  "instr_sem ISA = execute"
  "instr_fetch ISA = (fetch () \<bind> (\<lambda>res. case res of Some ast \<Rightarrow> return ast | None \<Rightarrow> Fail ''decode''))"
  by (auto simp: ISA_def)

lemma invokes_caps_iff_CCall[simp]:
  "invokes_caps ISA instr t \<longleftrightarrow> (\<exists>cs cb sel. instr = CCall (cs, cb, sel))"
  by (cases instr) (auto simp: ISA_def)

lemma instr_raises_ex_iff[simp]:
  "instr_raises_ex ISA instr t \<longleftrightarrow> hasException t (execute instr) \<or> hasFailure t (execute instr)"
  by (auto simp: ISA_def)

lemma fetch_raises_ex_iff[simp]:
  "fetch_raises_ex ISA t \<longleftrightarrow> hasException t (fetch_and_decode) \<or> hasFailure t (fetch_and_decode)"
  by (auto simp: ISA_def)

lemma TLBEntries_no_cap:
  assumes "r \<in> set TLBEntries"
  shows "\<And>c. of_regval r (Regval_Capability c) = None" and "name r \<noteq> ''KCC''"
  using assms
  unfolding TLBEntries_def register_defs
  by auto

lemma [simp]: "length TLBEntries = 64"
  by (auto simp: TLBEntries_def)

lemma vector_of_regval_Regval_Capability_None[simp]:
  "vector_of_regval or (Regval_Capability c) = None"
  by (auto simp: vector_of_regval_def)

definition is_cap_reg :: "('s, register_value, Capability) register_ref \<Rightarrow> bool" where
  "is_cap_reg r = (\<forall>v c. of_regval r v = Some c \<longleftrightarrow> v = Regval_Capability c)"

lemma Capability_of_regval_Some_iff_Regval_Capability[simp]:
  "Capability_of_regval v = Some c \<longleftrightarrow> v = Regval_Capability c"
  by (cases v) auto

lemma caps_of_regval_of_Capability[simp]:
  "caps_of_regval ISA (regval_of_Capability c) = {c}"
  by (auto simp: regval_of_Capability_def ISA_def)

lemma CapRegs_is_cap_reg: "r \<in> set CapRegs \<Longrightarrow> is_cap_reg r"
  unfolding register_defs CapRegs_def
  by (auto simp: is_cap_reg_def)

lemma [simp]: "length CapRegs = 32"
  by (auto simp: CapRegs_def)

definition "CapRegs_names \<equiv> name ` (set CapRegs)"

lemma CapRegs_names_unfold[simp]:
  "CapRegs_names =
   {''C31'', ''C30'', ''C29'', ''C28'', ''C27'', ''C26'', ''C25'', ''C24'', ''C23'', ''C22'', ''C21'',
    ''C20'', ''C19'', ''C18'', ''C17'', ''C16'', ''C15'', ''C14'', ''C13'', ''C12'', ''C11'', ''C10'',
    ''C09'', ''C08'', ''C07'', ''C06'', ''C05'', ''C04'', ''C03'', ''C02'', ''C01'', ''DDC''}"
  unfolding CapRegs_names_def CapRegs_def register_defs
  by auto

lemma name_CapRegs_CapRegs_names: "r \<in> set CapRegs \<Longrightarrow> name r \<in> CapRegs_names"
  unfolding CapRegs_names_def
  by auto

lemma name_CapRegs_not_privileged[simp]:
  assumes "r \<in> set CapRegs"
  shows "name r \<noteq> ''PCC''"
        "name r \<noteq> ''EPCC''"
        "name r \<noteq> ''ErrorEPCC''"
        "name r \<noteq> ''KDC''"
        "name r \<noteq> ''KCC''"
        "name r \<noteq> ''KR1C''"
        "name r \<noteq> ''KR2C''"
        "name r \<noteq> ''CapCause''"
        "name r \<noteq> ''CPLR''"
  using assms
  by (auto dest: name_CapRegs_CapRegs_names)

lemma TLBEntries_names_unfold[simp]:
  "TLBEntries_names =
     {''TLBEntry63'', ''TLBEntry62'', ''TLBEntry61'', ''TLBEntry60'', ''TLBEntry59'',
      ''TLBEntry58'', ''TLBEntry57'', ''TLBEntry56'', ''TLBEntry55'', ''TLBEntry54'',
      ''TLBEntry53'', ''TLBEntry52'', ''TLBEntry51'', ''TLBEntry50'', ''TLBEntry49'',
      ''TLBEntry48'', ''TLBEntry47'', ''TLBEntry46'', ''TLBEntry45'', ''TLBEntry44'',
      ''TLBEntry43'', ''TLBEntry42'', ''TLBEntry41'', ''TLBEntry40'', ''TLBEntry39'',
      ''TLBEntry38'', ''TLBEntry37'', ''TLBEntry36'', ''TLBEntry35'', ''TLBEntry34'',
      ''TLBEntry33'', ''TLBEntry32'', ''TLBEntry31'', ''TLBEntry30'', ''TLBEntry29'',
      ''TLBEntry28'', ''TLBEntry27'', ''TLBEntry26'', ''TLBEntry25'', ''TLBEntry24'',
      ''TLBEntry23'', ''TLBEntry22'', ''TLBEntry21'', ''TLBEntry20'', ''TLBEntry19'',
      ''TLBEntry18'', ''TLBEntry17'', ''TLBEntry16'', ''TLBEntry15'', ''TLBEntry14'',
      ''TLBEntry13'', ''TLBEntry12'', ''TLBEntry11'', ''TLBEntry10'', ''TLBEntry09'',
      ''TLBEntry08'', ''TLBEntry07'', ''TLBEntry06'', ''TLBEntry05'', ''TLBEntry04'',
      ''TLBEntry03'', ''TLBEntry02'', ''TLBEntry01'', ''TLBEntry00''}"
  unfolding TLBEntries_def register_defs TLBEntries_names_def
  by auto

lemma ref_name_not_PCC[simp]:
  "name CapCause_ref \<noteq> ''PCC''"
  "name CP0Cause_ref \<noteq> ''PCC''"
  "name CP0Status_ref \<noteq> ''PCC''"
  "name TLBEntryHi_ref \<noteq> ''PCC''"
  "name TLBEntryLo0_ref \<noteq> ''PCC''"
  "name TLBEntryLo1_ref \<noteq> ''PCC''"
  "name TLBContext_ref \<noteq> ''PCC''"
  "name TLBXContext_ref \<noteq> ''PCC''"
  by (auto simp: register_defs)

lemma uint6_upper_bound[simp]: "uint (idx :: 6 word) \<le> 63"
  using uint_bounded[of idx]
  by auto

lemma upto_63_unfold:
  "{0..63} = {0 :: int, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
              20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
              40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
              60, 61, 62, 63}"
  by eval

lemma TLBEntry_name_not_PCC[simp]:
  assumes "idx \<in> {0..63}"
  shows "name (TLBEntries ! (64 - nat (idx + 1))) \<noteq> ''PCC''"
  using assms
  unfolding upto_63_unfold
  by (auto simp: TLBEntries_def register_defs)

lemma upto_31_unfold: "{0..31} = {0 :: int, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31}"
  by eval

lemma [simp]: "uint (idx :: 5 word) \<le> 31"
  using uint_bounded[of idx]
  by auto

lemma [simp]: "caps_of_regval ISA (Regval_Capability c) = {c}"
  by (auto simp: ISA_def)

lemma [simp]: "bits_of_mem_bytes (mem_bytes_of_word (capToMemBits c)) = map bitU_of_bool (to_bl (capToMemBits c))"
  unfolding mem_bytes_of_word_def bits_of_mem_bytes_def bits_of_bytes_def 
  by (auto simp: append_assoc[symmetric] take_add[symmetric] simp del: append_assoc)

lemma [simp]: "of_bits_method BC_mword (bits_of_mem_bytes (mem_bytes_of_word (capToMemBits c))) = Some (capToMemBits c)"
  by auto

lemma Capability_tag_memBitsToCapability[simp]:
  "Capability_tag (memBitsToCapability tag c) = tag"
  by (auto simp: memBitsToCapability_def capBitsToCapability_def)

lemma Run_throw_False[simp]: "Run (throw e) t a \<longleftrightarrow> False"
  by (auto simp: throw_def)

lemma Run_SignalException_False[simp]:
  "Run (SignalException e) t a \<longleftrightarrow> False"
  by (auto simp: SignalException_def elim!: Run_bindE)

lemma Run_SignalException_wrappers_False[simp]:
  "Run (SignalExceptionTLB ex badAddr) t a \<longleftrightarrow> False"
  "Run (SignalExceptionBadAddr ex badAddr) t a \<longleftrightarrow> False"
  by (auto simp: SignalExceptionTLB_def SignalExceptionBadAddr_def elim!: Run_bindE)

lemma Run_raise_c2_exception_False[simp]:
  "Run (raise_c2_exception8 capEx reg8) t a \<longleftrightarrow> False"
  "Run (raise_c2_exception capEx reg5) t a \<longleftrightarrow> False"
  "Run (raise_c2_exception_noreg capEx) t a \<longleftrightarrow> False"
  by (auto simp: raise_c2_exception8_def raise_c2_exception_def raise_c2_exception_noreg_def elim!: Run_bindE)

lemma Done_eq_bind_iff:
  "Done a = (m \<bind> f) \<longleftrightarrow> (\<exists>a'. m = Done a' \<and> f a' = Done a)"
  "(m \<bind> f) = Done a \<longleftrightarrow> (\<exists>a'. m = Done a' \<and> f a' = Done a)"
  by (cases m; auto)+

lemma Exception_eq_bind_iff:
  "Exception e = (m \<bind> f) \<longleftrightarrow> (m = Exception e \<or> (\<exists>a. m = Done a \<and> f a = Exception e))"
  "(m \<bind> f) = Exception e \<longleftrightarrow> (m = Exception e \<or> (\<exists>a. m = Done a \<and> f a = Exception e))"
  by (cases m; auto)+

lemma read_reg_no_ex: "(read_reg r, t, Exception e) \<in> Traces \<longleftrightarrow> False"
  by (auto simp: read_reg_def elim: Read_reg_TracesE split: option.splits)

lemma [simp]: "bit_to_bool (bitU_of_bool b) = b"
  by (auto simp: bitU_of_bool_def)

lemma to_bl_bool_to_bits: "to_bl (bool_to_bits b) = [b]"
  by (auto simp: bool_to_bits_def) eval

lemma memBitsToCapability_capToMemBits[simp]:
  "memBitsToCapability tag (capToMemBits c) = c\<lparr>Capability_tag := tag\<rparr>"
  unfolding memBitsToCapability_def capToMemBits_def capToBits_def capBitsToCapability_def
  by (auto simp: word_bw_assocs subrange_vec_dec_subrange_list_dec slice_take word_cat_bl
                 of_bl_append_same getCapPerms_def getCapHardPerms_def test_bit_of_bl nth_append append_assoc[symmetric]
           simp del: append_assoc)
     (auto simp: to_bl_bool_to_bits)

lemma [simp]: "Capability_tag c \<Longrightarrow> c\<lparr>Capability_tag := True\<rparr> = c"
  by (cases c) auto

end

locale CHERI_MIPS_Axiom_Automaton = CHERI_MIPS_ISA +
  fixes enabled :: "(Capability, register_value) axiom_state \<Rightarrow> register_value event \<Rightarrow> bool"
begin

sublocale Cap_Axiom_Automaton CC ISA enabled ..

(*lemma non_cap_exp_reg_deref[non_cap_expI]:
  assumes "non_cap_exp (read_reg r :: (register_value, 'a, 'ex) monad)"
  shows "non_cap_exp (reg_deref r :: (register_value, 'a, 'ex) monad)"
  using assms
  by (auto simp: reg_deref_def)*)

lemma non_cap_exp_undefineds[non_cap_expI]:
  "non_cap_exp (undefined_unit u)"
  "non_cap_exp (undefined_string u)"
  "non_cap_exp (undefined_int u)"
  "non_cap_exp (undefined_range x y)"
  "non_cap_exp (undefined_bitvector n)"
  unfolding undefined_unit_def undefined_string_def undefined_int_def undefined_bitvector_def undefined_range_def
  by non_cap_expI

lemma non_cap_exp_barrier[non_cap_expI]:
  "non_cap_exp (barrier b)"
  unfolding barrier_def non_cap_exp_def
  by (auto elim: Traces_cases)

lemma non_cap_exp_skip[non_cap_expI]:
  "non_cap_exp (skip u)"
  unfolding skip_def
  by non_cap_expI

lemma non_cap_exp_maybe_fail[non_cap_expI]:
  "non_cap_exp (maybe_fail msg x)"
  unfolding maybe_fail_def non_cap_exp_def
  by (auto split: option.splits)

lemma non_cap_exp_shift_bits[non_cap_expI]:
  "non_cap_exp (shift_bits_left BCa BCb BCd v n)"
  "non_cap_exp (shift_bits_right BCa BCb BCd v n)"
  "non_cap_exp (shift_bits_right_arith BCa BCb BCd v n)"
  unfolding shift_bits_left_def shift_bits_right_def shift_bits_right_arith_def
  by non_cap_expI

lemma no_cap_regvals[simp]:
  "\<And>v. bitvector_1_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. bitvector_3_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. bitvector_6_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. bitvector_8_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. bitvector_16_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. bitvector_32_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. bitvector_64_dec_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. CauseReg_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. StatusReg_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. ContextReg_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. XContextReg_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv 
= {}"
  "\<And>v. int_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. TLBEntry_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. TLBEntryHiReg_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>v. TLBEntryLoReg_of_regval rv = Some v \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>xs. vector_of_regval of_rv rv = Some xs \<Longrightarrow> caps_of_regval ISA rv = {}"
  "\<And>xs. caps_of_regval ISA (regval_of_vector rv_of xs) = {}"
  by (cases rv; auto simp: ISA_def vector_of_regval_def regval_of_vector_def)+

lemma non_cap_reg_nth_TLBEntries[intro, simp]:
  assumes "idx \<in> {0..63}"
  shows "non_cap_reg (TLBEntries ! (64 - nat (idx + 1)))"
  using assms
  unfolding upto_63_unfold
  by (elim insertE) (auto simp: TLBEntries_def register_defs non_cap_reg_def)

lemma non_cap_exp_read_reg_access_TLBEntries[non_cap_expI]:
  assumes "idx \<in> {0..63}"
  shows "non_cap_exp (read_reg (access_list_dec TLBEntries idx))"
  using assms
  by non_cap_expI

lemma no_reg_writes_to_case_option[no_reg_writes_toI]:
  assumes "\<And>a. no_reg_writes_to Rs (f a)"
    and "no_reg_writes_to Rs m"
  shows "no_reg_writes_to Rs (case x of Some a \<Rightarrow> f a | None \<Rightarrow> m)"
  using assms
  by (cases x) auto

(*lemma no_reg_writes_to_reg_deref[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (reg_deref r)"
  unfolding reg_deref_def
  by no_reg_writes_toI*)

lemma no_reg_writes_to_undefineds[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (undefined_unit u)"
  "no_reg_writes_to Rs (undefined_string u)"
  "no_reg_writes_to Rs (undefined_int u)"
  "no_reg_writes_to Rs (undefined_range x y)"
  "no_reg_writes_to Rs (undefined_bitvector n)"
  unfolding undefined_unit_def undefined_string_def undefined_int_def undefined_range_def undefined_bitvector_def
  by (no_reg_writes_toI)+

lemma no_reg_writes_to_barrier[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (barrier b)"
  unfolding barrier_def no_reg_writes_to_def
  by (auto elim: Traces_cases)

lemma no_reg_writes_to_skip[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (skip u)"
  unfolding skip_def
  by no_reg_writes_toI

lemma no_reg_writes_to_maybe_fail[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (maybe_fail msg x)"
  unfolding maybe_fail_def non_cap_exp_def
  by (auto split: option.splits)

lemma no_reg_writes_to_shift_bits[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (shift_bits_left BCa BCb BCd v n)"
  "no_reg_writes_to Rs (shift_bits_right BCa BCb BCd v n)"
  "no_reg_writes_to Rs (shift_bits_right_arith BCa BCb BCd v n)"
  unfolding shift_bits_left_def shift_bits_right_def shift_bits_right_arith_def
  by no_reg_writes_toI+

lemma no_reg_writes_to_write_ram[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (write_ram arg0 arg1 arg2 arg3 arg4)"
  unfolding write_ram_def MEMea_def MEMval_def
  by no_reg_writes_toI

lemma no_reg_writes_to_read_ram[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (read_ram arg0 arg1 arg2 arg3)"
  unfolding read_ram_def MEMr_def
  by no_reg_writes_toI

lemma no_reg_writes_to_read_memt_bytes[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (read_memt_bytes BCa BCb rk addr sz)"
  unfolding read_memt_bytes_def maybe_fail_def
  by (auto simp: no_reg_writes_to_def elim: bind_Traces_cases Traces_cases split: option.splits)

lemma no_reg_writes_to_read_memt[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (read_memt BCa BCb rk addr sz)"
  unfolding read_memt_def
  by no_reg_writes_toI

lemma no_reg_writes_to_write_memt[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (write_memt BCa BCb wk addr sz v t)"
  unfolding write_memt_def
  by (auto simp: no_reg_writes_to_def elim: Traces_cases split: option.splits)

lemma no_reg_writes_to_MEMval_tagged[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMval_tagged addr sz t v)"
  unfolding MEMval_tagged_def
  by no_reg_writes_toI

lemma no_reg_writes_to_MEMval_tagged_conditional[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (MEMval_tagged_conditional addr sz t v)"
  unfolding MEMval_tagged_conditional_def
  by no_reg_writes_toI

lemma runs_no_reg_writes_to_SignalException[runs_no_reg_writes_toI]:
  "runs_no_reg_writes_to Rs (SignalException ex)"
  unfolding runs_no_reg_writes_to_def
  by auto

lemma runs_no_reg_writes_to_raise_c2_exception[runs_no_reg_writes_toI]:
  "runs_no_reg_writes_to Rs (raise_c2_exception8 capEx reg8)"
  "runs_no_reg_writes_to Rs (raise_c2_exception capEx reg5)"
  "runs_no_reg_writes_to Rs (raise_c2_exception_noreg capEx)"
  by (auto simp: runs_no_reg_writes_to_def)

lemma runs_no_reg_writes_to_checkCP0AccessHook[runs_no_reg_writes_toI]:
  "runs_no_reg_writes_to Rs (checkCP0AccessHook u)"
  unfolding checkCP0AccessHook_def pcc_access_system_regs_def
  by (no_reg_writes_toI)

lemma no_reg_writes_to_writeCapReg[no_reg_writes_toI, simp]:
  assumes "CapRegs_names \<inter> Rs = {}"
  shows "no_reg_writes_to Rs (writeCapReg arg0 arg1)"
  using assms name_CapRegs_CapRegs_names[of "access_list_dec CapRegs (uint arg0)"]
  unfolding writeCapReg_def bind_assoc capToString_def
  by (intro no_reg_writes_toI) (auto simp del: CapRegs_names_unfold)

lemma no_reg_writes_to_readCapReg[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (readCapReg arg0)"
  unfolding readCapReg_def bind_assoc
  by (no_reg_writes_toI)

lemma no_reg_writes_to_readCapRegDDC[no_reg_writes_toI, simp]:
  "no_reg_writes_to Rs (readCapRegDDC arg0)"
  unfolding readCapRegDDC_def bind_assoc
  by (no_reg_writes_toI)

lemma non_mem_exp_rwCapReg[non_mem_expI]:
  "non_mem_exp (readCapReg r)"
  "non_mem_exp (readCapRegDDC r)"
  "non_mem_exp (writeCapReg r v)"
  by (non_mem_expI simp: readCapReg_def readCapRegDDC_def writeCapReg_def capToString_def)

declare MemAccessType.split[where P = "\<lambda>m. no_reg_writes_to Rs m" for Rs, THEN iffD2, no_reg_writes_toI]
declare MemAccessType.split[split]
declare WordType.split[where P = "\<lambda>m. no_reg_writes_to Rs m" for Rs, THEN iffD2, no_reg_writes_toI]
declare WordType.split[split]
declare ClearRegSet.split[where P = "\<lambda>m. no_reg_writes_to Rs m" for Rs, THEN iffD2, no_reg_writes_toI]
declare ClearRegSet.split[split]

end

locale CHERI_MIPS_Axiom_Inv_Automaton = CHERI_MIPS_Axiom_Automaton +
  Cap_Axiom_Inv_Automaton where CC = CC and ISA = ISA and get_regval = get_regval and set_regval = set_regval
begin

lemma preserve_invariant_undefineds[preserves_invariantI]:
  "traces_preserve_invariant (undefined_unit u)"
  "traces_preserve_invariant (undefined_string u)"
  "traces_preserve_invariant (undefined_int u)"
  "traces_preserve_invariant (undefined_range x y)"
  "traces_preserve_invariant (undefined_bitvector n)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg; simp)+

lemma preserves_invariant_barrier[no_reg_writes_toI, simp]:
  "traces_preserve_invariant (barrier b)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg; simp)+

lemma preserves_invariant_skip[no_reg_writes_toI, simp]:
  "traces_preserve_invariant (skip u)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg; simp)+

lemma preserves_invariant_maybe_fail[no_reg_writes_toI, simp]:
  "traces_preserve_invariant (maybe_fail msg x)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg; simp)+

lemma preserves_invariant_shift_bits[no_reg_writes_toI, simp]:
  "traces_preserve_invariant (shift_bits_left BCa BCb BCd v n)"
  "traces_preserve_invariant (shift_bits_right BCa BCb BCd v n)"
  "traces_preserve_invariant (shift_bits_right_arith BCa BCb BCd v n)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg; simp)+

lemma preserves_invariant_write_ram[preserves_invariantI]:
  "traces_preserve_invariant (write_ram arg0 arg1 arg2 arg3 arg4)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg; simp)

lemma preserves_invariant_read_ram[preserves_invariantI]:
  "traces_preserve_invariant (read_ram arg0 arg1 arg2 arg3)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg; simp)

(*lemma traces_preserve_True[preserves_invariantI, simp]:
  "traces_preserve_invariant m"
  by (auto simp: traces_preserve_invariant_def trace_preserves_invariant_def)*)

lemma traces_enabled_case_option[traces_enabledI]:
  assumes "\<And>a. x = Some a \<Longrightarrow> traces_enabled (f a) s regs"
    and "x = None \<Longrightarrow> traces_enabled m s regs"
  shows "traces_enabled (case x of Some a \<Rightarrow> f a | None \<Rightarrow> m) s regs"
  using assms
  by (cases x) auto

lemma Run_inv_ifE:
  assumes "Run_inv (if c then m1 else m2) t a regs"
  obtains "Run_inv m1 t a regs" and "c" | "Run_inv m2 t a regs" and "\<not>c"
  using assms
  by (auto split: if_splits)

lemma Run_inv_letE:
  assumes "Run_inv (let x = y in f x) t a regs"
  obtains "Run_inv (f y) t a regs"
  using assms
  by auto

declare Run_inv_ifE[where t = t and thesis = "c \<in> derivable_caps (run s t)" for s t c, derivable_capsE]
declare Run_inv_letE[where t = t and thesis = "c \<in> derivable_caps (run s t)" for s t c, derivable_capsE]

lemma Run_inv_return[simp]: "Run_inv (return a) t a' regs \<longleftrightarrow> (a' = a \<and> t = [] \<and> invariant regs)"
  unfolding Run_inv_def
  by auto

lemma null_cap_derivable[intro, simp]: "null_cap \<in> derivable_caps s"
  unfolding null_cap_def derivable_caps_def
  by auto

lemma read_reg_access_CapRegs_derivable_caps[derivable_capsE]:
  assumes "Run_inv (read_reg (access_list_dec CapRegs idx)) t c regs"
    and "idx \<in> {0..31}" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  unfolding Run_inv_def upto_31_unfold
  by (elim insertE conjE Run_read_regE)
     (auto simp: CapRegs_def CapRegs_names_def derivable_caps_def register_defs intro!: derivable.Copy)

lemma memt_builtins_preserve_invariant[preserves_invariantI]:
  "\<And>BCa BCb rk addr sz. traces_preserve_invariant (read_memt_bytes BCa BCb rk addr sz)"
  "\<And>BCa BCb rk addr sz. traces_preserve_invariant (read_memt BCa BCb rk addr sz)"
  "\<And>BCa BCb wk addr sz v t. traces_preserve_invariant (write_memt BCa BCb wk addr sz v t)"
  "\<And>addr sz t v. traces_preserve_invariant (MEMval_tagged addr sz t v)"
  "\<And>addr sz t v. traces_preserve_invariant (MEMval_tagged_conditional addr sz t v)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg; simp)+

lemma dvd_8_Suc_iffs[simp]:
  "8 dvd Suc (Suc 0) \<longleftrightarrow> False"
  "8 dvd Suc (Suc (Suc 0)) \<longleftrightarrow> False"
  "8 dvd Suc (Suc (Suc (Suc 0))) \<longleftrightarrow> False"
  "8 dvd Suc (Suc (Suc (Suc (Suc 0)))) \<longleftrightarrow> False"
  "8 dvd Suc (Suc (Suc (Suc (Suc (Suc 0))))) \<longleftrightarrow> False"
  "8 dvd Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) \<longleftrightarrow> False"
  "8 dvd Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc x))))))) \<longleftrightarrow> 8 dvd x"
  by presburger+

lemma byte_chunks_eq_Some_iff[simp]:
  shows "byte_chunks xs = Some ys \<longleftrightarrow> ys = take_chunks 8 xs \<and> 8 dvd length xs"
  by (induction xs arbitrary: ys rule: byte_chunks.induct) (auto simp: bind_eq_Some_conv)

lemma mem_bytes_of_bits_mword_eq_Some_iff[simp]:
  fixes w :: "'a::len word"
  shows "mem_bytes_of_bits BC_mword w = Some bytes \<longleftrightarrow> bytes = mem_bytes_of_word w \<and> 8 dvd LENGTH('a)"
  by (auto simp: mem_bytes_of_bits_def bytes_of_bits_def mem_bytes_of_word_def BC_mword_defs)

lemma concat_take_chunks[simp]:
  assumes "n > 0"
  shows "List.concat (take_chunks n xs) = xs"
  using assms
  by (induction n xs rule: take_chunks.induct) auto

lemma bits_of_mem_bytes_of_word[simp]:
  fixes w :: "'a::len word"
  assumes "8 dvd LENGTH('a)"
  shows "bits_of_mem_bytes (mem_bytes_of_word w) = map bitU_of_bool (to_bl w)"
  using assms
  by (auto simp add: bits_of_mem_bytes_def bits_of_bytes_def mem_bytes_of_word_def simp del: take_chunks.simps)

lemma bitU_of_bool_eq_iff[simp]:
  "bitU_of_bool b = B1 \<longleftrightarrow> b" "bitU_of_bool b = B0 \<longleftrightarrow> \<not>b"
  by (auto simp: bitU_of_bool_def)

lemma memBitsToCapability_False_derivable_caps[intro, simp, derivable_capsI]:
  shows "memBitsToCapability False w \<in> derivable_caps s"
  by (auto simp: derivable_caps_def)

lemma memBitsToCapability_ucast_256_derivable_caps[intro, simp, derivable_capsI]:
  assumes "memBitsToCapability tag w \<in> derivable_caps s"
  shows "memBitsToCapability tag (ucast w) \<in> derivable_caps s"
  using assms
  by auto

lemma memBitsToCapability_capToMemBits_derivable_caps[intro, derivable_capsI]:
  assumes c: "c \<in> derivable_caps s" and tag: "tag \<longrightarrow> Capability_tag c"
  shows "memBitsToCapability tag (capToMemBits c) \<in> derivable_caps s"
  using assms
  by (cases tag) (auto simp: derivable_caps_def)

lemma read_from_KCC_run_mono: "read_from_KCC s \<subseteq> read_from_KCC (run s t)"
proof (induction t arbitrary: s)
  case (Cons e t)
  have "read_from_KCC s \<subseteq> read_from_KCC (axiom_step s e)"
    by auto
  also have "\<dots> \<subseteq> read_from_KCC (run (axiom_step s e) t)"
    by (rule Cons.IH)
  finally show ?case
    unfolding foldl_Cons .
qed auto

lemma exception_targets_run_imp:
  assumes "c \<in> exception_targets ISA (read_from_KCC s)"
  shows "c \<in> exception_targets ISA (read_from_KCC (run s t))"
  using assms read_from_KCC_run_mono
  by (auto simp: ISA_def)

lemma exception_targets_insert[simp]:
  "exception_targets ISA (insert (Regval_Capability c) C) = insert c (exception_targets ISA C)"
  by (auto simp: ISA_def)

lemma read_reg_KCC_exception_targets:
  assumes "Run_inv (read_reg KCC_ref) t c regs"
  shows "c \<in> exception_targets ISA (read_from_KCC (run s t))"
  using assms
  unfolding Run_inv_def
  by (auto elim!: Run_read_regE simp: KCC_ref_def)

lemma leq_perms_refl[intro, simp]: "leq_perms p p"
  unfolding leq_perms_def
  by auto

lemma setCapOffset_getCapOffset_idem:
  assumes "setCapOffset c offset = (representable, c')"
    and "uint offset = getCapOffset c"
  shows "c' = c"
  using assms uint_bounded[of "Capability_address c"]
  by (cases c)
     (auto simp add: setCapOffset_def getCapOffset_def uint_word_ariths mod_add_right_eq simp flip: uint_inject)


lemma setCapOffset_derivable_caps[derivable_capsE]:
  assumes "setCapOffset c offset = (representable, c')"
    and "Capability_tag c \<Longrightarrow> Capability_tag c' \<Longrightarrow> Capability_sealed c \<and> Capability_sealed c' \<Longrightarrow> uint offset = getCapOffset c"
    and "c \<in> derivable_caps s"
  shows "c' \<in> derivable_caps s"
proof -
  have "leq_cap CC c' c"
    using assms setCapOffset_getCapOffset_idem[OF assms(1)]
    by (auto simp: leq_cap_def setCapOffset_def getCapBase_def getCapTop_def get_cap_perms_def)
  then show ?thesis
    using assms
    by (auto simp: derivable_caps_def setCapOffset_def elim: derivable.Restrict)
qed

lemma Run_inv_return_derivable_caps[derivable_capsE]:
  assumes "Run_inv (return a) t a' regs" and "a \<in> derivable_caps s"
  shows "a' \<in> derivable_caps (run s t)" and "a' \<in> derivable_caps s"
  using assms
  by auto

lemma Run_inv_bind_derivable_caps[derivable_capsE]:
  assumes "Run_inv (m \<bind> f) t a regs" and "runs_preserve_invariant m"
    and "\<And>tm am tf. t = tm @ tf \<Longrightarrow> Run_inv m tm am regs \<Longrightarrow> Run_inv (f am) tf a (the (updates_regs inv_regs tm regs)) \<Longrightarrow> c \<in> derivable_caps (run (run s tm) tf)"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  by (elim Run_inv_bindE) auto

lemma int_to_cap_derivable_caps[derivable_capsI]:
  "unrepCap c \<in> derivable_caps s"
  by (auto simp: unrepCap_def derivable_caps_def)

lemma update_Capability_tag_derivable_caps[derivable_capsI]:
  assumes "t \<Longrightarrow> c \<in> derivable_caps s" and "t \<Longrightarrow> Capability_tag c"
  shows "c\<lparr>Capability_tag := t\<rparr> \<in> derivable_caps s"
  using assms
  by (cases "Capability_tag c") (auto simp: derivable_caps_def)


lemma preserves_invariant_readCapReg[preserves_invariantI]:
  "\<And>arg0. traces_preserve_invariant (readCapReg arg0)"
  "\<And>arg0. traces_preserve_invariant (readCapRegDDC arg0)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_toI; simp)+

lemma readCapReg_derivable[derivable_capsE]:
  assumes "Run_inv (readCapReg arg0) t c regs" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  unfolding readCapReg_def
  by (-) (derivable_capsI assms: assms)

lemma readCapRegDDC_derivable[derivable_capsE]:
  assumes "Run_inv (readCapRegDDC arg0) t c regs" and "CapRegs_names \<subseteq> accessible_regs s"
  shows "c \<in> derivable_caps (run s t)"
  using assms
  unfolding readCapRegDDC_def
  by (-) (derivable_capsI assms: assms)

lemma caps_of_CapCauseReg_empty[simp]: "caps_of_regval ISA (regval_of_CapCauseReg r) = {}"
  by (auto simp: ISA_def regval_of_CapCauseReg_def)

lemma letI: "P (let x = y in f x)" if "P (f y)"
  using that
  by auto

declare if_split[where P = "\<lambda>m. runs_preserve_invariant m", THEN iffD2, preserves_invariantI]
declare option.split[where P = "\<lambda>m. runs_preserve_invariant m", THEN iffD2, preserves_invariantI]
declare prod.split[where P = "\<lambda>m. runs_preserve_invariant m", THEN iffD2, preserves_invariantI]
declare sum.split[where P = "\<lambda>m. runs_preserve_invariant m", THEN iffD2, preserves_invariantI]
declare letI[where P = "\<lambda>m. runs_preserve_invariant m", preserves_invariantI]

declare MemAccessType.split[where P = "\<lambda>m. traces_enabled m s regs" for s regs, traces_enabled_split]
declare MemAccessType.split[where P = "\<lambda>m. runs_preserve_invariant m" for Rs, THEN iffD2, preserves_invariantI]
declare MemAccessType.split[where P = "\<lambda>m. traces_preserve_invariant m" for Rs, THEN iffD2, preserves_invariantI]
declare WordType.split[where P = "\<lambda>m. traces_enabled m s regs" for s regs, traces_enabled_split]
declare WordType.split[where P = "\<lambda>m. runs_preserve_invariant m" for Rs, THEN iffD2, preserves_invariantI]
declare WordType.split[where P = "\<lambda>m. traces_preserve_invariant m" for Rs, THEN iffD2, preserves_invariantI]
declare ClearRegSet.split[where P = "\<lambda>m. traces_enabled m s regs" for s regs, traces_enabled_split]
declare ClearRegSet.split[where P = "\<lambda>m. runs_preserve_invariant m" for Rs, THEN iffD2, preserves_invariantI]
declare ClearRegSet.split[where P = "\<lambda>m. traces_preserve_invariant m" for Rs, THEN iffD2, preserves_invariantI]

lemma preserves_invariant_SignalException[preserves_invariantI]:
  "runs_preserve_invariant (SignalException ex)"
  "runs_preserve_invariant (SignalExceptionBadAddr ex badAddr)"
  "runs_preserve_invariant (SignalExceptionTLB ex badAddr)"
  by (auto simp: runs_preserve_invariant_def)

lemma Run_raise_c2_exception_False[simp]:
  "Run_inv (raise_c2_exception8 capEx reg8) t a regs \<longleftrightarrow> False"
  "Run_inv (raise_c2_exception capEx reg5) t a regs \<longleftrightarrow> False"
  "Run_inv (raise_c2_exception_noreg capEx) t a regs \<longleftrightarrow> False"
  by (auto simp: Run_inv_def)

lemma runs_preserve_invariant_raise_c2_exception[preserves_invariantI]:
  "runs_preserve_invariant (raise_c2_exception8 capEx reg8)"
  "runs_preserve_invariant (raise_c2_exception capEx reg5)"
  "runs_preserve_invariant (raise_c2_exception_noreg capEx)"
  by (auto simp: runs_preserve_invariant_def)

end

locale CHERI_MIPS_Reg_Automaton = CHERI_MIPS_ISA +
  fixes ex_traces :: bool and invocation_traces :: bool
begin

abbreviation invariant where "invariant regs \<equiv> Capability_tag (regstate.PCC regs) \<and> \<not>Capability_sealed (regstate.PCC regs)"
abbreviation inv_regs :: "register_name set" where "inv_regs \<equiv> {''PCC''}"

sublocale Write_Cap_Inv_Automaton CC ISA ex_traces invocation_traces get_regval set_regval invariant inv_regs ..

sublocale CHERI_MIPS_Axiom_Inv_Automaton where enabled = enabled and invariant = invariant and inv_regs = inv_regs ..

lemma traces_enabled_read_reg_nth_CapRegs[traces_enabledI]:
  assumes "idx \<in> {0..31}"
  shows "traces_enabled (read_reg (access_list_dec CapRegs idx)) s regs"
  using assms
  unfolding upto_31_unfold
  by (elim insertE) (auto simp: CapRegs_def intro!: traces_enabled_read_reg)

lemma preserves_invariant_writeCapReg[preserves_invariantI]:
  "\<And>arg0 arg1. traces_preserve_invariant (writeCapReg arg0 arg1)"
  by (intro no_reg_writes_traces_preserve_invariantI no_reg_writes_toI; simp)+

lemma traces_enabled_read_mem[traces_enabledI]:
  "traces_enabled (read_mem BCa BCb rk addr_sz addr sz) s regs"
  unfolding read_mem_def read_mem_bytes_def traces_enabled_def maybe_fail_def
  by (auto elim: bind_Traces_cases Traces_cases split: option.splits)

lemma traces_enabled_read_memt[traces_enabledI]:
  "traces_enabled (read_memt BCa BCb rk addr sz) s regs"
  unfolding read_memt_def read_memt_bytes_def traces_enabled_def maybe_fail_def
  by (auto elim: bind_Traces_cases Traces_cases split: option.splits)

lemma traces_enabled_write_mem_ea[traces_enabledI]:
  "traces_enabled (write_mem_ea BCa wk a1 a2 a3) s regs"
  unfolding write_mem_ea_def traces_enabled_def maybe_fail_def
  by (auto elim: bind_Traces_cases Traces_cases split: option.splits)

lemma traces_enabled_write_mem[traces_enabledI]:
  "traces_enabled (write_mem BCa BCb wk a1 a2 a3 a4) s regs"
  unfolding write_mem_def traces_enabled_def
  by (auto elim: bind_Traces_cases Traces_cases split: option.splits)

lemma traces_enabled_write_memt[traces_enabledI]:
  assumes "tag = B1 \<longrightarrow> memBitsToCapability True (ucast w) \<in> derivable_caps s"
  shows "traces_enabled (write_memt BCa BC_mword wk addr sz w tag) s regs"
  using assms
  unfolding write_memt_def traces_enabled_def
  by (cases tag; auto split: option.splits simp: bind_eq_Some_conv ucast_bl derivable_caps_def elim!: Write_memt_TracesE)

lemma traces_enabled_write_ram[traces_enabledI]:
  "traces_enabled (write_ram a0 a1 a2 a3 a4) s regs"
  unfolding write_ram_def MEMval_def MEMea_def
  by (traces_enabledI intro: non_cap_expI[THEN non_cap_exp_traces_enabledI])

lemma traces_enabled_read_ram[traces_enabledI]:
  "traces_enabled (read_ram a0 a1 a2 a3) s regs"
  unfolding read_ram_def MEMr_def
  by (traces_enabledI)

lemma traces_enabled_MEMval_tagged[traces_enabledI]:
  assumes "memBitsToCapability tag (ucast v) \<in> derivable_caps s"
  shows "traces_enabled (MEMval_tagged addr sz tag v) s regs"
  unfolding MEMval_tagged_def
  by (traces_enabledI intro: non_cap_expI[THEN non_cap_exp_traces_enabledI] assms: assms)

lemma traces_enabled_MEMval_tagged_conditional[traces_enabledI]:
  assumes "memBitsToCapability tag (ucast v) \<in> derivable_caps s"
  shows "traces_enabled (MEMval_tagged_conditional addr sz tag v) s regs"
  unfolding MEMval_tagged_conditional_def
  by (traces_enabledI intro: non_cap_expI[THEN non_cap_exp_traces_enabledI] assms: assms)

(*lemma slice_cat_left:
  fixes a :: "'a::len word" and b :: "'b::len word"
  defines "c \<equiv> word_cat a b :: 'c:: len word"
  assumes "n \<ge> LENGTH('b)" and "LENGTH('c) = LENGTH('a) + LENGTH('b)"
  shows "(Word.slice n c :: 'd::len word) = Word.slice (n - LENGTH('b)) a" (is "?l = ?r")
  using assms test_bit_len[where x = a and n = "n' + n - LENGTH('b)" for n']
  by (intro word_eqI) (fastforce simp: nth_slice test_bit_cat)*)

lemma traces_enabled_set_next_pcc_ex:
  assumes arg0: "arg0 \<in> exception_targets ISA (read_from_KCC s)" and ex: "ex_traces"
  shows "traces_enabled (set_next_pcc arg0) s regs"
  unfolding set_next_pcc_def bind_assoc
  by (traces_enabledI assms: arg0 exception_targets_run_imp
                      intro: traces_enabled_write_reg ex no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg traces_runs_preserve_invariantI
                      simp: DelayedPCC_ref_def NextPCC_ref_def)

lemma traces_enabled_write_reg_nth_CapRegs[traces_enabledI]:
  assumes "c \<in> derivable_caps s" and "idx \<in> {0..31}"
  shows "traces_enabled (write_reg (access_list_dec CapRegs idx) c) s regs"
  using assms
  unfolding upto_31_unfold derivable_caps_def
  by (elim insertE; auto intro!: traces_enabled_write_reg simp: CapRegs_def register_defs)

lemma traces_enabled_writeCapReg[traces_enabledI]:
  assumes "arg1 \<in> derivable_caps s"
  shows "traces_enabled (writeCapReg arg0 arg1) s regs"
  unfolding writeCapReg_def bind_assoc capToString_def
  by (traces_enabledI assms: assms intro: non_cap_expI[THEN non_cap_exp_traces_enabledI] no_reg_writes_traces_preserve_invariantI no_reg_writes_to_write_reg)

lemma traces_enabled_readCapReg[traces_enabledI]:
  shows "traces_enabled (readCapReg arg0) s regs"
  unfolding readCapReg_def bind_assoc
  by (traces_enabledI intro: non_cap_expI[THEN non_cap_exp_traces_enabledI])

lemma traces_enabled_readCapRegDDC[traces_enabledI]:
  shows "traces_enabled (readCapRegDDC arg0) s regs"
  unfolding readCapRegDDC_def bind_assoc
  by (traces_enabledI)

fun trace_writes_cap_regs :: "register_value trace \<Rightarrow> register_name set" where
  "trace_writes_cap_regs [] = {}"
| "trace_writes_cap_regs (e # t) =
     {r. \<exists>v c. e = E_write_reg r v \<and> c \<in> caps_of_regval ISA v \<and> is_tagged_method CC c} \<union>
     trace_writes_cap_regs t"


fun trace_allows_system_reg_access :: "register_name set \<Rightarrow> register_value trace \<Rightarrow> bool" where
  "trace_allows_system_reg_access Rs [] = False"
| "trace_allows_system_reg_access Rs (e # t) = (allows_system_reg_access Rs e \<or> trace_allows_system_reg_access (Rs - trace_writes_cap_regs [e]) t)"

lemma trace_allows_system_reg_access_append:
  "trace_allows_system_reg_access Rs (t1 @ t2) = (trace_allows_system_reg_access Rs t1 \<or> trace_allows_system_reg_access (Rs - trace_writes_cap_regs t1) t2)"
  by (induction t1 arbitrary: Rs) (auto simp: Diff_eq Int_assoc)

lemma [simp]: "accessible_regs s - written_regs s = accessible_regs s"
  by (auto simp: accessible_regs_def)

lemma system_reg_access_run:
  "system_reg_access (run s t) = (system_reg_access s \<or> trace_allows_system_reg_access (accessible_regs s) t)"
  by (induction t arbitrary: s) (auto simp: accessible_regs_axiom_step Diff_Un Diff_Int_distrib Diff_Int)

lemma pcc_access_system_regs_allows_system_reg_access:
  assumes "Run_inv (pcc_access_system_regs u) t a regs"
  shows "trace_allows_system_reg_access Rs t \<longleftrightarrow> a \<and> ''PCC'' \<in> Rs"
  using assms
  unfolding pcc_access_system_regs_def Run_inv_def
  by (auto elim!: Run_bindE Run_read_regE simp: PCC_ref_def get_regval_def regval_of_Capability_def get_cap_perms_def)

lemma checkCP0Access_system_reg_access:
  assumes "Run_inv (checkCP0Access ()) t () regs" and "{''PCC''} \<subseteq> accessible_regs s"
  shows "trace_allows_system_reg_access (accessible_regs s) t"
  using assms pcc_access_system_regs_allows_system_reg_access[where Rs = "accessible_regs s"]
  unfolding checkCP0Access_def checkCP0AccessHook_def Run_inv_def
  by (auto elim!: Run_bindE simp: regstate_simp system_reg_access_run pcc_access_system_regs_allows_system_reg_access trace_allows_system_reg_access_append split: if_splits)

lemma Run_inv_runs_no_reg_writes_written_regs_eq:
  assumes "Run_inv m t a regs" and "runs_no_reg_writes_to {r} m"
  shows "r \<in> written_regs (run s t) \<longleftrightarrow> r \<in> written_regs s"
  using assms
  by (auto simp: Run_inv_def Run_runs_no_reg_writes_written_regs_eq)

lemmas runs_no_reg_writes_written_regs_eq =
  Run_runs_no_reg_writes_written_regs_eq Run_inv_runs_no_reg_writes_written_regs_eq

end

abbreviation "noCP0Access s \<equiv> get_StatusReg_EXL (CP0Status s) = 0 \<and> get_StatusReg_ERL (CP0Status s) = 0 \<and> get_StatusReg_KSU (CP0Status s) \<noteq> 0 \<and> \<not>(get_StatusReg_CU (CP0Status s) !! 0)"

locale CHERI_MIPS_Fixed_Trans =
  fixes trans_regstate :: regstate (*and is_fetch :: bool*)
  assumes noCP0Access_trans_regstate: "noCP0Access trans_regstate"
begin

definition "trans_regs \<equiv> {''CP0Status'', ''TLBEntryHi'', ''PCC''} \<union> TLBEntries_names"
definition "trans_inv s \<equiv> (\<exists>pcc. s\<lparr>regstate.PCC := pcc\<rparr> = trans_regstate)"

lemma invariant_trans_regstate[intro, simp]:
  "trans_inv trans_regstate"
proof -
  have "trans_regstate\<lparr>regstate.PCC := regstate.PCC trans_regstate\<rparr> = trans_regstate"
    by auto
  then show ?thesis
    unfolding trans_inv_def
    by blast
qed

fun MemAccessType_of_acctype :: "acctype \<Rightarrow> MemAccessType" where
  "MemAccessType_of_acctype Load = LoadData"
| "MemAccessType_of_acctype Store = StoreData"
| "MemAccessType_of_acctype Fetch = Instruction"

sublocale State_Invariant get_regval set_regval trans_inv trans_regs .

definition translate_addressM :: "nat \<Rightarrow> acctype \<Rightarrow> nat M" where
  "translate_addressM vaddr acctype \<equiv>
     let vaddr = word_of_int (int vaddr) in
     TLBTranslate vaddr (MemAccessType_of_acctype acctype) \<bind> (\<lambda>paddr.
     return (unat paddr))"

definition translate_address :: "nat \<Rightarrow> acctype \<Rightarrow> 'a \<Rightarrow> nat option" where
  "translate_address vaddr acctype _ = (if (\<exists>t a regs. Run_inv (translate_addressM vaddr acctype) t a regs) then Some (the_result (translate_addressM vaddr acctype)) else None)"

sublocale CHERI_MIPS_ISA where translate_address = translate_address .

end

locale CHERI_MIPS_Mem_Automaton = CHERI_MIPS_Fixed_Trans +
  fixes is_fetch :: bool and ex_traces :: bool
begin

sublocale Mem_Inv_Automaton
  where CC = CC and ISA = ISA and is_fetch = is_fetch and ex_traces = ex_traces
    and translation_assm = "\<lambda>t. (\<exists>regs. reads_regs_from inv_regs t regs \<and> trans_inv regs)"
    and get_regval = get_regval and set_regval = set_regval
    and invariant = trans_inv and inv_regs = trans_regs
  by unfold_locales (auto simp: ISA_def translate_address_def)

sublocale CHERI_MIPS_Axiom_Inv_Automaton
  where translate_address = translate_address and enabled = enabled
    and invariant = trans_inv and inv_regs = trans_regs and ex_traces = ex_traces
  by unfold_locales

(*lemma determ_runs_TLBTranslate: "determ_runs (TLBTranslate vaddr acctype)"
  sorry

lemma runs_preserve_invariant_TLBTranslate: "runs_preserve_invariant (TLBTranslate vaddr acctype)"
  sorry*)

lemma preserves_invariant_tlbSearch[preserves_invariantI]:
  "traces_preserve_invariant (tlbSearch vAddr)"
  unfolding tlbSearch_def
  by (preserves_invariantI)

lemma preserves_invariant_checkCP0AccessHook[preserves_invariantI]:
  "runs_preserve_invariant (checkCP0AccessHook u)"
  unfolding checkCP0AccessHook_def pcc_access_system_regs_def bind_assoc
  by preserves_invariantI

lemma preserves_invariant_getAccessLevel[preserves_invariantI]:
  "traces_preserve_invariant (getAccessLevel u)"
  unfolding getAccessLevel_def
  by (preserves_invariantI)

fun_cases StatusReg_of_regval_SomeE: "StatusReg_of_regval rv = Some a"

lemma read_reg_CP0Status_inv_fields:
  assumes "Run_inv (read_reg CP0Status_ref) t a regs"
  shows "get_StatusReg_EXL a = 0" and "get_StatusReg_ERL a = 0" and "get_StatusReg_KSU a \<noteq> 0"
    and "\<not>(get_StatusReg_CU a !! 0)"
  using assms noCP0Access_trans_regstate
  unfolding Run_inv_def trans_inv_def
  by (auto elim!: Run_read_regE StatusReg_of_regval_SomeE simp: CP0Status_ref_def trans_regs_def get_regval_def regval_of_StatusReg_def)

lemma bits_to_bool_iff_one:
  "bits_to_bool w \<longleftrightarrow> w = 1"
  by (cases w rule: exhaustive_1_word) (auto simp: bits_to_bool_def)

lemma Run_inv_getAccessLevel_neq_Kernel:
  assumes "Run_inv (getAccessLevel u) t a regs"
  shows "a \<noteq> Kernel"
  using assms
  unfolding getAccessLevel_def Let_def or_boolM_def
  by (auto simp: regstate_simp bits_to_bool_iff_one read_reg_CP0Status_inv_fields
           elim!: Run_inv_bindE intro!: preserves_invariantI traces_runs_preserve_invariantI split: if_splits)

lemma Run_inv_checkCP0Access_False[simp]:
  "Run_inv (checkCP0Access u) t a regs \<longleftrightarrow> False"
proof -
  define signal_ex :: "unit M"
    where "signal_ex \<equiv> set_CauseReg_CE CP0Cause_ref (vec_of_bits [B0, B0]) \<then> SignalException CpU"
  have "Run_inv signal_ex t a regs \<longleftrightarrow> False" for t a regs
    unfolding signal_ex_def Run_inv_def
    by (auto elim!: Run_bindE)
  then show ?thesis
    unfolding checkCP0Access_def and_boolM_def bind_assoc signal_ex_def[symmetric]
    by (auto elim!: Run_inv_bindE dest!: Run_inv_getAccessLevel_neq_Kernel
             intro!: preserves_invariantI traces_runs_preserve_invariantI
             simp: read_reg_CP0Status_inv_fields)
qed

lemma trans_inv_regs_eq_trans_regstate:
  assumes "trans_inv regs"
  shows "CP0Status regs = CP0Status trans_regstate \<and> TLBEntryHi regs = TLBEntryHi trans_regstate"
  using assms
  by (auto simp: trans_inv_def)

lemma determ_runs_read_reg_CP0Status[determ]: "determ_runs (read_reg CP0Status_ref)"
  by (intro determ_runs_read_inv_reg) (auto simp: trans_regs_def register_defs dest: trans_inv_regs_eq_trans_regstate)

lemma determ_runs_SignalExceptionBadAddr[determ]: "determ_runs (SignalExceptionBadAddr ex badAddr)"
  by (intro determ_runsI) (auto simp: Run_inv_def)

lemma determ_runs_SignalExceptionTLB[determ]: "determ_runs (SignalExceptionTLB ex badAddr)"
  by (intro determ_runsI) (auto simp: Run_inv_def)

lemma get_regval_TLBEntries:
  "r \<in> set TLBEntries \<Longrightarrow> trans_inv regs \<Longrightarrow> get_regval (name r) regs = Some (regval_of_TLBEntry (read_from r trans_regstate))"
  by (auto simp: TLBEntries_def trans_inv_def; simp add: register_defs)

lemma read_from_TLBEntries:
  assumes "idx \<in> {0..63}" and "trans_inv regs"
  shows "read_from (TLBEntries ! (64 - nat (idx + 1))) trans_regstate = read_from (TLBEntries ! (64 - nat (idx + 1))) regs"
  using assms
  unfolding upto_63_unfold
  by (elim insertE) (auto simp: trans_inv_def TLBEntries_def register_defs)

lemma of_regval_TLBEntries_nth[simp]:
  "idx \<in> {0..63} \<Longrightarrow> of_regval (TLBEntries ! (64 - nat (idx + 1))) v = TLBEntry_of_regval v"
  unfolding upto_63_unfold
  by (elim insertE) (auto simp: TLBEntries_def register_defs)

lemma determ_runs_read_reg_access_TLBEntries[determ]:
  "determ_traces (read_reg (access_list_dec TLBEntries idx))" if "idx \<in> {0..63}"
  using that
  by (intro determ_traces_read_inv_reg)
     (auto simp del: TLBEntries_names_unfold
           simp add: trans_regs_def TLBEntries_names_def regval_of_TLBEntry_def
           intro!: get_regval_TLBEntries read_from_TLBEntries)

lemma determ_traces_read_reg_TLBEntryHi[determ]:
  "determ_traces (read_reg TLBEntryHi_ref)"
  by (intro determ_traces_read_inv_reg)
     (auto simp: TLBEntryHi_ref_def trans_regs_def get_regval_def dest: trans_inv_regs_eq_trans_regstate)

lemma determ_traces_tlbSearch[determ]:
  "determ_runs (tlbSearch vAddr)"
  unfolding tlbSearch_def Let_def
  by (intro determ determ_traces_bindI determ_traces_foreachM determ_traces_if determ_traces_runs
            preserves_invariantI traces_runs_preserve_invariantI allI conjI impI)
      auto

lemma determ_runs_translate_addressM: "determ_runs (translate_addressM vaddr is_load)"
  unfolding translate_addressM_def TLBTranslate_def TLBTranslateC_def TLBTranslate2_def
            getAccessLevel_def undefined_range_def Let_def bind_assoc
  by (intro determ_runs_bindI determ_runs_if determ determ_traces_runs
            preserves_invariantI traces_runs_preserve_invariantI allI conjI impI)
      auto

lemma TLBTranslate_LoadData_translate_address_eq[simp]:
  assumes "Run_inv (TLBTranslate vaddr LoadData) t paddr regs"
  shows "translate_address (unat vaddr) Load t' = Some (unat paddr)"
proof -
  from assms have "Run_inv (translate_addressM (unat vaddr) Load) t (unat paddr) regs"
    unfolding translate_addressM_def Run_inv_def
    by (auto simp flip: uint_nat intro: Traces_bindI[of _ t paddr _ "[]", simplified])
  then show ?thesis
    using determ_runs_translate_addressM
    by (auto simp: translate_address_def determ_the_result_eq)
qed

lemma TLBTranslate_StoreData_translate_address_eq[simp]:
  assumes "Run_inv (TLBTranslate vaddr StoreData) t paddr regs"
  shows "translate_address (unat vaddr) Store t' = Some (unat paddr)"
proof -
  from assms have "Run_inv (translate_addressM (unat vaddr) Store) t (unat paddr) regs"
    unfolding translate_addressM_def Run_inv_def
    by (auto simp flip: uint_nat intro: Traces_bindI[of _ t paddr _ "[]", simplified])
  then show ?thesis
    using determ_runs_translate_addressM
    by (auto simp: translate_address_def determ_the_result_eq)
qed

lemma TLBTranslate_Instruction_translate_address_eq[simp]:
  assumes "Run_inv (TLBTranslate vaddr Instruction) t paddr regs"
  shows "translate_address (unat vaddr) Fetch t' = Some (unat paddr)"
proof -
  from assms have "Run_inv (translate_addressM (unat vaddr) Fetch) t (unat paddr) regs"
    unfolding translate_addressM_def Run_inv_def
    by (auto simp flip: uint_nat intro: Traces_bindI[of _ t paddr _ "[]", simplified])
  then show ?thesis
    using determ_runs_translate_addressM
    by (auto simp: translate_address_def determ_the_result_eq)
qed

end

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

context CHERI_MIPS_Fixed_Trans
begin

lemma [simp]: "tag_granule ISA = 32" by (auto simp: ISA_def)

lemma address_tag_aligned_plus_iff[simp]:
  fixes addr :: "64 word"
  assumes "int (tag_granule ISA) dvd i" and "0 \<le> i"
  shows "address_tag_aligned ISA (unat (addr + word_of_int i)) \<longleftrightarrow> address_tag_aligned ISA (unat addr)"
  using assms
  unfolding address_tag_aligned_def unat_def mod_eq_0_iff_dvd uint_ge_0[THEN dvd_nat_iff_int_dvd]
  by (auto simp: uint_word_ariths uint_word_of_int mod_add_right_eq dvd_mod_iff dvd_add_left_iff)

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

end

locale CHERI_MIPS_Mem_Instr_Automaton = CHERI_MIPS_Mem_Automaton where is_fetch = False

locale CHERI_MIPS_Mem_Fetch_Automaton = CHERI_MIPS_Mem_Automaton where is_fetch = True

end
