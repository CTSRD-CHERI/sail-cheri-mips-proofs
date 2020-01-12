theory CHERI_MIPS_Properties
imports CHERI_MIPS_Reg_Axioms CHERI_MIPS_Mem_Axioms Properties
begin

context CHERI_MIPS_Reg_Automaton
begin

lemma runs_no_reg_writes_to_incrementCP0Count[runs_no_reg_writes_toI]:
  assumes "{''TLBRandom'', ''CP0Count'', ''CP0Cause''} \<inter> Rs = {}"
  shows "runs_no_reg_writes_to Rs (incrementCP0Count u)"
  using assms
  unfolding incrementCP0Count_def bind_assoc Let_def
  by (no_reg_writes_toI simp: TLBRandom_ref_def CP0Count_ref_def CP0Cause_ref_def)

lemma TranslatePC_establishes_inv:
  assumes "Run (TranslatePC vaddr) t a" and "reads_regs_from {''PCC''} t s"
  shows "invariant s"
  using assms
  unfolding TranslatePC_def bind_assoc Let_def
  by (auto elim!: Run_bindE Run_read_regE split: if_splits
           simp: regstate_simp register_defs regval_of_Capability_def)

lemma not_PCC_regs[simp]:
  "name PC_ref \<noteq> ''PCC''"
  "name InBranchDelay_ref \<noteq> ''PCC''"
  "name NextPC_ref \<noteq> ''PCC''"
  "name NextInBranchDelay_ref \<noteq> ''PCC''"
  "name BranchPending_ref \<noteq> ''PCC''"
  "name CurrentInstrBits_ref \<noteq> ''PCC''"
  "name LastInstrBits_ref \<noteq> ''PCC''"
  "name UART_WRITTEN_ref \<noteq> ''PCC''"
  "name InstCount_ref \<noteq> ''PCC''"
  by (auto simp: register_defs)

lemma fetch_establishes_inv:
  assumes "Run (fetch u) t a" and "reads_regs_from {''PCC''} t s"
  shows "invariant (the (updates_regs {''PCC''} t s))"
  using assms
  unfolding fetch_def bind_assoc Let_def
  by (auto elim!: Run_bindE simp: regstate_simp dest: TranslatePC_establishes_inv)

lemma instr_fetch_establishes_inv:
  assumes "Run (instr_fetch ISA) t a" and "reads_regs_from {''PCC''} t s"
  shows "invariant (the (updates_regs {''PCC''} t s))"
  using assms
  by (auto simp: ISA_def elim!: Run_bindE split: option.splits dest: fetch_establishes_inv)

end

lemma (in CHERI_MIPS_Mem_Automaton) preserves_invariant_instr_fetch[preserves_invariantI]:
  shows "runs_preserve_invariant (instr_fetch ISA)"
  by (auto simp: ISA_def intro!: preserves_invariantI; simp add: runs_preserve_invariant_def)

context CHERI_MIPS_Fixed_Trans
begin

definition "state_assms t reg_s mem_s \<equiv> reads_regs_from trans_regs t mem_s \<and> reads_regs_from {''PCC''} t reg_s \<and> trans_inv mem_s"
definition "fetch_assms t \<equiv> (\<exists>reg_s mem_s. state_assms t reg_s mem_s)"
definition "instr_assms t \<equiv> (\<exists>reg_s mem_s. state_assms t reg_s mem_s \<and> CHERI_MIPS_Reg_Automaton.invariant reg_s)"

sublocale CHERI_ISA where CC = CC and ISA = ISA and fetch_assms = fetch_assms and instr_assms = instr_assms
proof
  fix t instr
  interpret Reg_Axioms: CHERI_MIPS_Reg_Automaton
    where ex_traces = "instr_raises_ex ISA instr t"
      and invocation_traces = "invokes_caps ISA instr t"
      and translate_address = translate_address .
  interpret Mem_Axioms: CHERI_MIPS_Mem_Instr_Automaton trans_regstate "instr_raises_ex ISA instr t"
    by unfold_locales
  assume t: "hasTrace t (instr_sem ISA instr)" and "instr_assms t"
  then obtain reg_s mem_s
    where reg_assms: "reads_regs_from {''PCC''} t reg_s" "Reg_Axioms.invariant reg_s"
      and mem_assms: "reads_regs_from trans_regs t mem_s" "trans_inv mem_s"
    by (auto simp: instr_assms_def state_assms_def)
  show "cheri_axioms CC ISA False (instr_raises_ex ISA instr t)
        (invokes_caps ISA instr t) t"
    unfolding cheri_axioms_def
    using Reg_Axioms.hasTrace_instr_reg_axioms[OF t reg_assms]
    using Mem_Axioms.hasTrace_instr_mem_axioms[OF t mem_assms]
    by auto
next
  fix t
  interpret Fetch_Axioms: CHERI_MIPS_Reg_Fetch_Automaton trans_regstate "fetch_raises_ex ISA t" ..
  assume t: "hasTrace t (instr_fetch ISA)" and "fetch_assms t"
  then obtain regs where *: "reads_regs_from trans_regs t regs" "trans_inv regs"
    by (auto simp: fetch_assms_def state_assms_def)
  then show "cheri_axioms CC ISA True (fetch_raises_ex ISA t) False t"
    unfolding cheri_axioms_def
    using Fetch_Axioms.hasTrace_fetch_reg_axioms[OF t *]
    using Fetch_Axioms.Mem_Automaton.hasTrace_fetch_mem_axioms[OF t *]
    by auto
next
  fix t t' instr
  interpret Mem_Axioms: CHERI_MIPS_Mem_Instr_Automaton trans_regstate by unfold_locales
  assume *: "instr_assms (t @ t')" and **: "Run (instr_sem ISA instr) t ()"
  have "trans_inv (the (updates_regs trans_regs t mem_s))"
    if "trans_inv mem_s" and "reads_regs_from trans_regs t mem_s" for mem_s
    using Mem_Axioms.preserves_invariant_execute[of instr] that **
    by (elim runs_preserve_invariantE[where t = t and s = mem_s and a = "()"])
       (auto simp: instr_assms_def state_assms_def regstate_simp)
  with * show "instr_assms t \<and> fetch_assms t'"
    by (auto simp: instr_assms_def fetch_assms_def state_assms_def regstate_simp)
next
  fix t t' instr
  interpret Reg_Axioms: CHERI_MIPS_Reg_Automaton
    where ex_traces = "fetch_raises_ex ISA t"
      and invocation_traces = False
      and translate_address = translate_address .
  interpret Mem_Axioms: CHERI_MIPS_Mem_Automaton trans_regstate by unfold_locales
  assume *: "fetch_assms (t @ t')" and **: "Run (instr_fetch ISA) t instr"
  have ***: "trans_inv (the (updates_regs trans_regs t regs))"
    if "reads_regs_from trans_regs t regs" and "trans_inv regs" for regs
    using ** that
    by (elim runs_preserve_invariantE[OF Mem_Axioms.preserves_invariant_instr_fetch]) auto
  show "fetch_assms t \<and> instr_assms t'"
    using * **
    unfolding fetch_assms_def instr_assms_def state_assms_def
    by (fastforce simp: regstate_simp elim!: Run_bindE split: option.splits
                  dest: Reg_Axioms.fetch_establishes_inv ***)
qed

lemma translate_address_tag_aligned:
  fixes s :: "regstate sequential_state"
  assumes "translate_address vaddr acctype s = Some paddr"
  shows "address_tag_aligned ISA paddr = address_tag_aligned ISA vaddr"
    (is "?aligned paddr = ?aligned vaddr")
proof -
  interpret CHERI_MIPS_Mem_Automaton ..
  have [simp]: "?aligned (unat (word_of_int (int vaddr) :: 64 word)) \<longleftrightarrow> ?aligned vaddr"
    unfolding address_tag_aligned_def
    by (auto simp: unat_def uint_word_of_int nat_mod_distrib nat_power_eq mod_mod_cancel)
  from assms obtain t regs where "Run_inv (translate_addressM vaddr acctype) t paddr regs"
    by (auto simp: translate_address_def determ_the_result_eq[OF determ_runs_translate_addressM]
             split: if_splits)
  then show ?thesis
    by (auto simp: translate_addressM_def elim!: Run_inv_bindE intro: preserves_invariantI)
qed

sublocale CHERI_ISA_State where CC = CC and ISA = ISA
  and read_regval = get_regval and write_regval = set_regval
  and fetch_assms = fetch_assms and instr_assms = instr_assms
  and s_translation_tables = "\<lambda>_. {}" and s_translate_address = translate_address
  using get_absorb_set_regval get_ignore_set_regval translate_address_tag_aligned
  by unfold_locales (auto simp: ISA_def translate_address_def)

thm reachable_caps_instrs_trace_intradomain_monotonicity

lemma regstate_put_mem_bytes_eq[simp]:
  "regstate (put_mem_bytes addr sz v tag s) = regstate s"
  by (auto simp: put_mem_bytes_def Let_def)

lemma set_regval_Some_Some:
  assumes "set_regval r v s = Some s1"
  obtains s1' where "set_regval r v s' = Some s1'"
  using assms
  by (elim set_regval_cases of_regval_SomeE) (auto simp: register_defs)

lemma get_regval_eq_reads_regs_imp:
  assumes "\<forall>r \<in> Rs. get_regval r s = get_regval r s'"
    and "reads_regs_from Rs t s'"
  shows "reads_regs_from Rs t s"
proof (use assms in \<open>induction t arbitrary: s s'\<close>)
  case (Cons e t)
  then show ?case
  proof (cases e)
    fix r v
    assume e: "e = E_write_reg r v"
    with Cons show ?thesis
    proof cases
      assume r: "r \<in> Rs"
      with Cons.prems e obtain s1' where s1': "set_regval r v s' = Some s1'" and *: "reads_regs_from Rs t s1'"
        by (auto split: if_splits option.splits)
      moreover obtain s1 where s1: "set_regval r v s = Some s1"
        by (rule set_regval_Some_Some[OF s1'])
      have **: "\<forall>r' \<in> Rs. get_regval r' s1 = get_regval r' s1'"
      proof
        fix r'
        assume "r' \<in> Rs"
        then show "get_regval r' s1 = get_regval r' s1'"
          using s1 s1' Cons.prems
          by (cases "r' = r") (auto simp: get_absorb_set_regval get_ignore_set_regval)
      qed
      show ?thesis
        using e r s1 Cons.IH[OF ** *]
        by auto
    qed auto
  qed (auto split: if_splits option.splits)
qed auto

lemma set_other_reg_reads_regs_iff:
  assumes "set_regval r v s = Some s'" and "r \<notin> Rs"
  shows "reads_regs_from Rs t s' = reads_regs_from Rs t s"
proof -
  have "\<forall>r' \<in> Rs. get_regval r' s = get_regval r' s'"
    using assms get_ignore_set_regval
    by fastforce
  then show ?thesis
    using get_regval_eq_reads_regs_imp[of Rs s s' t]
    using get_regval_eq_reads_regs_imp[of Rs s' s t]
    by auto
qed

lemma reads_regs_from_mono:
  assumes "reads_regs_from Rs t s"
    and "Rs' \<subseteq> Rs"
  shows "reads_regs_from Rs' t s"
  using assms
  by (induction Rs t s rule: reads_regs_from.induct)
     (auto split: if_splits option.splits dest: set_other_reg_reads_regs_iff[where Rs = Rs'])

(*lemma s_run_trace_reads_regs_from:
  assumes "s_run_trace t s = Some s'"
  shows "reads_regs_from Rs t (regstate s)"
proof (use assms in \<open>induction t arbitrary: s\<close>)
  case (Cons e t)
  then obtain s'' where "s_emit_event e s = Some s''" and t: "s_run_trace t s'' = Some s'"
    by (auto split: Option.bind_splits)
  moreover from Cons.IH[OF t] have "reads_regs_from Rs t (regstate s'')" .
  ultimately show ?case
    by (cases e) (auto split: Option.bind_splits if_splits simp: set_other_reg_reads_regs_iff)
qed auto*)

lemma s_invariant_trivial:
  assumes t: "s_allows_trace t s" and f: "\<And>s'. f s' = f s"
  shows "s_invariant f t s"
proof -
  have f: "f s1 = f s2" for s1 s2
    using f[of s1] f[of s2, symmetric]
    by auto
  obtain s' where "s_run_trace t s = Some s'"
    using t
    by blast
  then show "s_invariant f t s"
    by (induction "(get_regval, set_regval)" t s rule: runTraceS.induct)
       (auto split: Option.bind_splits intro: f)
qed

lemma hasTrace_fetch_execute_reachable_caps_mono:
  assumes t: "hasTrace t (fetch_execute_loop ISA n)"
    and s: "s_run_trace t s = Some s'"
    and regs: "reads_regs_from trans_regs t trans_regstate"
    and no_ex: "\<not> instrs_raise_ex ISA n t"
    and no_ccall: "\<not> instrs_invoke_caps ISA n t"
  shows "reachable_caps s' \<subseteq> reachable_caps s"
proof (intro reachable_caps_instrs_trace_intradomain_monotonicity[OF t _ s no_ex no_ccall])
  have "state_assms t trans_regstate trans_regstate"
    using regs
    by (auto simp: state_assms_def trans_regs_def elim: reads_regs_from_mono)
  then show "fetch_assms t"
    by (auto simp: fetch_assms_def)
  show "s_invariant (\<lambda>s' addr load. local.translate_address addr load s') t s"
    and "s_invariant (\<lambda>_. {}) t s"
    and "s_invariant_holds no_caps_in_translation_tables t s"
    using s
    by (auto simp: translate_address_def no_caps_in_translation_tables_def intro: s_invariant_trivial)
qed

end

end
