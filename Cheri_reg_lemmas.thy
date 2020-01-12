theory Cheri_reg_lemmas
imports "Sail-CHERI-MIPS.Cheri_lemmas"
begin

termination execute by size_change

definition
  "register_names \<equiv>
    {''InstCount'', ''CID'', ''ErrorEPCC'', ''KDC'', ''KR2C'', ''KR1C'', ''CPLR'', 
     ''CULR'', ''C31'', ''C30'', ''C29'', ''C28'', ''C27'', ''C26'', ''C25'',
     ''C24'', ''C23'', ''C22'', ''C21'', ''C20'', ''C19'', ''C18'', ''C17'',
     ''C16'', ''C15'', ''C14'', ''C13'', ''C12'', ''C11'', ''C10'', ''C09'',
     ''C08'', ''C07'', ''C06'', ''C05'', ''C04'', ''C03'', ''C02'', ''C01'',
     ''DDC'', ''CapCause'', ''NextPCC'', ''DelayedPCC'', ''PCC'', ''KCC'', ''EPCC'',
     ''UART_RVALID'', ''UART_RDATA'', ''UART_WRITTEN'', ''UART_WDATA'', ''GPR'',
     ''LO'', ''HI'', ''DelayedPC'', ''BranchPending'', ''InBranchDelay'',
     ''NextInBranchDelay'', ''CP0Status'', ''CP0ConfigK0'', ''CP0UserLocal'',
     ''CP0HWREna'', ''CP0Count'', ''CP0BadInstrP'', ''CP0BadInstr'',
     ''LastInstrBits'', ''CurrentInstrBits'', ''CP0BadVAddr'', ''CP0LLAddr'',
     ''CP0LLBit'', ''CP0Cause'', ''CP0Compare'', ''TLBEntry63'', ''TLBEntry62'',
     ''TLBEntry61'', ''TLBEntry60'', ''TLBEntry59'', ''TLBEntry58'', ''TLBEntry57'',
     ''TLBEntry56'', ''TLBEntry55'', ''TLBEntry54'', ''TLBEntry53'', ''TLBEntry52'',
     ''TLBEntry51'', ''TLBEntry50'', ''TLBEntry49'', ''TLBEntry48'', ''TLBEntry47'',
     ''TLBEntry46'', ''TLBEntry45'', ''TLBEntry44'', ''TLBEntry43'', ''TLBEntry42'',
     ''TLBEntry41'', ''TLBEntry40'', ''TLBEntry39'', ''TLBEntry38'', ''TLBEntry37'',
     ''TLBEntry36'', ''TLBEntry35'', ''TLBEntry34'', ''TLBEntry33'', ''TLBEntry32'',
     ''TLBEntry31'', ''TLBEntry30'', ''TLBEntry29'', ''TLBEntry28'', ''TLBEntry27'',
     ''TLBEntry26'', ''TLBEntry25'', ''TLBEntry24'', ''TLBEntry23'', ''TLBEntry22'',
     ''TLBEntry21'', ''TLBEntry20'', ''TLBEntry19'', ''TLBEntry18'', ''TLBEntry17'',
     ''TLBEntry16'', ''TLBEntry15'', ''TLBEntry14'', ''TLBEntry13'', ''TLBEntry12'',
     ''TLBEntry11'', ''TLBEntry10'', ''TLBEntry09'', ''TLBEntry08'', ''TLBEntry07'',
     ''TLBEntry06'', ''TLBEntry05'', ''TLBEntry04'', ''TLBEntry03'', ''TLBEntry02'',
     ''TLBEntry01'', ''TLBEntry00'', ''TLBXContext'', ''TLBEntryHi'', ''TLBWired'',
     ''TLBPageMask'', ''TLBContext'', ''TLBEntryLo1'', ''TLBEntryLo0'',
     ''TLBRandom'', ''TLBIndex'', ''TLBProbe'', ''NextPC'', ''PC''}"

lemma register_name_cases:
  obtains "r = ''InstCount''"
  | "r = ''CID''"
  | "r = ''ErrorEPCC''"
  | "r = ''KDC''"
  | "r = ''KR2C''"
  | "r = ''KR1C''"
  | "r = ''CPLR''"
  | "r = ''CULR''"
  | "r = ''C31''"
  | "r = ''C30''"
  | "r = ''C29''"
  | "r = ''C28''"
  | "r = ''C27''"
  | "r = ''C26''"
  | "r = ''C25''"
  | "r = ''C24''"
  | "r = ''C23''"
  | "r = ''C22''"
  | "r = ''C21''"
  | "r = ''C20''"
  | "r = ''C19''"
  | "r = ''C18''"
  | "r = ''C17''"
  | "r = ''C16''"
  | "r = ''C15''"
  | "r = ''C14''"
  | "r = ''C13''"
  | "r = ''C12''"
  | "r = ''C11''"
  | "r = ''C10''"
  | "r = ''C09''"
  | "r = ''C08''"
  | "r = ''C07''"
  | "r = ''C06''"
  | "r = ''C05''"
  | "r = ''C04''"
  | "r = ''C03''"
  | "r = ''C02''"
  | "r = ''C01''"
  | "r = ''DDC''"
  | "r = ''CapCause''"
  | "r = ''NextPCC''"
  | "r = ''DelayedPCC''"
  | "r = ''PCC''"
  | "r = ''KCC''"
  | "r = ''EPCC''"
  | "r = ''UART_RVALID''"
  | "r = ''UART_RDATA''"
  | "r = ''UART_WRITTEN''"
  | "r = ''UART_WDATA''"
  | "r = ''GPR''"
  | "r = ''LO''"
  | "r = ''HI''"
  | "r = ''DelayedPC''"
  | "r = ''BranchPending''"
  | "r = ''InBranchDelay''"
  | "r = ''NextInBranchDelay''"
  | "r = ''CP0Status''"
  | "r = ''CP0ConfigK0''"
  | "r = ''CP0UserLocal''"
  | "r = ''CP0HWREna''"
  | "r = ''CP0Count''"
  | "r = ''CP0BadInstrP''"
  | "r = ''CP0BadInstr''"
  | "r = ''LastInstrBits''"
  | "r = ''CurrentInstrBits''"
  | "r = ''CP0BadVAddr''"
  | "r = ''CP0LLAddr''"
  | "r = ''CP0LLBit''"
  | "r = ''CP0Cause''"
  | "r = ''CP0Compare''"
  | "r = ''TLBEntry63''"
  | "r = ''TLBEntry62''"
  | "r = ''TLBEntry61''"
  | "r = ''TLBEntry60''"
  | "r = ''TLBEntry59''"
  | "r = ''TLBEntry58''"
  | "r = ''TLBEntry57''"
  | "r = ''TLBEntry56''"
  | "r = ''TLBEntry55''"
  | "r = ''TLBEntry54''"
  | "r = ''TLBEntry53''"
  | "r = ''TLBEntry52''"
  | "r = ''TLBEntry51''"
  | "r = ''TLBEntry50''"
  | "r = ''TLBEntry49''"
  | "r = ''TLBEntry48''"
  | "r = ''TLBEntry47''"
  | "r = ''TLBEntry46''"
  | "r = ''TLBEntry45''"
  | "r = ''TLBEntry44''"
  | "r = ''TLBEntry43''"
  | "r = ''TLBEntry42''"
  | "r = ''TLBEntry41''"
  | "r = ''TLBEntry40''"
  | "r = ''TLBEntry39''"
  | "r = ''TLBEntry38''"
  | "r = ''TLBEntry37''"
  | "r = ''TLBEntry36''"
  | "r = ''TLBEntry35''"
  | "r = ''TLBEntry34''"
  | "r = ''TLBEntry33''"
  | "r = ''TLBEntry32''"
  | "r = ''TLBEntry31''"
  | "r = ''TLBEntry30''"
  | "r = ''TLBEntry29''"
  | "r = ''TLBEntry28''"
  | "r = ''TLBEntry27''"
  | "r = ''TLBEntry26''"
  | "r = ''TLBEntry25''"
  | "r = ''TLBEntry24''"
  | "r = ''TLBEntry23''"
  | "r = ''TLBEntry22''"
  | "r = ''TLBEntry21''"
  | "r = ''TLBEntry20''"
  | "r = ''TLBEntry19''"
  | "r = ''TLBEntry18''"
  | "r = ''TLBEntry17''"
  | "r = ''TLBEntry16''"
  | "r = ''TLBEntry15''"
  | "r = ''TLBEntry14''"
  | "r = ''TLBEntry13''"
  | "r = ''TLBEntry12''"
  | "r = ''TLBEntry11''"
  | "r = ''TLBEntry10''"
  | "r = ''TLBEntry09''"
  | "r = ''TLBEntry08''"
  | "r = ''TLBEntry07''"
  | "r = ''TLBEntry06''"
  | "r = ''TLBEntry05''"
  | "r = ''TLBEntry04''"
  | "r = ''TLBEntry03''"
  | "r = ''TLBEntry02''"
  | "r = ''TLBEntry01''"
  | "r = ''TLBEntry00''"
  | "r = ''TLBXContext''"
  | "r = ''TLBEntryHi''"
  | "r = ''TLBWired''"
  | "r = ''TLBPageMask''"
  | "r = ''TLBContext''"
  | "r = ''TLBEntryLo1''"
  | "r = ''TLBEntryLo0''"
  | "r = ''TLBRandom''"
  | "r = ''TLBIndex''"
  | "r = ''TLBProbe''"
  | "r = ''NextPC''"
  | "r = ''PC''"
  | "r \<notin> register_names"
proof cases
  assume "r \<in> register_names"
  then show ?thesis
    unfolding register_names_def
    by (elim insertE) (auto elim: that)
qed

lemma set_regval_non_register_name[simp]:
  "r \<notin> register_names \<Longrightarrow> set_regval r v s = None"
  by (auto simp: register_names_def set_regval_def)

lemma get_regval_non_register_name[simp]:
  "r \<notin> register_names \<Longrightarrow> get_regval r s = None"
  by (auto simp: register_names_def get_regval_def)

lemma set_regval_cases:
  assumes "set_regval r v s = Some s'"
  obtains v' where "r = ''InstCount''" and "int_of_regval v = Some v'" and "s' = s\<lparr>InstCount := v'\<rparr>"
  | v' where "r = ''CID''" and "bitvector_64_dec_of_regval v = Some v'" and "s' = s\<lparr>CID := v'\<rparr>"
  | v' where "r = ''ErrorEPCC''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>ErrorEPCC := v'\<rparr>"
  | v' where "r = ''KDC''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>KDC := v'\<rparr>"
  | v' where "r = ''KR2C''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>KR2C := v'\<rparr>"
  | v' where "r = ''KR1C''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>KR1C := v'\<rparr>"
  | v' where "r = ''CPLR''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>CPLR := v'\<rparr>"
  | v' where "r = ''CULR''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>CULR := v'\<rparr>"
  | v' where "r = ''C31''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C31 := v'\<rparr>"
  | v' where "r = ''C30''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C30 := v'\<rparr>"
  | v' where "r = ''C29''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C29 := v'\<rparr>"
  | v' where "r = ''C28''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C28 := v'\<rparr>"
  | v' where "r = ''C27''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C27 := v'\<rparr>"
  | v' where "r = ''C26''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C26 := v'\<rparr>"
  | v' where "r = ''C25''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C25 := v'\<rparr>"
  | v' where "r = ''C24''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C24 := v'\<rparr>"
  | v' where "r = ''C23''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C23 := v'\<rparr>"
  | v' where "r = ''C22''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C22 := v'\<rparr>"
  | v' where "r = ''C21''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C21 := v'\<rparr>"
  | v' where "r = ''C20''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C20 := v'\<rparr>"
  | v' where "r = ''C19''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C19 := v'\<rparr>"
  | v' where "r = ''C18''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C18 := v'\<rparr>"
  | v' where "r = ''C17''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C17 := v'\<rparr>"
  | v' where "r = ''C16''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C16 := v'\<rparr>"
  | v' where "r = ''C15''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C15 := v'\<rparr>"
  | v' where "r = ''C14''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C14 := v'\<rparr>"
  | v' where "r = ''C13''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C13 := v'\<rparr>"
  | v' where "r = ''C12''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C12 := v'\<rparr>"
  | v' where "r = ''C11''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C11 := v'\<rparr>"
  | v' where "r = ''C10''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C10 := v'\<rparr>"
  | v' where "r = ''C09''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C09 := v'\<rparr>"
  | v' where "r = ''C08''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C08 := v'\<rparr>"
  | v' where "r = ''C07''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C07 := v'\<rparr>"
  | v' where "r = ''C06''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C06 := v'\<rparr>"
  | v' where "r = ''C05''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C05 := v'\<rparr>"
  | v' where "r = ''C04''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C04 := v'\<rparr>"
  | v' where "r = ''C03''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C03 := v'\<rparr>"
  | v' where "r = ''C02''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C02 := v'\<rparr>"
  | v' where "r = ''C01''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>C01 := v'\<rparr>"
  | v' where "r = ''DDC''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>DDC := v'\<rparr>"
  | v' where "r = ''CapCause''" and "CapCauseReg_of_regval v = Some v'" and "s' = s\<lparr>CapCause := v'\<rparr>"
  | v' where "r = ''NextPCC''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>NextPCC := v'\<rparr>"
  | v' where "r = ''DelayedPCC''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>DelayedPCC := v'\<rparr>"
  | v' where "r = ''PCC''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>regstate.PCC := v'\<rparr>"
  | v' where "r = ''KCC''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>regstate.KCC := v'\<rparr>"
  | v' where "r = ''EPCC''" and "Capability_of_regval v = Some v'" and "s' = s\<lparr>EPCC := v'\<rparr>"
  | v' where "r = ''UART_RVALID''" and "bitvector_1_dec_of_regval v = Some v'" and "s' = s\<lparr>UART_RVALID := v'\<rparr>"
  | v' where "r = ''UART_RDATA''" and "bitvector_8_dec_of_regval v = Some v'" and "s' = s\<lparr>UART_RDATA := v'\<rparr>"
  | v' where "r = ''UART_WRITTEN''" and "bitvector_1_dec_of_regval v = Some v'" and "s' = s\<lparr>UART_WRITTEN := v'\<rparr>"
  | v' where "r = ''UART_WDATA''" and "bitvector_8_dec_of_regval v = Some v'" and "s' = s\<lparr>UART_WDATA := v'\<rparr>"
  | v' where "r = ''GPR''" and "vector_of_regval bitvector_64_dec_of_regval v = Some v'" and "s' = s\<lparr>GPR := v'\<rparr>"
  | v' where "r = ''LO''" and "bitvector_64_dec_of_regval v = Some v'" and "s' = s\<lparr>LO := v'\<rparr>"
  | v' where "r = ''HI''" and "bitvector_64_dec_of_regval v = Some v'" and "s' = s\<lparr>HI := v'\<rparr>"
  | v' where "r = ''DelayedPC''" and "bitvector_64_dec_of_regval v = Some v'" and "s' = s\<lparr>DelayedPC := v'\<rparr>"
  | v' where "r = ''BranchPending''" and "bitvector_1_dec_of_regval v = Some v'" and "s' = s\<lparr>BranchPending := v'\<rparr>"
  | v' where "r = ''InBranchDelay''" and "bitvector_1_dec_of_regval v = Some v'" and "s' = s\<lparr>InBranchDelay := v'\<rparr>"
  | v' where "r = ''NextInBranchDelay''" and "bitvector_1_dec_of_regval v = Some v'" and "s' = s\<lparr>NextInBranchDelay := v'\<rparr>"
  | v' where "r = ''CP0Status''" and "StatusReg_of_regval v = Some v'" and "s' = s\<lparr>CP0Status := v'\<rparr>"
  | v' where "r = ''CP0ConfigK0''" and "bitvector_3_dec_of_regval v = Some v'" and "s' = s\<lparr>CP0ConfigK0 := v'\<rparr>"
  | v' where "r = ''CP0UserLocal''" and "bitvector_64_dec_of_regval v = Some v'" and "s' = s\<lparr>CP0UserLocal := v'\<rparr>"
  | v' where "r = ''CP0HWREna''" and "bitvector_32_dec_of_regval v = Some v'" and "s' = s\<lparr>CP0HWREna := v'\<rparr>"
  | v' where "r = ''CP0Count''" and "bitvector_32_dec_of_regval v = Some v'" and "s' = s\<lparr>CP0Count := v'\<rparr>"
  | v' where "r = ''CP0BadInstrP''" and "bitvector_32_dec_of_regval v = Some v'" and "s' = s\<lparr>CP0BadInstrP := v'\<rparr>"
  | v' where "r = ''CP0BadInstr''" and "bitvector_32_dec_of_regval v = Some v'" and "s' = s\<lparr>CP0BadInstr := v'\<rparr>"
  | v' where "r = ''LastInstrBits''" and "bitvector_32_dec_of_regval v = Some v'" and "s' = s\<lparr>LastInstrBits := v'\<rparr>"
  | v' where "r = ''CurrentInstrBits''" and "bitvector_32_dec_of_regval v = Some v'" and "s' = s\<lparr>CurrentInstrBits := v'\<rparr>"
  | v' where "r = ''CP0BadVAddr''" and "bitvector_64_dec_of_regval v = Some v'" and "s' = s\<lparr>CP0BadVAddr := v'\<rparr>"
  | v' where "r = ''CP0LLAddr''" and "bitvector_64_dec_of_regval v = Some v'" and "s' = s\<lparr>CP0LLAddr := v'\<rparr>"
  | v' where "r = ''CP0LLBit''" and "bitvector_1_dec_of_regval v = Some v'" and "s' = s\<lparr>CP0LLBit := v'\<rparr>"
  | v' where "r = ''CP0Cause''" and "CauseReg_of_regval v = Some v'" and "s' = s\<lparr>CP0Cause := v'\<rparr>"
  | v' where "r = ''CP0Compare''" and "bitvector_32_dec_of_regval v = Some v'" and "s' = s\<lparr>CP0Compare := v'\<rparr>"
  | v' where "r = ''TLBEntry63''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry63 := v'\<rparr>"
  | v' where "r = ''TLBEntry62''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry62 := v'\<rparr>"
  | v' where "r = ''TLBEntry61''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry61 := v'\<rparr>"
  | v' where "r = ''TLBEntry60''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry60 := v'\<rparr>"
  | v' where "r = ''TLBEntry59''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry59 := v'\<rparr>"
  | v' where "r = ''TLBEntry58''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry58 := v'\<rparr>"
  | v' where "r = ''TLBEntry57''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry57 := v'\<rparr>"
  | v' where "r = ''TLBEntry56''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry56 := v'\<rparr>"
  | v' where "r = ''TLBEntry55''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry55 := v'\<rparr>"
  | v' where "r = ''TLBEntry54''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry54 := v'\<rparr>"
  | v' where "r = ''TLBEntry53''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry53 := v'\<rparr>"
  | v' where "r = ''TLBEntry52''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry52 := v'\<rparr>"
  | v' where "r = ''TLBEntry51''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry51 := v'\<rparr>"
  | v' where "r = ''TLBEntry50''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry50 := v'\<rparr>"
  | v' where "r = ''TLBEntry49''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry49 := v'\<rparr>"
  | v' where "r = ''TLBEntry48''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry48 := v'\<rparr>"
  | v' where "r = ''TLBEntry47''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry47 := v'\<rparr>"
  | v' where "r = ''TLBEntry46''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry46 := v'\<rparr>"
  | v' where "r = ''TLBEntry45''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry45 := v'\<rparr>"
  | v' where "r = ''TLBEntry44''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry44 := v'\<rparr>"
  | v' where "r = ''TLBEntry43''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry43 := v'\<rparr>"
  | v' where "r = ''TLBEntry42''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry42 := v'\<rparr>"
  | v' where "r = ''TLBEntry41''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry41 := v'\<rparr>"
  | v' where "r = ''TLBEntry40''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry40 := v'\<rparr>"
  | v' where "r = ''TLBEntry39''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry39 := v'\<rparr>"
  | v' where "r = ''TLBEntry38''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry38 := v'\<rparr>"
  | v' where "r = ''TLBEntry37''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry37 := v'\<rparr>"
  | v' where "r = ''TLBEntry36''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry36 := v'\<rparr>"
  | v' where "r = ''TLBEntry35''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry35 := v'\<rparr>"
  | v' where "r = ''TLBEntry34''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry34 := v'\<rparr>"
  | v' where "r = ''TLBEntry33''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry33 := v'\<rparr>"
  | v' where "r = ''TLBEntry32''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry32 := v'\<rparr>"
  | v' where "r = ''TLBEntry31''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry31 := v'\<rparr>"
  | v' where "r = ''TLBEntry30''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry30 := v'\<rparr>"
  | v' where "r = ''TLBEntry29''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry29 := v'\<rparr>"
  | v' where "r = ''TLBEntry28''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry28 := v'\<rparr>"
  | v' where "r = ''TLBEntry27''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry27 := v'\<rparr>"
  | v' where "r = ''TLBEntry26''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry26 := v'\<rparr>"
  | v' where "r = ''TLBEntry25''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry25 := v'\<rparr>"
  | v' where "r = ''TLBEntry24''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry24 := v'\<rparr>"
  | v' where "r = ''TLBEntry23''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry23 := v'\<rparr>"
  | v' where "r = ''TLBEntry22''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry22 := v'\<rparr>"
  | v' where "r = ''TLBEntry21''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry21 := v'\<rparr>"
  | v' where "r = ''TLBEntry20''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry20 := v'\<rparr>"
  | v' where "r = ''TLBEntry19''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry19 := v'\<rparr>"
  | v' where "r = ''TLBEntry18''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry18 := v'\<rparr>"
  | v' where "r = ''TLBEntry17''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry17 := v'\<rparr>"
  | v' where "r = ''TLBEntry16''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry16 := v'\<rparr>"
  | v' where "r = ''TLBEntry15''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry15 := v'\<rparr>"
  | v' where "r = ''TLBEntry14''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry14 := v'\<rparr>"
  | v' where "r = ''TLBEntry13''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry13 := v'\<rparr>"
  | v' where "r = ''TLBEntry12''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry12 := v'\<rparr>"
  | v' where "r = ''TLBEntry11''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry11 := v'\<rparr>"
  | v' where "r = ''TLBEntry10''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry10 := v'\<rparr>"
  | v' where "r = ''TLBEntry09''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry09 := v'\<rparr>"
  | v' where "r = ''TLBEntry08''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry08 := v'\<rparr>"
  | v' where "r = ''TLBEntry07''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry07 := v'\<rparr>"
  | v' where "r = ''TLBEntry06''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry06 := v'\<rparr>"
  | v' where "r = ''TLBEntry05''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry05 := v'\<rparr>"
  | v' where "r = ''TLBEntry04''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry04 := v'\<rparr>"
  | v' where "r = ''TLBEntry03''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry03 := v'\<rparr>"
  | v' where "r = ''TLBEntry02''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry02 := v'\<rparr>"
  | v' where "r = ''TLBEntry01''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry01 := v'\<rparr>"
  | v' where "r = ''TLBEntry00''" and "TLBEntry_of_regval v = Some v'" and "s' = s\<lparr>TLBEntry00 := v'\<rparr>"
  | v' where "r = ''TLBXContext''" and "XContextReg_of_regval v = Some v'" and "s' = s\<lparr>TLBXContext := v'\<rparr>"
  | v' where "r = ''TLBEntryHi''" and "TLBEntryHiReg_of_regval v = Some v'" and "s' = s\<lparr>TLBEntryHi := v'\<rparr>"
  | v' where "r = ''TLBWired''" and "bitvector_6_dec_of_regval v = Some v'" and "s' = s\<lparr>TLBWired := v'\<rparr>"
  | v' where "r = ''TLBPageMask''" and "bitvector_16_dec_of_regval v = Some v'" and "s' = s\<lparr>TLBPageMask := v'\<rparr>"
  | v' where "r = ''TLBContext''" and "ContextReg_of_regval v = Some v'" and "s' = s\<lparr>TLBContext := v'\<rparr>"
  | v' where "r = ''TLBEntryLo1''" and "TLBEntryLoReg_of_regval v = Some v'" and "s' = s\<lparr>TLBEntryLo1 := v'\<rparr>"
  | v' where "r = ''TLBEntryLo0''" and "TLBEntryLoReg_of_regval v = Some v'" and "s' = s\<lparr>TLBEntryLo0 := v'\<rparr>"
  | v' where "r = ''TLBRandom''" and "bitvector_6_dec_of_regval v = Some v'" and "s' = s\<lparr>TLBRandom := v'\<rparr>"
  | v' where "r = ''TLBIndex''" and "bitvector_6_dec_of_regval v = Some v'" and "s' = s\<lparr>TLBIndex := v'\<rparr>"
  | v' where "r = ''TLBProbe''" and "bitvector_1_dec_of_regval v = Some v'" and "s' = s\<lparr>TLBProbe := v'\<rparr>"
  | v' where "r = ''NextPC''" and "bitvector_64_dec_of_regval v = Some v'" and "s' = s\<lparr>NextPC := v'\<rparr>"
  | v' where "r = ''PC''" and "bitvector_64_dec_of_regval v = Some v'" and "s' = s\<lparr>PC := v'\<rparr>"
proof -
  from assms have "r \<in> register_names"
    by (cases "r \<in> register_names") auto
  with assms show thesis
    by (cases r rule: register_name_cases) (auto simp: register_defs elim: that)
qed

lemma get_regval_simps:
  "get_regval ''InstCount'' s = Some (regval_of_int (InstCount s))"
  "get_regval ''CID'' s = Some (regval_of_bitvector_64_dec (CID s))"
  "get_regval ''ErrorEPCC'' s = Some (regval_of_Capability (ErrorEPCC s))"
  "get_regval ''KDC'' s = Some (regval_of_Capability (KDC s))"
  "get_regval ''KR2C'' s = Some (regval_of_Capability (KR2C s))"
  "get_regval ''KR1C'' s = Some (regval_of_Capability (KR1C s))"
  "get_regval ''CPLR'' s = Some (regval_of_Capability (CPLR s))"
  "get_regval ''CULR'' s = Some (regval_of_Capability (CULR s))"
  "get_regval ''C31'' s = Some (regval_of_Capability (C31 s))"
  "get_regval ''C30'' s = Some (regval_of_Capability (C30 s))"
  "get_regval ''C29'' s = Some (regval_of_Capability (C29 s))"
  "get_regval ''C28'' s = Some (regval_of_Capability (C28 s))"
  "get_regval ''C27'' s = Some (regval_of_Capability (C27 s))"
  "get_regval ''C26'' s = Some (regval_of_Capability (C26 s))"
  "get_regval ''C25'' s = Some (regval_of_Capability (C25 s))"
  "get_regval ''C24'' s = Some (regval_of_Capability (C24 s))"
  "get_regval ''C23'' s = Some (regval_of_Capability (C23 s))"
  "get_regval ''C22'' s = Some (regval_of_Capability (C22 s))"
  "get_regval ''C21'' s = Some (regval_of_Capability (C21 s))"
  "get_regval ''C20'' s = Some (regval_of_Capability (C20 s))"
  "get_regval ''C19'' s = Some (regval_of_Capability (C19 s))"
  "get_regval ''C18'' s = Some (regval_of_Capability (C18 s))"
  "get_regval ''C17'' s = Some (regval_of_Capability (C17 s))"
  "get_regval ''C16'' s = Some (regval_of_Capability (C16 s))"
  "get_regval ''C15'' s = Some (regval_of_Capability (C15 s))"
  "get_regval ''C14'' s = Some (regval_of_Capability (C14 s))"
  "get_regval ''C13'' s = Some (regval_of_Capability (C13 s))"
  "get_regval ''C12'' s = Some (regval_of_Capability (C12 s))"
  "get_regval ''C11'' s = Some (regval_of_Capability (C11 s))"
  "get_regval ''C10'' s = Some (regval_of_Capability (C10 s))"
  "get_regval ''C09'' s = Some (regval_of_Capability (C09 s))"
  "get_regval ''C08'' s = Some (regval_of_Capability (C08 s))"
  "get_regval ''C07'' s = Some (regval_of_Capability (C07 s))"
  "get_regval ''C06'' s = Some (regval_of_Capability (C06 s))"
  "get_regval ''C05'' s = Some (regval_of_Capability (C05 s))"
  "get_regval ''C04'' s = Some (regval_of_Capability (C04 s))"
  "get_regval ''C03'' s = Some (regval_of_Capability (C03 s))"
  "get_regval ''C02'' s = Some (regval_of_Capability (C02 s))"
  "get_regval ''C01'' s = Some (regval_of_Capability (C01 s))"
  "get_regval ''DDC'' s = Some (regval_of_Capability (DDC s))"
  "get_regval ''CapCause'' s = Some (regval_of_CapCauseReg (CapCause s))"
  "get_regval ''NextPCC'' s = Some (regval_of_Capability (NextPCC s))"
  "get_regval ''DelayedPCC'' s = Some (regval_of_Capability (DelayedPCC s))"
  "get_regval ''PCC'' s = Some (regval_of_Capability (regstate.PCC s))"
  "get_regval ''KCC'' s = Some (regval_of_Capability (regstate.KCC s))"
  "get_regval ''EPCC'' s = Some (regval_of_Capability (EPCC s))"
  "get_regval ''UART_RVALID'' s = Some (regval_of_bitvector_1_dec (UART_RVALID s))"
  "get_regval ''UART_RDATA'' s = Some (regval_of_bitvector_8_dec (UART_RDATA s))"
  "get_regval ''UART_WRITTEN'' s = Some (regval_of_bitvector_1_dec (UART_WRITTEN s))"
  "get_regval ''UART_WDATA'' s = Some (regval_of_bitvector_8_dec (UART_WDATA s))"
  "get_regval ''GPR'' s = Some (regval_of_vector regval_of_bitvector_64_dec (GPR s))"
  "get_regval ''LO'' s = Some (regval_of_bitvector_64_dec (LO s))"
  "get_regval ''HI'' s = Some (regval_of_bitvector_64_dec (HI s))"
  "get_regval ''DelayedPC'' s = Some (regval_of_bitvector_64_dec (DelayedPC s))"
  "get_regval ''BranchPending'' s = Some (regval_of_bitvector_1_dec (BranchPending s))"
  "get_regval ''InBranchDelay'' s = Some (regval_of_bitvector_1_dec (InBranchDelay s))"
  "get_regval ''NextInBranchDelay'' s = Some (regval_of_bitvector_1_dec (NextInBranchDelay s))"
  "get_regval ''CP0Status'' s = Some (regval_of_StatusReg (CP0Status s))"
  "get_regval ''CP0ConfigK0'' s = Some (regval_of_bitvector_3_dec (CP0ConfigK0 s))"
  "get_regval ''CP0UserLocal'' s = Some (regval_of_bitvector_64_dec (CP0UserLocal s))"
  "get_regval ''CP0HWREna'' s = Some (regval_of_bitvector_32_dec (CP0HWREna s))"
  "get_regval ''CP0Count'' s = Some (regval_of_bitvector_32_dec (CP0Count s))"
  "get_regval ''CP0BadInstrP'' s = Some (regval_of_bitvector_32_dec (CP0BadInstrP s))"
  "get_regval ''CP0BadInstr'' s = Some (regval_of_bitvector_32_dec (CP0BadInstr s))"
  "get_regval ''LastInstrBits'' s = Some (regval_of_bitvector_32_dec (LastInstrBits s))"
  "get_regval ''CurrentInstrBits'' s = Some (regval_of_bitvector_32_dec (CurrentInstrBits s))"
  "get_regval ''CP0BadVAddr'' s = Some (regval_of_bitvector_64_dec (CP0BadVAddr s))"
  "get_regval ''CP0LLAddr'' s = Some (regval_of_bitvector_64_dec (CP0LLAddr s))"
  "get_regval ''CP0LLBit'' s = Some (regval_of_bitvector_1_dec (CP0LLBit s))"
  "get_regval ''CP0Cause'' s = Some (regval_of_CauseReg (CP0Cause s))"
  "get_regval ''CP0Compare'' s = Some (regval_of_bitvector_32_dec (CP0Compare s))"
  "get_regval ''TLBEntry63'' s = Some (regval_of_TLBEntry (TLBEntry63 s))"
  "get_regval ''TLBEntry62'' s = Some (regval_of_TLBEntry (TLBEntry62 s))"
  "get_regval ''TLBEntry61'' s = Some (regval_of_TLBEntry (TLBEntry61 s))"
  "get_regval ''TLBEntry60'' s = Some (regval_of_TLBEntry (TLBEntry60 s))"
  "get_regval ''TLBEntry59'' s = Some (regval_of_TLBEntry (TLBEntry59 s))"
  "get_regval ''TLBEntry58'' s = Some (regval_of_TLBEntry (TLBEntry58 s))"
  "get_regval ''TLBEntry57'' s = Some (regval_of_TLBEntry (TLBEntry57 s))"
  "get_regval ''TLBEntry56'' s = Some (regval_of_TLBEntry (TLBEntry56 s))"
  "get_regval ''TLBEntry55'' s = Some (regval_of_TLBEntry (TLBEntry55 s))"
  "get_regval ''TLBEntry54'' s = Some (regval_of_TLBEntry (TLBEntry54 s))"
  "get_regval ''TLBEntry53'' s = Some (regval_of_TLBEntry (TLBEntry53 s))"
  "get_regval ''TLBEntry52'' s = Some (regval_of_TLBEntry (TLBEntry52 s))"
  "get_regval ''TLBEntry51'' s = Some (regval_of_TLBEntry (TLBEntry51 s))"
  "get_regval ''TLBEntry50'' s = Some (regval_of_TLBEntry (TLBEntry50 s))"
  "get_regval ''TLBEntry49'' s = Some (regval_of_TLBEntry (TLBEntry49 s))"
  "get_regval ''TLBEntry48'' s = Some (regval_of_TLBEntry (TLBEntry48 s))"
  "get_regval ''TLBEntry47'' s = Some (regval_of_TLBEntry (TLBEntry47 s))"
  "get_regval ''TLBEntry46'' s = Some (regval_of_TLBEntry (TLBEntry46 s))"
  "get_regval ''TLBEntry45'' s = Some (regval_of_TLBEntry (TLBEntry45 s))"
  "get_regval ''TLBEntry44'' s = Some (regval_of_TLBEntry (TLBEntry44 s))"
  "get_regval ''TLBEntry43'' s = Some (regval_of_TLBEntry (TLBEntry43 s))"
  "get_regval ''TLBEntry42'' s = Some (regval_of_TLBEntry (TLBEntry42 s))"
  "get_regval ''TLBEntry41'' s = Some (regval_of_TLBEntry (TLBEntry41 s))"
  "get_regval ''TLBEntry40'' s = Some (regval_of_TLBEntry (TLBEntry40 s))"
  "get_regval ''TLBEntry39'' s = Some (regval_of_TLBEntry (TLBEntry39 s))"
  "get_regval ''TLBEntry38'' s = Some (regval_of_TLBEntry (TLBEntry38 s))"
  "get_regval ''TLBEntry37'' s = Some (regval_of_TLBEntry (TLBEntry37 s))"
  "get_regval ''TLBEntry36'' s = Some (regval_of_TLBEntry (TLBEntry36 s))"
  "get_regval ''TLBEntry35'' s = Some (regval_of_TLBEntry (TLBEntry35 s))"
  "get_regval ''TLBEntry34'' s = Some (regval_of_TLBEntry (TLBEntry34 s))"
  "get_regval ''TLBEntry33'' s = Some (regval_of_TLBEntry (TLBEntry33 s))"
  "get_regval ''TLBEntry32'' s = Some (regval_of_TLBEntry (TLBEntry32 s))"
  "get_regval ''TLBEntry31'' s = Some (regval_of_TLBEntry (TLBEntry31 s))"
  "get_regval ''TLBEntry30'' s = Some (regval_of_TLBEntry (TLBEntry30 s))"
  "get_regval ''TLBEntry29'' s = Some (regval_of_TLBEntry (TLBEntry29 s))"
  "get_regval ''TLBEntry28'' s = Some (regval_of_TLBEntry (TLBEntry28 s))"
  "get_regval ''TLBEntry27'' s = Some (regval_of_TLBEntry (TLBEntry27 s))"
  "get_regval ''TLBEntry26'' s = Some (regval_of_TLBEntry (TLBEntry26 s))"
  "get_regval ''TLBEntry25'' s = Some (regval_of_TLBEntry (TLBEntry25 s))"
  "get_regval ''TLBEntry24'' s = Some (regval_of_TLBEntry (TLBEntry24 s))"
  "get_regval ''TLBEntry23'' s = Some (regval_of_TLBEntry (TLBEntry23 s))"
  "get_regval ''TLBEntry22'' s = Some (regval_of_TLBEntry (TLBEntry22 s))"
  "get_regval ''TLBEntry21'' s = Some (regval_of_TLBEntry (TLBEntry21 s))"
  "get_regval ''TLBEntry20'' s = Some (regval_of_TLBEntry (TLBEntry20 s))"
  "get_regval ''TLBEntry19'' s = Some (regval_of_TLBEntry (TLBEntry19 s))"
  "get_regval ''TLBEntry18'' s = Some (regval_of_TLBEntry (TLBEntry18 s))"
  "get_regval ''TLBEntry17'' s = Some (regval_of_TLBEntry (TLBEntry17 s))"
  "get_regval ''TLBEntry16'' s = Some (regval_of_TLBEntry (TLBEntry16 s))"
  "get_regval ''TLBEntry15'' s = Some (regval_of_TLBEntry (TLBEntry15 s))"
  "get_regval ''TLBEntry14'' s = Some (regval_of_TLBEntry (TLBEntry14 s))"
  "get_regval ''TLBEntry13'' s = Some (regval_of_TLBEntry (TLBEntry13 s))"
  "get_regval ''TLBEntry12'' s = Some (regval_of_TLBEntry (TLBEntry12 s))"
  "get_regval ''TLBEntry11'' s = Some (regval_of_TLBEntry (TLBEntry11 s))"
  "get_regval ''TLBEntry10'' s = Some (regval_of_TLBEntry (TLBEntry10 s))"
  "get_regval ''TLBEntry09'' s = Some (regval_of_TLBEntry (TLBEntry09 s))"
  "get_regval ''TLBEntry08'' s = Some (regval_of_TLBEntry (TLBEntry08 s))"
  "get_regval ''TLBEntry07'' s = Some (regval_of_TLBEntry (TLBEntry07 s))"
  "get_regval ''TLBEntry06'' s = Some (regval_of_TLBEntry (TLBEntry06 s))"
  "get_regval ''TLBEntry05'' s = Some (regval_of_TLBEntry (TLBEntry05 s))"
  "get_regval ''TLBEntry04'' s = Some (regval_of_TLBEntry (TLBEntry04 s))"
  "get_regval ''TLBEntry03'' s = Some (regval_of_TLBEntry (TLBEntry03 s))"
  "get_regval ''TLBEntry02'' s = Some (regval_of_TLBEntry (TLBEntry02 s))"
  "get_regval ''TLBEntry01'' s = Some (regval_of_TLBEntry (TLBEntry01 s))"
  "get_regval ''TLBEntry00'' s = Some (regval_of_TLBEntry (TLBEntry00 s))"
  "get_regval ''TLBXContext'' s = Some (regval_of_XContextReg (TLBXContext s))"
  "get_regval ''TLBEntryHi'' s = Some (regval_of_TLBEntryHiReg (TLBEntryHi s))"
  "get_regval ''TLBWired'' s = Some (regval_of_bitvector_6_dec (TLBWired s))"
  "get_regval ''TLBPageMask'' s = Some (regval_of_bitvector_16_dec (TLBPageMask s))"
  "get_regval ''TLBContext'' s = Some (regval_of_ContextReg (TLBContext s))"
  "get_regval ''TLBEntryLo1'' s = Some (regval_of_TLBEntryLoReg (TLBEntryLo1 s))"
  "get_regval ''TLBEntryLo0'' s = Some (regval_of_TLBEntryLoReg (TLBEntryLo0 s))"
  "get_regval ''TLBRandom'' s = Some (regval_of_bitvector_6_dec (TLBRandom s))"
  "get_regval ''TLBIndex'' s = Some (regval_of_bitvector_6_dec (TLBIndex s))"
  "get_regval ''TLBProbe'' s = Some (regval_of_bitvector_1_dec (TLBProbe s))"
  "get_regval ''NextPC'' s = Some (regval_of_bitvector_64_dec (NextPC s))"
  "get_regval ''PC'' s = Some (regval_of_bitvector_64_dec (PC s))"
  by (auto simp: register_defs)

lemma get_ignore_set_regval:
  assumes s': "set_regval r v s = Some s'" and r': "r' \<noteq> r"
  shows "get_regval r' s' = get_regval r' s"
  using assms
  apply (elim set_regval_cases)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  subgoal by (cases r' rule: register_name_cases; simp add: get_regval_simps)
  done

fun_cases of_regval_SomeE:
  "int_of_regval v = Some v'"
  "bit_of_regval v = Some v'"
  "bitvector_1_dec_of_regval v = Some v'"
  "bitvector_3_dec_of_regval v = Some v'"
  "bitvector_6_dec_of_regval v = Some v'"
  "bitvector_8_dec_of_regval v = Some v'"
  "bitvector_16_dec_of_regval v = Some v'"
  "bitvector_32_dec_of_regval v = Some v'"
  "bitvector_64_dec_of_regval v = Some v'"
  "Capability_of_regval v = Some v'"
  "CapCauseReg_of_regval v = Some v'"
  "CauseReg_of_regval v = Some v'"
  "ContextReg_of_regval v = Some v'"
  "XContextReg_of_regval v = Some v'"
  "StatusReg_of_regval v = Some v'"
  "TLBEntry_of_regval v = Some v'"
  "TLBEntryHiReg_of_regval v = Some v'"
  "TLBEntryLoReg_of_regval v = Some v'"

lemmas regval_of_defs =
  regval_of_int_def regval_of_bitvector_64_dec_def regval_of_Capability_def regval_of_CapCauseReg_def
  regval_of_CauseReg_def regval_of_ContextReg_def regval_of_XContextReg_def regval_of_StatusReg_def
  regval_of_TLBEntry_def regval_of_TLBEntryHiReg_def regval_of_TLBEntryLoReg_def
  regval_of_bit_def regval_of_bitvector_1_dec_def regval_of_bitvector_3_dec_def
  regval_of_bitvector_6_dec_def regval_of_bitvector_8_dec_def regval_of_bitvector_16_dec_def
  regval_of_bitvector_32_dec_def regval_of_vector_def

lemma vector_of_regval_SomeE:
  assumes *: "vector_of_regval of_rv v = Some xs" and **: "\<And>v v'. of_rv v = Some v' \<Longrightarrow> rv_of v' = v"
  obtains "v = Regval_vector (map rv_of xs)"
proof -
  from * obtain vs where "v = Regval_vector vs" and ***: "map of_rv vs = map Some xs"
    by (auto simp: vector_of_regval_def split: register_value.splits)
  moreover have "map rv_of xs = vs"
    using ** ***
    by (induction xs arbitrary: vs) auto
  ultimately
  show ?thesis
    using that
    by blast
qed

lemma get_absorb_set_regval:
  assumes "set_regval r v s = Some s'"
  shows "get_regval r s' = Some v"
  using assms
  by (elim set_regval_cases)
     (auto simp: get_regval_simps regval_of_defs elim: of_regval_SomeE vector_of_regval_SomeE)

end
