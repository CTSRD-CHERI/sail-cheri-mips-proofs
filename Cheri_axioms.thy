chapter \<open>Generated by Lem from \<open>cheri_axioms.lem\<close>.\<close>

theory "Cheri_axioms" 

imports
  Main
  "LEM.Lem_pervasives_extra"
  "Sail.Sail2_values"
  "Sail.Sail2_prompt_monad"
  "Sail.Sail2_operators"
  "Capabilities"

begin 

\<comment> \<open>\<open>open import Pervasives_extra\<close>\<close>
\<comment> \<open>\<open>open import Sail2_values\<close>\<close>
\<comment> \<open>\<open>open import Sail2_prompt_monad\<close>\<close>
\<comment> \<open>\<open>open import Sail2_operators\<close>\<close>
\<comment> \<open>\<open>open import Capabilities\<close>\<close>

datatype acctype = Load | Store | Fetch

record( 'cap, 'regval, 'instr, 'e) isa =
  
 instr_sem ::" 'instr \<Rightarrow> ('regval, unit, 'e) monad " 

     instr_fetch ::" ('regval, 'instr, 'e) monad " 

     tag_granule ::" nat " 

     PCC ::" register_name \<comment> \<open>\<open> trace 'regval -> \<close>\<close> set " 

     KCC ::" register_name \<comment> \<open>\<open> trace 'regval -> \<close>\<close> set " 

     IDC ::" register_name \<comment> \<open>\<open> trace 'regval -> \<close>\<close> set " 

     caps_of_regval ::" 'regval \<Rightarrow> 'cap set " 

     invokes_caps ::" 'instr \<Rightarrow> 'regval trace \<Rightarrow> bool " 

     instr_raises_ex ::" 'instr \<Rightarrow> 'regval trace \<Rightarrow> bool " 

     fetch_raises_ex ::" 'regval trace \<Rightarrow> bool " 

     exception_targets ::" 'regval set \<Rightarrow> 'cap set " 

     privileged_regs ::" register_name \<comment> \<open>\<open> trace 'regval -> \<close>\<close> set " 

     translation_tables ::" 'regval trace \<Rightarrow> nat set " 

     translate_address ::" nat \<Rightarrow> acctype \<Rightarrow> 'regval trace \<Rightarrow>  nat option " 


definition writes_mem_val_at_idx  :: " nat \<Rightarrow>('a event)list \<Rightarrow>(nat*nat*(memory_byte)list*bitU)option "  where 
     " writes_mem_val_at_idx i t = ( Option.bind (index t i) writes_mem_val )" 
  for  i  :: " nat " 
  and  t  :: "('a event)list "

definition writes_mem_cap_at_idx  :: " 'a Capability_class \<Rightarrow> nat \<Rightarrow>('b event)list \<Rightarrow>(nat*nat*'a)option "  where 
     " writes_mem_cap_at_idx dict_Capabilities_Capability_a i t = ( Option.bind (index t i) 
  (writes_mem_cap dict_Capabilities_Capability_a) )" 
  for  dict_Capabilities_Capability_a  :: " 'a Capability_class " 
  and  i  :: " nat " 
  and  t  :: "('b event)list "

definition writes_to_reg_at_idx  :: " nat \<Rightarrow>('a event)list \<Rightarrow>(string)option "  where 
     " writes_to_reg_at_idx i t = ( Option.bind (index t i) writes_to_reg )" 
  for  i  :: " nat " 
  and  t  :: "('a event)list "

definition writes_reg_caps_at_idx  :: " 'd Capability_class \<Rightarrow>('d,'c,'b,'a)isa \<Rightarrow> nat \<Rightarrow>('c event)list \<Rightarrow> 'd set "  where 
     " writes_reg_caps_at_idx dict_Capabilities_Capability_d ISA i t = ( case_option {} (writes_reg_caps 
  dict_Capabilities_Capability_d(caps_of_regval   ISA)) (index t i))" 
  for  dict_Capabilities_Capability_d  :: " 'd Capability_class " 
  and  ISA  :: "('d,'c,'b,'a)isa " 
  and  i  :: " nat " 
  and  t  :: "('c event)list "

definition reads_mem_val_at_idx  :: " nat \<Rightarrow>('a event)list \<Rightarrow>(nat*nat*(memory_byte)list*bitU)option "  where 
     " reads_mem_val_at_idx i t = ( Option.bind (index t i) reads_mem_val )" 
  for  i  :: " nat " 
  and  t  :: "('a event)list "

definition reads_mem_cap_at_idx  :: " 'a Capability_class \<Rightarrow> nat \<Rightarrow>('b event)list \<Rightarrow>(nat*nat*'a)option "  where 
     " reads_mem_cap_at_idx dict_Capabilities_Capability_a i t = ( Option.bind (index t i) 
  (reads_mem_cap dict_Capabilities_Capability_a) )" 
  for  dict_Capabilities_Capability_a  :: " 'a Capability_class " 
  and  i  :: " nat " 
  and  t  :: "('b event)list "

definition reads_from_reg_at_idx  :: " nat \<Rightarrow>('a event)list \<Rightarrow>(string)option "  where 
     " reads_from_reg_at_idx i t = ( Option.bind (index t i) reads_from_reg )" 
  for  i  :: " nat " 
  and  t  :: "('a event)list "

definition reads_reg_caps_at_idx  :: " 'd Capability_class \<Rightarrow>('d,'c,'b,'a)isa \<Rightarrow> nat \<Rightarrow>('c event)list \<Rightarrow> 'd set "  where 
     " reads_reg_caps_at_idx dict_Capabilities_Capability_d ISA i t = ( case_option {} (reads_reg_caps 
  dict_Capabilities_Capability_d(caps_of_regval   ISA)) (index t i))" 
  for  dict_Capabilities_Capability_d  :: " 'd Capability_class " 
  and  ISA  :: "('d,'c,'b,'a)isa " 
  and  i  :: " nat " 
  and  t  :: "('c event)list "


\<comment> \<open>\<open>val address_range : nat -> nat -> list nat\<close>\<close>
definition address_range  :: " nat \<Rightarrow> nat \<Rightarrow>(nat)list "  where 
     " address_range start len = ( genlist (\<lambda> n .  start + n) len )" 
  for  start  :: " nat " 
  and  len  :: " nat "


\<comment> \<open>\<open>val address_tag_aligned : forall 'cap 'regval 'instr 'e.
  isa 'cap 'regval 'instr 'e -> nat -> bool\<close>\<close>
definition address_tag_aligned  :: "('cap,'regval,'instr,'e)isa \<Rightarrow> nat \<Rightarrow> bool "  where 
     " address_tag_aligned ISA addr = ( ((addr mod(tag_granule   ISA)) =( 0 :: nat)))" 
  for  ISA  :: "('cap,'regval,'instr,'e)isa " 
  and  addr  :: " nat "


\<comment> \<open>\<open>val cap_reg_written_before_idx : forall 'cap 'regval 'instr 'e. Capability 'cap, Eq 'cap, SetType 'cap =>
  isa 'cap 'regval 'instr 'e -> nat -> register_name -> trace 'regval -> bool\<close>\<close>
definition cap_reg_written_before_idx  :: " 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow> nat \<Rightarrow> string \<Rightarrow>('regval event)list \<Rightarrow> bool "  where 
     " cap_reg_written_before_idx dict_Capabilities_Capability_cap ISA i r t = ( ((\<exists> j.  (j < i) \<and> ((writes_to_reg_at_idx j t = Some r) \<and> \<not> (writes_reg_caps_at_idx 
  dict_Capabilities_Capability_cap ISA j t = {})))))" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  ISA  :: "('cap,'regval,'instr,'e)isa " 
  and  i  :: " nat " 
  and  r  :: " string " 
  and  t  :: "('regval event)list "


\<comment> \<open>\<open>val system_access_permitted_before_idx : forall 'cap 'regval 'instr 'e. Capability 'cap, SetType 'cap, Eq 'cap =>
  isa 'cap 'regval 'instr 'e -> nat -> trace 'regval -> bool\<close>\<close>
definition system_access_permitted_before_idx  :: " 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow> nat \<Rightarrow>('regval event)list \<Rightarrow> bool "  where 
     " system_access_permitted_before_idx dict_Capabilities_Capability_cap ISA i t = (
  ((\<exists> j. \<exists> r. \<exists> c. 
     (j < i) \<and>
     ((reads_from_reg_at_idx j t = Some r) \<and>
     (\<not> (cap_reg_written_before_idx 
  dict_Capabilities_Capability_cap ISA j r t) \<and>
     ((c \<in> (reads_reg_caps_at_idx 
  dict_Capabilities_Capability_cap ISA j t)) \<and>
     ((r \<in>(PCC   ISA)) \<and> ((r \<notin>(privileged_regs   ISA)) \<and>
     ((is_tagged_method   dict_Capabilities_Capability_cap) c \<and> (\<not> ((is_sealed_method   dict_Capabilities_Capability_cap) c) \<and>(permit_system_access  
     ((get_perms_method   dict_Capabilities_Capability_cap) c))))))))))))" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  ISA  :: "('cap,'regval,'instr,'e)isa " 
  and  i  :: " nat " 
  and  t  :: "('regval event)list "


\<comment> \<open>\<open>val permits_cap_load : forall 'cap. Capability 'cap => 'cap -> nat -> nat -> bool\<close>\<close>
definition permits_cap_load  :: " 'cap Capability_class \<Rightarrow> 'cap \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool "  where 
     " permits_cap_load dict_Capabilities_Capability_cap c vaddr sz = (
  ((is_tagged_method   dict_Capabilities_Capability_cap) c \<and> (\<not> ((is_sealed_method   dict_Capabilities_Capability_cap) c) \<and>
   ((List.set (address_range vaddr sz) \<subseteq> (
  (get_mem_region_method   dict_Capabilities_Capability_cap) c)) \<and>(permit_load_capability  
   ((get_perms_method   dict_Capabilities_Capability_cap) c))))))" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  c  :: " 'cap " 
  and  vaddr  :: " nat " 
  and  sz  :: " nat "


\<comment> \<open>\<open>val available_caps : forall 'cap 'regval 'instr 'e. Capability 'cap, Eq 'cap, SetType 'cap =>
  isa 'cap 'regval 'instr 'e -> nat -> trace 'regval -> set 'cap\<close>\<close>
fun  available_caps  :: " 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow> nat \<Rightarrow>('regval event)list \<Rightarrow> 'cap set "  where 
     " available_caps dict_Capabilities_Capability_cap ISA 0 t = ( {} )" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  ISA  :: "('cap,'regval,'instr,'e)isa " 
  and  t  :: "('regval event)list "
|" available_caps dict_Capabilities_Capability_cap ISA ((Suc i)) t = ( 
  (let caps_of = (\<lambda> e . 
                  ((case  reads_mem_cap dict_Capabilities_Capability_cap e of
                         Some (_, _, c) => {c}
                     | None => {}
                   )) \<union>
                    ((case  reads_from_reg e of
                           Some r =>
                     if (\<not>
                           (cap_reg_written_before_idx
                              dict_Capabilities_Capability_cap ISA i 
                            r t) \<and>
                           (system_access_permitted_before_idx
                              dict_Capabilities_Capability_cap ISA i 
                            t \<or> \<not> (r \<in> (privileged_regs   ISA))))
                     then
                       reads_reg_caps dict_Capabilities_Capability_cap
                         (caps_of_regval   ISA) e else {}
                       | None => {}
                     ))) in
  (let new_caps = (case_option {} caps_of (index t i)) in
  (available_caps dict_Capabilities_Capability_cap ISA i t) \<union> new_caps)) )" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  ISA  :: "('cap,'regval,'instr,'e)isa " 
  and  i  :: " nat " 
  and  t  :: "('regval event)list "


\<comment> \<open>\<open>val read_reg_axiom : forall 'cap 'regval 'instr 'e. Capability 'cap, SetType 'cap, Eq 'cap, Eq 'regval =>
  isa 'cap 'regval 'instr 'e -> bool -> trace 'regval -> bool\<close>\<close>
definition read_reg_axiom  :: " 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow> bool \<Rightarrow>('regval event)list \<Rightarrow> bool "  where 
     " read_reg_axiom dict_Capabilities_Capability_cap ISA has_ex t = (
  ((\<forall> i. \<forall> r. \<forall> v. 
     ((index t i = Some (E_read_reg r v)) \<and> (r \<in>(privileged_regs   ISA)))
     \<longrightarrow>
     (system_access_permitted_before_idx 
  dict_Capabilities_Capability_cap ISA i t \<or>
      (has_ex \<comment> \<open>\<open>&& r IN ISA.KCC\<close>\<close>)))))" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  ISA  :: "('cap,'regval,'instr,'e)isa " 
  and  has_ex  :: " bool " 
  and  t  :: "('regval event)list "


\<comment> \<open>\<open>val store_cap_mem_axiom : forall 'cap 'regval 'instr 'e. Capability 'cap, SetType 'cap, Eq 'cap =>
  isa 'cap 'regval 'instr 'e -> trace 'regval -> bool\<close>\<close>
definition store_cap_mem_axiom  :: " 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow>('regval event)list \<Rightarrow> bool "  where 
     " store_cap_mem_axiom dict_Capabilities_Capability_cap ISA t = (
  ((\<forall> i. \<forall> c. \<forall> addr. \<forall> sz. 
     (writes_mem_cap_at_idx 
  dict_Capabilities_Capability_cap i t = Some (addr, sz, c))
     \<longrightarrow>
     (cap_derivable dict_Capabilities_Capability_cap (available_caps dict_Capabilities_Capability_cap ISA i t) c))))" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  ISA  :: "('cap,'regval,'instr,'e)isa " 
  and  t  :: "('regval event)list "


\<comment> \<open>\<open>val store_cap_reg_axiom : forall 'cap 'regval 'instr 'e. Capability 'cap, SetType 'cap, SetType 'regval, Eq 'cap, Eq 'regval =>
  isa 'cap 'regval 'instr 'e -> bool -> bool -> trace 'regval -> bool\<close>\<close>
definition store_cap_reg_axiom  :: " 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>('regval event)list \<Rightarrow> bool "  where 
     " store_cap_reg_axiom dict_Capabilities_Capability_cap ISA has_ex invokes_caps1 t = (
  ((\<forall> i. \<forall> c. \<forall> r. 
     ((writes_to_reg_at_idx i t = Some r) \<and> (c \<in> (writes_reg_caps_at_idx 
  dict_Capabilities_Capability_cap ISA i t)))
     \<longrightarrow>
     (cap_derivable dict_Capabilities_Capability_cap (available_caps dict_Capabilities_Capability_cap ISA i t) c \<or>
     ((has_ex \<and>
      (
	 (\<comment> \<open>\<open>exists r' v' j.
         j < i &&
	 index t j = Just (E_read_reg r' v') &&\<close>\<close>c \<in>(exception_targets   ISA) {v' .( \<exists> r'.  \<exists> j.  (j < i) \<and> ((index t j = Some (E_read_reg r' v')) \<and> (r' \<in>(KCC   ISA))))}) \<and>
         (
         \<comment> \<open>\<open>reads_from_reg_at_idx j t = Just r' &&
         c' IN (reads_reg_caps_at_idx ISA j t) &&
         leq_cap c c' &&
         r' IN (ISA.KCC \<open>take j t\<close>) &&\<close>\<close>r \<in> ((PCC   ISA) \<comment> \<open>\<open>take i t\<close>\<close>)))) \<or>
     ((\<exists> cc. \<exists> cd0. 
        invokes_caps1 \<and>
        (cap_derivable 
  dict_Capabilities_Capability_cap (available_caps dict_Capabilities_Capability_cap ISA i t) cc \<and>
        (cap_derivable 
  dict_Capabilities_Capability_cap (available_caps dict_Capabilities_Capability_cap ISA i t) cd0 \<and>
        (invokable dict_Capabilities_Capability_cap cc cd0 \<and>
        ((leq_cap dict_Capabilities_Capability_cap c (unseal dict_Capabilities_Capability_cap cc True) \<and> (r \<in>(PCC   ISA))) \<or>
         (leq_cap dict_Capabilities_Capability_cap c (unseal dict_Capabilities_Capability_cap cd0 True) \<and> (r \<in>(IDC   ISA))))))))))))))" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  ISA  :: "('cap,'regval,'instr,'e)isa " 
  and  has_ex  :: " bool " 
  and  invokes_caps1  :: " bool " 
  and  t  :: "('regval event)list "


\<comment> \<open>\<open>val load_mem_axiom : forall 'cap 'regval 'instr 'e. Capability 'cap, SetType 'cap, Eq 'cap =>
  isa 'cap 'regval 'instr 'e -> bool -> trace 'regval -> bool\<close>\<close>
definition load_mem_axiom  :: " 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow> bool \<Rightarrow>('regval event)list \<Rightarrow> bool "  where 
     " load_mem_axiom dict_Capabilities_Capability_cap ISA is_fetch t = (
  ((\<forall> i. \<forall> paddr. \<forall> sz. \<forall> v. \<forall> tag. 
     ((reads_mem_val_at_idx i t = Some (paddr, sz, v, tag)) \<and>
      \<not> (paddr \<in> ((translation_tables   ISA) (List.take i t))))
     \<longrightarrow>
     ((\<exists> c'. \<exists> vaddr. 
        cap_derivable 
  dict_Capabilities_Capability_cap (available_caps dict_Capabilities_Capability_cap ISA i t) c' \<and> (
  (is_tagged_method   dict_Capabilities_Capability_cap) c' \<and> (\<not> ((is_sealed_method   dict_Capabilities_Capability_cap) c') \<and>
        (((translate_address   ISA) vaddr (if is_fetch then Fetch else Load) (List.take i t) = Some paddr) \<and>
        ((List.set (address_range vaddr sz) \<subseteq> (
  (get_mem_region_method   dict_Capabilities_Capability_cap) c')) \<and>
        ((if is_fetch \<and> (tag = B0) then(permit_execute   (
  (get_perms_method   dict_Capabilities_Capability_cap) c')) else(permit_load   (
  (get_perms_method   dict_Capabilities_Capability_cap) c'))) \<and>
        ((tag \<noteq> B0) \<longrightarrow> ((permit_load_capability  (
  (get_perms_method   dict_Capabilities_Capability_cap) c')) \<and> ((sz =(tag_granule   ISA)) \<and> address_tag_aligned ISA paddr)))))))))))))" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  ISA  :: "('cap,'regval,'instr,'e)isa " 
  and  is_fetch  :: " bool " 
  and  t  :: "('regval event)list "


\<comment> \<open>\<open>val mem_val_is_cap : forall 'cap 'regval 'instr 'e. Capability 'cap, SetType 'cap, Eq 'cap =>
  isa 'cap 'regval 'instr 'e -> list memory_byte -> bitU -> bool\<close>\<close>
definition mem_val_is_cap  :: " 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow>(memory_byte)list \<Rightarrow> bitU \<Rightarrow> bool "  where 
     " mem_val_is_cap dict_Capabilities_Capability_cap _ v t = ( ((\<exists> c. 
  (cap_of_mem_bytes_method   dict_Capabilities_Capability_cap) v t = Some (c :: 'cap))))" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  v  :: "(memory_byte)list " 
  and  t  :: " bitU "


\<comment> \<open>\<open>val mem_val_is_local_cap : forall 'cap 'regval 'instr 'e. Capability 'cap, SetType 'cap, Eq 'cap =>
  isa 'cap 'regval 'instr 'e -> list memory_byte -> bitU -> bool\<close>\<close>
definition mem_val_is_local_cap  :: " 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow>(memory_byte)list \<Rightarrow> bitU \<Rightarrow> bool "  where 
     " mem_val_is_local_cap dict_Capabilities_Capability_cap _ v t = ( ((\<exists> c.  (
  (cap_of_mem_bytes_method   dict_Capabilities_Capability_cap) v t = Some (c :: 'cap)) \<and> \<not> (
  (get_global_method   dict_Capabilities_Capability_cap) c))))" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  v  :: "(memory_byte)list " 
  and  t  :: " bitU "


\<comment> \<open>\<open>val store_tag_axiom : forall 'cap 'regval 'instr 'e. Capability 'cap, SetType 'cap, Eq 'cap =>
  isa 'cap 'regval 'instr 'e -> trace 'regval -> bool\<close>\<close>
definition store_tag_axiom  :: " 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow>('regval event)list \<Rightarrow> bool "  where 
     " store_tag_axiom dict_Capabilities_Capability_cap ISA t = (
  ((\<forall> i. \<forall> paddr. \<forall> sz. \<forall> v. \<forall> tag. 
     (writes_mem_val_at_idx i t = Some (paddr, sz, v, tag))
     \<longrightarrow>
     ((List.length v = sz) \<and>
      (((tag = B0) \<or> (tag = B1)) \<and>
      ((tag = B1) \<longrightarrow> (address_tag_aligned ISA paddr \<and> (sz =(tag_granule   ISA)))))))))" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  ISA  :: "('cap,'regval,'instr,'e)isa " 
  and  t  :: "('regval event)list "


\<comment> \<open>\<open>val store_mem_axiom : forall 'cap 'regval 'instr 'e. Capability 'cap, SetType 'cap, Eq 'cap =>
  isa 'cap 'regval 'instr 'e -> trace 'regval -> bool\<close>\<close>
definition store_mem_axiom  :: " 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow>('regval event)list \<Rightarrow> bool "  where 
     " store_mem_axiom dict_Capabilities_Capability_cap ISA t = (
  ((\<forall> i. \<forall> paddr. \<forall> sz. \<forall> v. \<forall> tag. 
     ((writes_mem_val_at_idx i t = Some (paddr, sz, v, tag)) \<and>
      \<not> (paddr \<in> ((translation_tables   ISA) (List.take i t))))
     \<longrightarrow>
     ((\<exists> c'. \<exists> vaddr. 
        cap_derivable 
  dict_Capabilities_Capability_cap (available_caps dict_Capabilities_Capability_cap ISA i t) c' \<and> (
  (is_tagged_method   dict_Capabilities_Capability_cap) c' \<and> (\<not> ((is_sealed_method   dict_Capabilities_Capability_cap) c') \<and>
        (((translate_address   ISA) vaddr Store (List.take i t) = Some paddr) \<and>
        ((List.set (address_range vaddr sz) \<subseteq> (
  (get_mem_region_method   dict_Capabilities_Capability_cap) c')) \<and>
        ((if (mem_val_is_cap 
  dict_Capabilities_Capability_cap ISA v tag \<and> (tag = B1))
         then(permit_store_capability   (
  (get_perms_method   dict_Capabilities_Capability_cap) c'))
         else(permit_store   (
  (get_perms_method   dict_Capabilities_Capability_cap) c'))) \<and>
        ((mem_val_is_local_cap 
  dict_Capabilities_Capability_cap ISA v tag \<and> (tag = B1)) \<longrightarrow>(permit_store_local_capability   (
  (get_perms_method   dict_Capabilities_Capability_cap) c')))))))))))))" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  ISA  :: "('cap,'regval,'instr,'e)isa " 
  and  t  :: "('regval event)list "


\<comment> \<open>\<open>val cheri_axioms : forall 'cap 'regval 'instr 'e. Capability 'cap, SetType 'cap, SetType 'regval, Eq 'cap, Eq 'regval =>
  isa 'cap 'regval 'instr 'e -> bool -> bool -> bool -> trace 'regval -> bool\<close>\<close>
definition cheri_axioms  :: " 'cap Capability_class \<Rightarrow>('cap,'regval,'instr,'e)isa \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>('regval event)list \<Rightarrow> bool "  where 
     " cheri_axioms dict_Capabilities_Capability_cap ISA is_fetch has_ex invokes_caps1 t = (
  store_cap_mem_axiom 
  dict_Capabilities_Capability_cap ISA t \<and>
  (store_cap_reg_axiom 
  dict_Capabilities_Capability_cap ISA has_ex invokes_caps1 t \<and>
  (read_reg_axiom dict_Capabilities_Capability_cap ISA has_ex t \<and>
  (load_mem_axiom dict_Capabilities_Capability_cap ISA is_fetch t \<and>
  (store_tag_axiom dict_Capabilities_Capability_cap ISA t \<and>
  store_mem_axiom dict_Capabilities_Capability_cap ISA t)))))" 
  for  dict_Capabilities_Capability_cap  :: " 'cap Capability_class " 
  and  ISA  :: "('cap,'regval,'instr,'e)isa " 
  and  is_fetch  :: " bool " 
  and  has_ex  :: " bool " 
  and  invokes_caps1  :: " bool " 
  and  t  :: "('regval event)list "

end
