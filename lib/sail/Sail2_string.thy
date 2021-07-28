chapter \<open>Generated by Lem from \<open>../../src/gen_lib/sail2_string.lem\<close>.\<close>

theory "Sail2_string" 

imports
  Main
  "LEM.Lem_pervasives"
  "LEM.Lem_list"
  "LEM.Lem_list_extra"
  "LEM.Lem_string"
  "LEM.Lem_string_extra"
  "Sail2_operators"
  "Sail2_values"

begin 

\<comment> \<open>\<open>open import Pervasives\<close>\<close>
\<comment> \<open>\<open>open import List\<close>\<close>
\<comment> \<open>\<open>open import List_extra\<close>\<close>
\<comment> \<open>\<open>open import String\<close>\<close>
\<comment> \<open>\<open>open import String_extra\<close>\<close>

\<comment> \<open>\<open>open import Sail2_operators\<close>\<close>
\<comment> \<open>\<open>open import Sail2_values\<close>\<close>

\<comment> \<open>\<open>val string_sub : string -> ii -> ii -> string\<close>\<close>
definition string_sub  :: \<open> string \<Rightarrow> int \<Rightarrow> int \<Rightarrow> string \<close>  where 
     \<open> string_sub str start len = (
  (List.take (nat (abs ( len))) (List.drop (nat (abs ( start))) ( str))))\<close> 
  for  str  :: " string " 
  and  start  :: " int " 
  and  len  :: " int "


\<comment> \<open>\<open>val string_startswith : string -> string -> bool\<close>\<close>
definition string_startswith  :: \<open> string \<Rightarrow> string \<Rightarrow> bool \<close>  where 
     \<open> string_startswith str1 str2 = (
  (let prefix = (string_sub str1(( 0 :: int)) (int (List.length str2))) in
  (prefix = str2)))\<close> 
  for  str1  :: " string " 
  and  str2  :: " string "


\<comment> \<open>\<open>val string_drop : string -> ii -> string\<close>\<close>
definition string_drop  :: \<open> string \<Rightarrow> int \<Rightarrow> string \<close>  where 
     \<open> string_drop str n = (
  (List.drop (nat (abs ( n))) ( str)))\<close> 
  for  str  :: " string " 
  and  n  :: " int "


\<comment> \<open>\<open>val string_take : string -> ii -> string\<close>\<close>
definition string_take  :: \<open> string \<Rightarrow> int \<Rightarrow> string \<close>  where 
     \<open> string_take str n = (
  (List.take (nat (abs ( n))) ( str)))\<close> 
  for  str  :: " string " 
  and  n  :: " int "


\<comment> \<open>\<open>val string_length : string -> ii\<close>\<close>
definition string_length  :: \<open> string \<Rightarrow> int \<close>  where 
     \<open> string_length s = ( int (List.length s))\<close> 
  for  s  :: " string "


definition string_append  :: \<open> string \<Rightarrow> string \<Rightarrow> string \<close>  where 
     \<open> string_append = ( (@))\<close>


\<comment> \<open>\<open>**********************************************
 * Begin stuff that should be in Lem Num_extra *
 **********************************************\<close>\<close>

\<comment> \<open>\<open>val maybeIntegerOfString : string -> maybe integer\<close>\<close>
definition maybeIntegerOfString  :: \<open> string \<Rightarrow>(int)option \<close>  where 
     \<open> maybeIntegerOfString _ = ( None )\<close>


\<comment> \<open>\<open>**********************************************
 * end stuff that should be in Lem Num_extra   *
 **********************************************\<close>\<close>

function (sequential,domintros)  maybe_int_of_prefix  :: \<open> string \<Rightarrow>(int*int)option \<close>  where 
     \<open> maybe_int_of_prefix s = ( 
  if(s = ('''')) then None else
    ((let len = (string_length s) in
     (case  maybeIntegerOfString s of
           Some n => Some (n, len)
       | None => maybe_int_of_prefix
                   (string_sub s (( 0 :: int)) (len - ( 1 :: int)))
     ))) )\<close> 
  for  s  :: " string " 
by pat_completeness auto


definition maybe_int_of_string  :: \<open> string \<Rightarrow>(int)option \<close>  where 
     \<open> maybe_int_of_string = ( maybeIntegerOfString )\<close>


\<comment> \<open>\<open>val n_leading_spaces : string -> ii\<close>\<close>
function (sequential,domintros)  n_leading_spaces  :: \<open> string \<Rightarrow> int \<close>  where 
     \<open> n_leading_spaces s = (
  (let len = (string_length s) in
  if len =( 0 :: int) then( 0 :: int) else
    if len =( 1 :: int) then  
  if(s = ('' '')) then ( 1 :: int) else ( 0 :: int)
    else
           \<comment> \<open>\<open> Isabelle generation for pattern matching on characters
              is currently broken, so use an if-expression \<close>\<close>
           if nth s(( 0 :: nat)) = (CHR '' '')
           then( 1 :: int) + (n_leading_spaces (string_sub s(( 1 :: int)) (len -( 1 :: int))))
           else( 0 :: int)))\<close> 
  for  s  :: " string " 
by pat_completeness auto

  \<comment> \<open>\<open> end \<close>\<close>

definition opt_spc_matches_prefix  :: \<open> string \<Rightarrow>(unit*int)option \<close>  where 
     \<open> opt_spc_matches_prefix s = (
  Some (() , n_leading_spaces s))\<close> 
  for  s  :: " string "


definition spc_matches_prefix  :: \<open> string \<Rightarrow>(unit*int)option \<close>  where 
     \<open> spc_matches_prefix s = (
  (let n = (n_leading_spaces s) in
  \<comment> \<open>\<open> match n with \<close>\<close>
\<comment> \<open>\<open> | 0 -> Nothing \<close>\<close>
  if n =( 0 :: int) then None else
  \<comment> \<open>\<open> | n -> \<close>\<close> Some (() , n)))\<close> 
  for  s  :: " string "

  \<comment> \<open>\<open> end \<close>\<close>

\<comment> \<open>\<open> Python:
f = """let hex_bits_{0}_matches_prefix s =
  match maybe_int_of_prefix s with
  | Nothing -> Nothing
  | Just (n, len) ->
    if 0 <= n && n < (2 ** {0}) then
      Just ((of_int {0} n, len))
    else
      Nothing
  end
"""

for i in list(range(1, 34)) + [48, 64]:
  print(f.format(i))
\<close>\<close>
definition hex_bits_1_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_1_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 1 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 1 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_2_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_2_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 2 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 2 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_3_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_3_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 3 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 3 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_4_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_4_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 4 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 4 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_5_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_5_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 5 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 5 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_6_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_6_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 6 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 6 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_7_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_7_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 7 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 7 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_8_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_8_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 8 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 8 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_9_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_9_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 9 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 9 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_10_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_10_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 10 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 10 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_11_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_11_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 11 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 11 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_12_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_12_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 12 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 12 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_13_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_13_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 13 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 13 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_14_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_14_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 14 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 14 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_15_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_15_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 15 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 15 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_16_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_16_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 16 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 16 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_17_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_17_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 17 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 17 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_18_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_18_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 18 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 18 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_19_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_19_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 19 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 19 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_20_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_20_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 20 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 20 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_21_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_21_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 21 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 21 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_22_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_22_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 22 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 22 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_23_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_23_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 23 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 23 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_24_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_24_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 24 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 24 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_25_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_25_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 25 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 25 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_26_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_26_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 26 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 26 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_27_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_27_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 27 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 27 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_28_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_28_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 28 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 28 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_29_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_29_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 29 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 29 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_30_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_30_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 30 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 30 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_31_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_31_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 31 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 31 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_32_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_32_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 32 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 32 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_33_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_33_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 33 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 33 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_48_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_48_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 48 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 48 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "


definition hex_bits_64_matches_prefix  :: \<open> 'a Bitvector_class \<Rightarrow> string \<Rightarrow>('a*int)option \<close>  where 
     \<open> hex_bits_64_matches_prefix dict_Sail2_values_Bitvector_a s = (
  (case  maybe_int_of_prefix s of
    None => None
  | Some (n, len) =>
    if(( 0 :: int) \<le> n) \<and> (n < (( 2 :: int) ^( 64 :: nat))) then
      Some (((of_int_method   dict_Sail2_values_Bitvector_a)(( 64 :: int)) n, len))
    else
      None
  ))\<close> 
  for  dict_Sail2_values_Bitvector_a  :: " 'a Bitvector_class " 
  and  s  :: " string "

end
