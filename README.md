# CHERI-MIPS capability monotonicity proof

This repository contains a proof of capability monotonicity of the CHERI-MIPS
architecture specified in Sail.  The proof uses the version of the architecture
in commit `4d8457c1` of the
[sail-cheri-mips](https://github.com/CTSRD-CHERI/sail-cheri-mips) repository.

## Proof structure

The proof is structured as follows:

  * The files `capabilities.lem` and `cheri_axioms.lem` contain an ISA
    abstraction and local properties that each instruction of the architecture
    has to satisfy to guarantee capability monotonicity.  These files are
    translated by the Lem tool into Isabelle theories with corresponding names.

  * The `Properties.thy` file contains the capability monotonicity proof above
    this abstract model.

  * The `CHERI_MIPS_Instantiation.thy` file contains the instantiation of the
    abstract model for the Sail-CHERI-MIPS specification.

  * The files `CHERI_MIPS_Reg_Axioms.thy` and `CHERI_MIPS_Mem_Axioms.thy`
    contain proofs that all instructions of CHERI-MIPS satisfy the required
    local properties.  This is supported by lemmas and proof infrastructure in
    a number of files, e.g. `CHERI_MIPS_Gen_Lemmas.thy` with generated register
    footprint lemmas about the functions in the specification, or
    `Recognising_Automata.thy` with proof tools for verifying the
    instruction-local properties.

  * The `CHERI_MIPS_Properties.thy` file contains the instantiation of the
    capability monotonicity theorem for CHERI-MIPS.

Parts of the proof about the bulk of the architecture were originally
generated automatically using the `gen_lemmas.ml` tool written in OCaml,
although it is not advisable to re-run this tool any more, as the proofs have
since been edited manually.  The tool used the `fp.json` file with information
about the call graph of functions in the architecture, the types of functions
and the registers they access;  this file was generated by a patched version of
Sail (commit `02e33d24`).

## Running the proofs

The proof requires [Isabelle 2019](https://isabelle.in.tum.de/website-Isabelle2019/index.html).
The proof has last been tested with the following versions of dependencies:
  * [sail-cheri-mips](https://github.com/CTSRD-CHERI/sail-cheri-mips) commit `4d8457c1`
  * [sail](https://github.com/rems-project/sail) commit `63343363`
  * [lem](https://github.com/rems-project/lem) commit `a839114`
  * [Isabelle 2019](https://isabelle.in.tum.de/website-Isabelle2019/index.html)

Isabelle needs to be told about the paths to the Lem and Sail libraries as well
as the `sail-cheri-mips/cheri` directory with the Isabelle definitions
generated from the Sail specification.  This can be done either on the command
line with `-d <path>` arguments to Isabelle, or by adding the paths to the
`ROOTS` file in Isabelle's user home directory (`~/.isabelle/Isabelle2019` on
Linux).  The proof can then be inspected interactively by running (in this
directory)
```
isabelle jedit -d . -l Sail-CHERI-MIPS CHERI_MIPS_Properties.thy
```
or checked non-interactively using
```
isabelle build -D .
```
The proof takes around 5 minutes to process on an Intel W-2145 CPU @ 3.70GHz,
in addition to 5 minutes to process the CHERI-MIPS specification.
