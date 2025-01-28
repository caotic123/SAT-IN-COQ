# SAT-IN-COQ

[Work in Progress]

*Read the PDF document for more details*

This repository formalize the SAT problem components including propositional format, proof format, also we formalize famous algorithms employed by SAT SOLVERS.

We may attack also SMT in the future.


# Installing

You need the [Coq](https://coq.inria.fr/download) proof assistant to check the proofs, you also need [Coq hammer](https://coqhammer.github.io/).

After you can check by using your terminal: coqc sat.v

# Running the code

You only need ocaml to run the extracted code (no need of external library):

Type in your terminal:

ocamlc sat sat.v
sat <file_in_format_dimacs>

Or type run.sh to run every benchmark file.

