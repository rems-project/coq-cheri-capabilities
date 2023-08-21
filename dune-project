(lang dune 3.8)
(using coq 0.8)

(generate_opam_files false)

(name coq-cheri-capabilities)

(source (github rems-project/coq-cheri-capabilities))
(license BSD-3-clause)
(authors "Ricardo Almeida" "Vadim Zaliva")
(maintainers "ricardo.almeida@ed.ac.uk")

(package
 (name coq-cheri-capabilities)
 (synopsis "Coq interface for CHERI capabilities")
 (description "\| An abstract interface for CHERI capabilities 
              "\| and a concrete one for the Morello architecture.
 )
 (depends 
 	(coq (< 8.17.0))
  coq-sail
  coq-ext-lib
  ; coq-struct-tact
  (coq-stdpp-unstable (= dev.2023-02-17.2.2d8ccea3))
 )
)

