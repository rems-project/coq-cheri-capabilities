(lang dune 3.7)
(using coq 0.7)

(name coq-cheri-capabilities)

(generate_opam_files)


(source (github rems-project/coq-cheri-capabilities))
(license BSD-3-clause)
(authors "Ricardo Almeida" "Vadim Zaliva")
(maintainers "ricardo.almeida@ed.ac.uk")

(package
 (name coq-cheri-capabilities)
 (synopsis "My first Dune package!")
 (description "\| This is my first attempt at creating
              "\| a project with Dune.
 )
 (depends 
 	(coq (< 8.17.0))
  coq-sail
  coq-ext-lib
  coq-struct-tact
  (coq-stdpp-unstable (= dev.2023-02-17.2.2d8ccea3))
 )
)

