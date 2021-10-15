(lang dune 2.5)
(name coq-katamaran)
(using coq 0.2)

(license BSD-2-Clause)
(maintainers "Steven Keuchel <steven.keuchel@vub.be>")
(authors "Dominique Devriese" "Georgy Lukyanov" "Sander Huyghebaert" "Steven Keuchel")
(source (github katamaran-project/katamaran))
(homepage "https://katamaran-project.github.io/")

(version 0.1.0)
(package
 (name coq-katamaran)
 (synopsis "Separation logic-based verification of instruction sets")
 (description "Katamaran is a semi-automated separation logic verifier for
the Sail specification language. It works on an embedded
version of Sail called μSail and verifies separation
logic-based contracts of functions by generating (succinct)
first-order verification conditions. It further comes with a
complete model based on the Iris separation logic
framework.")
 (tags
  ("keyword:program verification"
   "keyword:separation logic"
   "keyword:symbolic execution"
   "keyword:instruction sets"
   "category:Computer Science/Semantics and Compilation/Semantics"
   "logpath:Katamaran"))
 (depends
  (coq                   (or (and (>= 8.12) (< 8.14~)) (= dev)))
  (coq-bbv               (or (and (>= 1.2)  (< 1.3~)) (= dev)))
  (coq-equations         (or (and (>= 1.2)  (< 1.4~)) (= dev)))
  (coq-iris              (= 3.4.0))
  (coq-iris-string-ident (= 0.1.0))
  (coq-stdpp             (= 1.5.0))))
