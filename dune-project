(lang dune 3.3)
(name coq-katamaran)
(using coq 0.4)

(license BSD-2-Clause)
(maintainers "Steven Keuchel <steven.keuchel@vub.be>")
(authors "Dominique Devriese" "Georgy Lukyanov" "Sander Huyghebaert" "Steven Keuchel")
(source (github katamaran-project/katamaran))
(homepage "https://katamaran-project.github.io/")

(version 0.2.0)
(package
 (name coq-katamaran)
 (synopsis "Separation logic-based verification of instruction sets")
 (description "Katamaran is a semi-automated separation logic verifier for
the Sail specification language. It works on an embedded
version of Sail called Sail and verifies separation
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
  (rocq-core      (and (>= 9.2)    (< 9.4)))
  (rocq-equations (and (>= 1.3.2)  (< 1.4)))
  (rocq-iris      (and (>= 4.5.0)  (< 4.6)))
  (rocq-stdpp     (and (>= 1.13.0) (< 1.14)))))
