(dump-nanosail-ast)

(pretty-print-lists)

;(annotate-functions-with-ast)

;; (ignore-all-overloads)
;; (ignore-pragmas (lambda (identifier)
;;                   (contains? '("include_start"
;;                                "include_end"
;;                                "file_start"
;;                                "file_end"
;;                                "sail_internal")
;;                              identifier)))

(ignore-function-definition-and-top-level-type-constraints-predicate
 (lambda (identifier)
   (or
    (string-ends-with? "_of_num" identifier)
    (string-starts-with? "num_of_" identifier)
    (string-starts-with? "undefined_" identifier)
    (string-starts-with? "regval_of_" identifier)
    (string-ends-with? "_of_regval" identifier)
    (= "reverse_bits_in_byte" identifier)
    (= "log2" identifier)
    (= "zeros_implicit" identifier)
    (= "ones" identifier)
    (contains? '(
                 "sep"
                 "sail_zeros"
                 "sail_ones"
                 "slice_mask"
                 )
               identifier))))

;; Translate these polymorphic unions to muSail's ty.sum instead of to a
;; ty.union of their own. The first constructor becomes inl, the second inr,
;; so option('a) becomes ty.sum 'a ty.unit, i.e., ty.option 'a.
(translate-union-as-sum "option" "Some" "None")
(translate-union-as-sum "result" "Ok" "Err")

;; (ignore-type-definition-predicate (lambda (identifier)
;;                                (contains? '("real"
;;                                             "option"
;;                                             "register_value"
;;                                             "bits"
;;                                             "regstate")
;;                                           identifier)))

;; (ignore-value-definition-predicate
;;  (lambda (identifier)
;;    (contains? '(
;;                 "default_capability"
;;                 "initial_regstate"
;;                 "initial_Capability"
;;                 )
;;               identifier)))

(template "base.template.v")
(template "machine.template.v")
