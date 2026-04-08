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
    (contains? '(
                 "sep"
                 )
               identifier))))

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
