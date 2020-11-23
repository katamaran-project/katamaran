Debugging verification failures
========================================

Revealing debug information
---------------------------

To investigate failures of contract verification you can selectively make parts
of the symbolic executor opaque or prevent delta expansion. As of now, the
functions of interest are `valid_obligation` and `Error`, but you may also want
to include more fixpoints to reduce the size of the output.

For instance, the tactic invocation
```
compute - [NamedEnv Lit Error valid_obligation].
```

might yield

```
valid_obligation (obligation [] (formula_eq (term_var "i") (term_lit ty_addr 0%Z))
```

which reveals the symbolic representation of the obligation which uses the
symbolic logic variables from the contracts.

Failed chunk consumption
------------------------

A failed consumption of a heap chunk will provide you with a value of the
`DynamicMutatorError` record:

```
Error
  {| dmuterr_function := "dmut_consume_chunk_evar";
     dmuterr_message := "Empty extraction";
     dmuterr_data_type := 
       EvarError 
         [("reg", ty_lv), ("w", ty_word), ("result", ty_word)]
         [("w", ty_word), ("_", ty_unit)]
         (Chunk [("reg", ty_lv), ("w", ty_word), ("result", ty_word)]);
     dmuterr_data := 
     {| evarerror_env := [Some (term_lit ty_lv R0), Some (term_var "w"), Some (term_var "w")];
        evarerror_data := term_var "reg" ↦r term_var "w" 
     |};
     dmuterr_logic_context := [("w", ty_word), ("_", ty_unit)];
     dmuterr_program_context := [("reg", ty_lv)];
     dmuterr_localstore := [term_lit ty_lv R0];
     dmuterr_pathcondition := [];
     dmuterr_heap := [reg0 ↦ term_var "w"]%list 
   |}
```

The interesting parts here are the contents of the heap `dmuterr_heap` and the
chunk to be consumed `evarerror_data`. In the above example, the user-defined
predicate `term_var "reg" ↦r term_var "w"` is to be consumed, but the heap only
contains the primitive register points to chunk `reg0 ↦ term_var "w"`.

Debugging mutator from Katamaran 2.0
------------------------------------

The next version of Katamaran will use a symbolic version of outcome trees. The
contract validity predicate `TwoPointO.ValidContractDynMutDebug` will show the
resulting tree just before applying post-condition satisfaction:

```
TwoPointO.sout_ok_opaque [("reg", ty_lv), ("w", ty_word)]
  (sout_subst "reg" (term_lit ty_lv R0)
     (sout_fail
        {| dmuterr_function := "dmut_consume_chunk_evar";
           dmuterr_message := "Empty extraction";
           dmuterr_data_type := 
             EvarError
               [("reg", ty_lv), ("w", ty_word), ("result", ty_word)] 
               [("w", ty_word)] (Chunk [("reg", ty_lv), ("w", ty_word), ("result", ty_word)]);
           dmuterr_data := 
           {| evarerror_env := [Some (term_lit ty_lv R0), Some (term_var "w"), Some (term_var "w")];
              evarerror_data := term_var "reg" ↦r term_var "w" 
           |};
           dmuterr_logic_context := [("w", ty_word)];
           dmuterr_program_context := [("reg", ty_lv)];
           dmuterr_localstore := [term_lit ty_lv R0];
           dmuterr_pathcondition := [];
           dmuterr_heap := [reg0 ↦ term_var "w"]%list 
        |}))
```
