
type ('a, 'r) coq_Reflexive = 'a -> 'r

type ('a, 'r) coq_Transitive = 'a -> 'a -> 'a -> 'r -> 'r -> 'r

type ('a, 'r) coq_PreOrder = { coq_PreOrder_Reflexive : ('a, 'r) coq_Reflexive;
                               coq_PreOrder_Transitive : ('a, 'r)
                                                         coq_Transitive }
