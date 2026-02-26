open Ofe

type __ = Obj.t

type bi = { bi_emp : __; bi_pure : (__ -> __); bi_and : (__ -> __ -> __);
            bi_or : (__ -> __ -> __); bi_impl : (__ -> __ -> __);
            bi_forall : (__ -> (__ -> __) -> __);
            bi_exist : (__ -> (__ -> __) -> __); bi_sep : (__ -> __ -> __);
            bi_wand : (__ -> __ -> __); bi_persistently : (__ -> __);
            bi_later : (__ -> __); bi_cofe_aux : coq_Cofe }
