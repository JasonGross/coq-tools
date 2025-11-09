Require Import ZArith.
Notation hide := _.
Check I.
Ltac big n :=
    match n with
    | O => idtac
    | S ?n => let x := eval vm_compute in (List.repeat Z.div_eucl 16) in
        big n
    end.
Check I.
Goal True.
    big 40.
Abort.
