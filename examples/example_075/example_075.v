Require Import ZArith.
Require Import List.
Module List.
    Section Repeat.
        Variable A : Type.
        Fixpoint repeat (x : A) (n: nat ) :=
            match n with
            | O => nil
            | S k => cons x (repeat x k)
            end.

    End Repeat.
End List.
Notation hide := _.
Check I.
Fail I.
Goal True. idtac "File ""./example_075.v"", line 999, characters 0-0:". idtac "Error:". Abort.
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
