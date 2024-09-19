From Coq Require Import Program.
Program Definition foo : False := _.
Next Obligation. Admitted.
Section bar.
  Context (v : False).
  Definition bar := v.
End bar.
Check bar : True.
