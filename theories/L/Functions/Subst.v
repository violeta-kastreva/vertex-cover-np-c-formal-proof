From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Functions.EqBool Datatypes.LTerm.
(** ** Extracted substitution on terms *)

Instance term_substT :
  computableTime' subst (fun s _ => (5, (fun n _ => (1, (fun t _ => ( (size s) * (size s + c__eqbComp nat * 4 + 20), tt)))))).
Proof.
  unfold subst. change Nat.eqb with (EqBool.eqb (X:=nat)).
  extract. unfold eqbTime.

  recRel_prettify2. all:unfold eqbTime; cbn [fst snd size].
  all:try rewrite !size_nat_enc.
  all:try nia.
Qed.
