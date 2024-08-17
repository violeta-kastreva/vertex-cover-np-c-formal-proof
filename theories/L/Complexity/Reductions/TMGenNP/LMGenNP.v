From Undecidability.L Require Import Tactics.LTactics Prelim.MoreList Prelim.MoreBase.
From Undecidability.L.Complexity Require Import Synthetic.

From Undecidability.L Require Import LM_heap_def.

(** The halting formulation of the generic NP-complete problem for the abstract machine executing L-terms. 
This is usefull as we have a Turing machine that simulates this abstract machine. *)

Definition initLMGen s c : (list (nat*list Tok)*list (nat*list Tok)*list (option ((nat * list Tok) * nat)))
  := ([(0,s++c++[appT])],[],[]).

Section fixX.
  Local Unset Implicit Arguments.
  Context (X:Type) `{R__X : registered X}.   

  Definition LMHaltsOrDiverges : list Tok*nat*nat -> Prop :=
    fun '(P, maxSize, steps (*in unary*)) =>
      (exists s, P = compile s /\ proc s)
      /\ forall (c : X), size (enc c) <= maxSize -> forall k sigma', evaluatesIn step k (initLMGen P (compile (enc c))) sigma' -> k <= steps.

  Definition LMGenNP : list Tok*nat*nat -> Prop:= 
               (fun '(P, maxSize, k (*in unary*)) =>
                  exists (c:X), size (enc c) <= maxSize /\ (exists sigma' k', k' <= k /\ evaluatesIn step k' (initLMGen P (compile (enc c))) sigma')).
End fixX.

