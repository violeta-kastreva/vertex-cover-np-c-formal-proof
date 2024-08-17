Require Import Coq.Logic.Classical_Prop.

Require Import Lia.

Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

From PslBase Require Import FinTypes.


Definition eq_dec_vertex {A : eqType} (x y : A) : bool :=
    if eqType_dec x y then true else false.

(* Check if an element is in a list using a provided equality decision function *)
Fixpoint in_list {A : eqType} (x : A) (l : list A) : bool :=
  match l with
  | [] => false
  | y :: ys => if eq_dec_vertex x y then true else in_list x ys
  end.

Fixpoint list_diff {A : eqType} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => []
  | x :: xs => if in_list x l2 then list_diff xs l2 else x :: list_diff xs l2
  end.

  (* Fixpoint list_diff_length {A : eqType} (l1 l2 : list A) : nat :=
  match l1 with
  | [] => 0
  | x :: xs => if in_list x l2 then list_diff_length xs l2 else 1 + list_diff_length xs l2
  end. *)

  Fixpoint count_in_list {A : eqType} (l1 l2 : list A) : nat :=
    match l1 with
    | [] => 0
    | x :: xs => if in_list x l2 then S (count_in_list xs l2) else count_in_list xs l2
    end.

Lemma list_diff_length {A : eqType} (l1 l2 : list A) :
length (list_diff l1 l2) = length l1 - count_in_list l1 l2.
  Proof.
    induction l1 as [| x xs IH]; simpl.
    - (* Base case: when l1 is empty *)
      reflexivity.
    - (* Inductive step: when l1 is non-empty *)
      destruct (in_list x l2) eqn:Hx.
      + (* Case when x is in l2 *)
        rewrite IH. simpl. lia.
      + (* Case when x is not in l2 *)
        simpl. rewrite IH. simpl.  
  Qed.
  
  

Lemma dupfree_list_diff {A : eqType} (l1 l2 : list A) :
  dupfree l1 -> dupfree (list_diff l1 l2).
Proof.
  intros H. induction l1 as [| x xs IH]; simpl.
  - constructor.
  - destruct (in_list x l2) eqn:Hx.
    + apply IH. inversion H; assumption.
    + inversion H; subst. constructor.
      * intros Hcontra. apply in_list_spec in Hcontra.
        rewrite Hx in Hcontra. discriminate.
      * apply IH. assumption.
Qed.

(* Assume the function dupfree_elem that says all elements in a finite type list are distinct *)
Axiom dupfree_elem : forall (A : eqType) (l : list A), dupfree l.
End ss.
  Section dd.