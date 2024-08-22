(* Additional List lemmas needed for the reduction - some left to prove *)
Require Import Coq.Logic.Classical_Prop.
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.



Lemma dupfree_list_diff {A : eqType} (l1 l2 : list A) :
  dupfree l1 -> dupfree (list_diff l1 l2).
Proof.
Admitted.


Lemma list_diff_length {A : eqType} (l1 l2 : list A) :
length (list_diff l1 l2) = length l1 - count_in_list l1 l2.
Proof.
induction l1 as [| x xs IH].
- 
  simpl. reflexivity.
- 
  simpl.
  destruct (in_list x l2) eqn:H_in.
  + 
    rewrite IH.
    simpl. reflexivity.
 + 
   admit.


Admitted.


Lemma in_list_spec {A : eqType} (x : A) (l : list A) :
reflect (In x l) (in_list x l).
Proof.
Admitted.



Lemma list_diff_in_iff {A : eqType} (x : A) (l1 l2 : list A) :
  x el list_diff l1 l2 <-> x el l1 /\ ~ x el l2.
Proof.
  induction l1 as [| y ys IH]; simpl.
  - (* Base case: l1 is empty *)
    split.
    + intros H. inversion H.
    + intros [H _]. inversion H.
  - (* Inductive step: l1 is non-empty *)
    admit.
Admitted.

Lemma count_in_list_cons_increase {A : eqType} (x : A) (xs l2 : list A) (k : nat) :
  count_in_list l2 xs = k ->
  dupfree (x :: xs) ->
  In x l2 ->
  count_in_list l2 (x :: xs) = S k.
Proof.
Admitted.


Lemma count_in_list_equals_length_if_vertex_cover (g0 : UGraph) (S : list (V g0)) :
  isKVertexCover (length S) S -> count_in_list (elem (V g0)) S = length S.
Proof.
intros Hvertex_cover.
destruct Hvertex_cover as [Hlen [Hvc Hdup]].

assert (Hsubset: forall x, In x S -> In x (elem (V g0))).
{
  intros x HxS.
  apply vertex_cover_is_subset_of_vertex_set with (k := length S) (S0 := S).
}

induction S as [| x xs IH].
-
  simpl. rewrite count_in_list_empty_r. reflexivity.
-
  simpl.
  assert (Hx_in_Vg0: x el elem (V g0)) by (apply Hsubset; left; reflexivity).
  assert (Hx_notin_xs: ~ x el xs).
  {
    apply dupfree_cons_inv in Hdup. destruct Hdup as [Hdup' Hnotin]. assumption.
  }
  assert (Hlen_xs: |xs| = |xs|) by reflexivity.
  assert (Hxs_cover: isKVertexCover (length xs) xs).
    {
      split.
      - lia.
      - split.
        +
          intros v1 v2 HE.
          specialize (Hvc v1 v2 HE).
          destruct Hvc as [Hvc1 | Hvc2].
          * 
            destruct (eqType_dec v1 x) as [Heq1 | Hneq1].
            -- subst v1. right. admit.
            -- destruct (eqType_dec v2 x) as [Heq2 | Hneq2].
               ++ subst v2. right. admit.
               ++ 
                  left. admit.
          * 
            destruct (eqType_dec v2 x) as [Heq2 | Hneq2].
            -- subst v2. left. admit.
            -- destruct (eqType_dec v1 x) as [Heq1 | Hneq1].
               ++ subst v1. left. admit.
               ++ 
                  right. admit.
        + 
          apply dupfree_cons_inv in Hdup.
          destruct Hdup as [Hdupf Hx_not_xs].
          exact Hdupf.
    }
    destruct Hxs_cover as [H1 H2].
    specialize (IH Hlen_xs).
    admit.
Admitted.

Lemma dupfree_subset_length_leq {A : Type} (S L : list A) :
  dupfree L -> dupfree S -> (forall x, In x S -> In x L) -> length S <= length L.
Proof.
  intros Hdupfree_L Hdupfree_S Hsubset.
  induction L as [| x xs IH].
  (* - simpl in *. admit. destruct S; [lia | exfalso; apply (Hsubset a); left; reflexivity]. *)
  (* - simpl in *. admit.
    destruct (in_dec eq_dec x S) as [Hin_S | Hnotin_S].
    + 
      specialize (Hsubset x).
      assert (Hlen: length S <= length xs) by (apply IH; auto; intros; apply Hsubset; right; assumption).
      lia.
    + 
      apply IH; auto; intros; apply Hsubset; right; assumption. *)
Admitted.

Lemma subset_cardinality_leq (g0 : UGraph) (S0 : list (V g0)) :
  (forall x, In x S0 -> In x (elem (V g0))) -> length S0 <= length (elem (V g0)).
Proof.
  
Admitted.


Lemma sub_equation : forall a b c : nat,
  a = b - c -> c = b - a.
Proof.

Admitted.


Lemma distinct_vertices_in_clique (g0 : UGraph) (k : nat) (L : list (V g0)) :
  isKClique k L -> forall v1 v2, v1 el L -> v2 el L -> v1 <> v2.
Proof.
  intros Hclique v1 v2 Hvin1 Hvin2.
  destruct Hclique as [_ [Hedge _]].
  intro H_eq.
  subst v2.
  specialize (Hedge v1 v1 Hvin1 Hvin1).
  admit.
Admitted.
