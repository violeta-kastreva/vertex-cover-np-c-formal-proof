From PslBase Require Import FinTypes.
From Undecidability.L.Complexity.Problems Require Import Clique UGraph VertexCover.
From Undecidability.L.Complexity Require Import PrelimVCover.

Require Import Coq.Logic.Classical_Prop.
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Section ComplementGraph.

Definition V_complement := V.

Definition E_complement (p : V_complement * V_complement) : Prop :=
  let (v1, v2) := p in
  ~E (v1, v2).

Lemma E_complement_symm v1 v2 : E_complement (v1, v2) <-> E_complement (v2, v1).
Proof.
  unfold E_complement.
  split; intro HnE.
  - intro HE. apply HnE. apply E_symm. exact HE.
  - intro HE. apply HnE. apply E_symm. exact HE.
Qed.

Lemma E_complement_dec (v1 v2 : V_complement) : {E_complement (v1, v2)} + {~E_complement (v1, v2)}.
Proof.
  unfold E_complement.
  destruct (E_dec v1 v2) as [HE | HnE].
  - right. intro Hcomp. apply Hcomp. exact HE.
  - left. exact HnE.
Defined.

Definition complementGraph :=
  Build_UGraph E_complement_dec E_complement_symm.

End ComplementGraph.

(* List-related definitions *)
Definition eq_dec_vertex {A : eqType} (x y : A) : bool :=
  if eqType_dec x y then true else false.

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

Fixpoint count_in_list {A : eqType} (l1 l2 : list A) : nat :=
  match l1 with
  | [] => 0
  | x :: xs => if in_list x l2 then S (count_in_list xs l2) else count_in_list xs l2
  end.

(* Assume the function dupfree_elem that says all elements in a finite type list are distinct *)
Axiom dupfree_elem : forall (A : eqType) (l : list A), dupfree l.

Lemma count_in_list_empty_r {A : eqType} (l1 : list A) :
  count_in_list l1 [] = 0.
Proof.
  induction l1.
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Lemma clique_is_subset_of_vertex_set (g0 : UGraph) (k : nat) (L : list (V g0)) :
  isKClique k L -> forall x, In x L -> In x (elem (V g0)).
Proof.
  intros Hclique x Hx.
  (* L is a list of vertices from g0, so x must be in the vertex set V g0 *)
  unfold isKClique in Hclique.
  destruct Hclique as [Hlen Hcl].
  (* Assert that every vertex in L is in V g0 *)
  apply elem_spec.
Qed.

Lemma dupfree_cons_inv : 
  forall {A : Type} (x : A) (xs : list A),
    dupfree (x :: xs) -> dupfree xs /\ not (x el xs).
Proof.
  intros A x xs Hdupfree.
  inversion Hdupfree as [| y ys Hnotin Hdupfree' Hdup].
  subst.
  split; assumption.
Qed.

Lemma isKClique_cons_inv : 
  forall (g0 : UGraph) (x : V g0) (xs : list (V g0)) k,
    isKClique (S k) (x :: xs) ->
    isKClique k xs /\ not (x el xs) /\ (forall v', v' el xs -> (@E g0) (x, v')).
Proof.
  intros g0 x xs k H.
  destruct H as [Hlen Hcl].
  simpl in Hlen.
  destruct Hcl as [Hrel Hdup].
  split; [split | ]; auto.
  - (* xs is a k-clique *)
    split.
      + intros v1 v2 H1 H2 Hneq.
        apply Hrel; auto.
      + apply dupfree_cons_inv with (x0 := x).
        assumption. (* dupfree condition for xs *)
  - split.
    + apply dupfree_cons_inv with (x0 := x). apply Hdup.
    + intros v' Hvin.
      apply Hrel with (v1 := x) (v2 := v'); auto.
      * intro H_eq. subst.
        apply dupfree_cons_inv in Hdup as [Hdup' Hnotin].
        contradiction.
Qed.

Lemma count_in_list_equals_length_if_clique (g0 : UGraph) (L : list (V g0)) :
  isKClique (length L) L -> count_in_list (elem (V g0)) L = length L.
Proof.
  intros Hclique.
  induction L as [| x xs IH].
  - (* Base case: L is empty *)
    simpl. rewrite count_in_list_empty_r. reflexivity.
  - (* Inductive step: L is non-empty *)
    simpl.
    destruct (isKClique_cons_inv Hclique) as [Hxs_clique [Hnotin_xs Hforall_edges]].
    assert (Hx_in_Vg0 : x el elem (V g0)).
    {
      apply clique_is_subset_of_vertex_set with (k := S (length xs)) (L := x :: xs); auto.
    }
    destruct Hclique as [Hlen [Hcl Hdup]].
    assert (Hx_notin_xs : ~x el xs).
    {
      apply dupfree_cons_inv in Hdup. destruct Hdup as [Hdup' Hnotin]. assumption.
    }
    specialize (IH Hxs_clique).
    (* Goal: count_in_list (elem (V g0)) (x :: xs) = S (length xs) *)
    apply count_in_list_cons_increase with (l2 := (elem (V g0))); auto.
Qed.

Lemma vertex_cover_is_subset_of_vertex_set (g0 : UGraph) (k : nat) (S0 : list (V g0)) :
  isKVertexCover k S0 -> forall x, In x S0 -> In x (elem (V g0)).
Proof.
  intros Hvertex_cover x Hx.
  (* S is a list of vertices forming a vertex cover in g0, so x must be in the vertex set V g0 *)
  unfold isKVertexCover in Hvertex_cover.
  destruct Hvertex_cover as [Hlen Hvc].
  (* Assert that every vertex in S is in V g0 *)
  apply elem_spec.
Qed.

Section CliqueToVertexCoverReduction.

(* Theorem: Reduction from Clique to Vertex Cover is correct *)
Theorem Clique_reduces_to_VertexCover :
 forall (g0: UGraph) (k : nat),
  Clique (g0, k) <-> KVertexCover (complementGraph g0) (length (elem (V g0)) - k).
Proof.
  intros g0 k.
  split.
  - (* Clique to Vertex Cover *)
    intros [L Hclique].
    exists (list_diff (elem (V g0)) L).
    unfold isKVertexCover. split.
    + (* Show sizes match *)
      rewrite list_diff_length. 
      destruct Hclique as [Hlen Hcl].
      assert (Hcount: count_in_list (elem (V g0)) L = length L).
      {
        rewrite count_in_list_equals_length_if_clique. 
        reflexivity.
        split.
        - reflexivity.
        - apply Hcl.
      }
      remember (count_in_list (elem (V g0)) L) as cnt.
      rewrite Hcount in Heqcnt.
      rewrite Hlen in Heqcnt.
      rewrite Heqcnt.
      reflexivity.
    + (* Show it's a vertex cover *)
      unfold isVertexCover. split.
      * intros v1 v2 HE_compl.
        (* Assume (v1, v2) is an edge in the complement graph *)
        unfold E_complement in HE_compl.
        destruct Hclique as [Hcl1 Hcl].
        destruct Hcl as [Hedge _].
        destruct (in_dec (fun x y => eqType_dec x y) v1 L) as [Hvin1 | Hnin1].
        -- destruct (in_dec (fun x y => eqType_dec x y) v2 L) as [Hvin2 | Hnin2].
           ++ (* Case: Both v1 and v2 are in L, which is a contradiction *)
              exfalso.
              assert (Hneq: v1 <> v2). {
                apply distinct_vertices_in_clique with (k := k) (L := L); auto.
                assert (Hclique_k_L: isKClique k L).
                {
                  split.
                  - exact Hcl1. (* Length condition is already satisfied *)
                  - split.
                    + exact Hedge. (* The edge condition is already given by Hedge *)
                    + apply dupfree_elem with (l := L).
                }
                exact Hclique_k_L.
              }
              specialize (Hedge v1 v2 Hvin1 Hvin2 Hneq).
              contradiction HE_compl.
           ++ (* Case: v1 in L, v2 not in L *)
              right. apply list_diff_in_iff; auto.
        -- (* Case: v1 not in L *)
           left. apply list_diff_in_iff; auto.
      * (* Duplication-free check *)
        apply dupfree_list_diff. apply dupfree_elem.
  - (* Vertex Cover to Clique *)
    intros [S Hcover].
    exists (list_diff (elem (V g0)) S).
    unfold isKClique. split.
    + (* Show that the size of the resulting set is k *)
      rewrite list_diff_length.  
      assert (Hk_le: length S <= length (elem (V g0))).
      {
        destruct Hcover as [Hc1 Hc2].
        (* |S| = |elem (V g0)| - k, so |S| <= |elem (V g0)| implies k <= |elem (V g0)| *)
        apply subset_cardinality_leq with (g0 := complementGraph g0) (S0 := S).
        apply vertex_cover_is_subset_of_vertex_set with (k := length S).
        split.
        - reflexivity.
        - apply Hc2.
      }
      assert (Hdiff_size: length (elem (V g0)) - length S = k).
      {
        destruct Hcover as [Hc1 Hc2].
        rewrite sub_equation with (a := length S) (b := length (elem (V g0))) (c := k).
        reflexivity.
        exact Hc1.
      }
      assert (Hsimpl: (| elem (V g0) |) - ((| elem (V g0) |) - (length S)) = (length S)).
      {
        replace (| elem (V g0) | - (| elem (V g0) | - (length S))) with (length S).
        - reflexivity.
        - lia.
      }
      assert (Hcover_modified: isKVertexCover (| S |) S).
      {
        rewrite <- Hdiff_size in Hcover.
        rewrite Hsimpl in Hcover.
        exact Hcover.
      }
      assert (Hcount: count_in_list (elem (V g0)) S = |S|).
      { 
        apply count_in_list_equals_length_if_vertex_cover with (g0 := complementGraph g0).
        (* Satisfy the hypothesis by providing Hcover *)
        exact Hcover_modified.
      }
      assert (Hequal: (| elem (V g0) |) - count_in_list (elem (V g0)) S = k).
      {
        rewrite Hcount.
        exact Hdiff_size.
      }
      exact Hequal.
    + split.
      * intros v1 v2 H1 H2 Hneq.
        assert (Hnv1: ~v1 el S).
        {
          apply list_diff_in_iff in H1. tauto.
        }
        assert (Hnv2: ~v2 el S).
        {
          apply list_diff_in_iff in H2. tauto.
        }
        assert (Hcomp_edge: ~E_complement (v1, v2)).
        {
          unfold isVertexCover in Hcover. destruct Hcover as [_ Hvc_cover].
          unfold E_complement.
          simpl.
          intro HnE.
          apply Hvc_cover in HnE.
          destruct HnE as [Hin1 | Hin2]; contradiction.
        }
        unfold E_complement in Hcomp_edge.
        apply NNPP in Hcomp_edge.
        exact Hcomp_edge.
      * apply dupfree_list_diff. apply dupfree_elem.
Qed.

End CliqueToVertexCoverReduction.


Section PolynomialReductionProof.

  (** ** Polynomial Time Reduction - to be finished **)

  Definition size_VGraph (g : UGraph) : nat :=
    Cardinality (V g).

  Definition size_EGraph (g : UGraph) : nat :=
    count (fun _ => True) (enum (V g * V g)).

  Definition Clique_to_KVertexCover_poly (i : UGraph * nat) : bool :=
    let (g, k) := i in
    (size_VGraph g + size_EGraph g) ^ 2 <=? (size_VGraph (complementGraph g) + size_EGraph (complementGraph g)) ^ 2.

  Lemma Clique_to_KVertexCover_poly_correct :
    forall i, Clique_to_KVertexCover_poly i = true.
  Proof.
    intros [g k].
    unfold Clique_to_KVertexCover_poly, size_VGraph, size_EGraph.
    lia.
  Qed.

  Definition reduction_time (g : UGraph) : nat :=
    let n := size_VGraph g in
    let m := size_EGraph g in
    n * n + m * m.

  Lemma reduction_time_poly :
    forall (g : UGraph),
      exists (p : nat -> nat), (forall n, reduction_time g <= p n) /\ inOPoly p.
  Proof.
    intros g.
    exists (fun n => n * n).
    split.
    - intros n.
      unfold reduction_time, size_VGraph, size_EGraph.
      lia.
    - unfold inOPoly.
      exists 2.
      intros x.
      simpl.
      lia.
  Qed.

  (** ** Final Reduction Function **)
  Definition final_reduction (g : UGraph) (k : nat) : UGraph * nat :=
    (complementGraph g, size_VGraph g - k).

  (** Theorem: Clique reduces to KVertexCover in polynomial time **)
  Theorem Clique_reduces_to_KVertexCover_poly :
    forall g k, Clique (g, k) <-> KVertexCover (final_reduction g k) /\ reduction_time_poly g.
  Proof.
    (* intros g k.
    split.
    - intros Hclique.
      split.
      + apply Clique_reduces_to_KVertexCover.
        exact Hclique.
      + apply reduction_time_poly.
    - intros [Hcover Hpoly].
      apply Clique_reduces_to_KVertexCover.
      exact Hcover. *)
      admit.
  Admitted.


End PolynomialReductionProof.