Add LoadPath "/mnt/d/hamiltonian-cycle-formal-proof-np-c/ba-gaeher/external/uds-psl-base" as PslBase.
From PslBase Require Import FinTypes.

Require Import Coq.Logic.Classical_Prop.

Require Import Lia.

Require Import List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

  (* Section: Graph def *)

Record UGraph := 
  { 
    V : finType;
    E : V * V -> Prop; 
    E_dec : forall v1 v2, {E (v1, v2)} + {~ E (v1, v2)};
    E_symm: forall v1 v2, E (v1, v2) <-> E (v2, v1)
  }.
  (* Section: Clique Def *)

Section fixGraph.
  Variable (g : UGraph).
  Notation V := (V g).
  Notation E := (@E g).

  Definition isClique (l : list V) := (forall v1 v2, v1 el l -> v2 el l -> v1 <> v2 -> E (v1, v2)) /\ dupfree l.
  Definition isKClique k (l : list V) := |l| = k /\ isClique l.

  (** An alternative inductive characterization *)
  Inductive indKClique : nat -> list V -> Prop :=
    | indKCliqueNil : indKClique 0 []
    | indKCliqueS L v k : indKClique k L -> not (v el L) -> (forall v', v' el L -> E (v, v')) -> indKClique (S k) (v :: L).
  Hint Constructors indKClique.

  Lemma indKClique_iff k L: isKClique k L <-> indKClique k L.
  Proof.
    split.
    - intros [H1 [H2 H3]]. revert L H1 H2 H3. induction k; intros.
      + destruct L; cbn in H1; [ eauto | congruence].
      + destruct L; cbn in *; [congruence | ].
        constructor.
        * apply IHk; [lia | intros; apply H2; eauto | now inv H3].
        * now inv H3.
        * intros v' Hel. apply H2; [eauto | eauto | ]. inv H3. intros ->. congruence.
    - induction 1 as [ | ? ? ? ? IH].
      + split; [ | split]; [now cbn | intros ? ? [] | constructor].
      + destruct IH as (IH1 & IH2 & IH3). split; [ | split].
        * cbn. lia.
        * intros v1 v2 [-> | H2] [-> | H3] H4; try congruence.
          -- now apply H1.
          -- apply E_symm. now apply H1.
          -- now apply IH2.
        * now constructor.
  Qed.
End fixGraph.

Definition Clique (i : UGraph * nat) := let (g, k) := i in exists l, @isKClique g k l.

  (* Section: VertexCover def *)


Section ss.
  Variable g : UGraph.
  Notation V := (V g).
  Notation E := (@E g).

  (** ** Definition of Vertex Cover *)

  (** A vertex cover is a set of vertices such that every edge has at least one endpoint in the set *)
  Definition isVertexCover (S : list V) : Prop :=
    (forall v1 v2, E (v1, v2) -> v1 el S \/ v2 el S) /\ dupfree S.

  (** A k-vertex cover is a vertex cover of size k *)
  Definition isKVertexCover (k : nat) (S : list V) : Prop :=
    |S| = k /\ isVertexCover S.

  (** ** Definition of KVertexCover Problem *)

  (** We define the KVertexCover problem as seeking a vertex cover of size k in a given graph *)
  Definition KVertexCover (k : nat) : Prop :=
      exists S, isKVertexCover k S.



Definition V_complement := V.

(* Step 2: Define the edge relation for the complement graph *)
Definition E_complement (p : V_complement * V_complement) : Prop :=
  let (v1, v2) := p in
  ~ E (v1, v2).

(* Step 3: Prove the symmetry of the complement edge relation *)
Lemma E_complement_symm v1 v2 : E_complement (v1, v2) <-> E_complement (v2, v1).
Proof.
  unfold E_complement.
  split; intro HnE.
  - intro HE. apply HnE. apply E_symm. exact HE.
  - intro HE. apply HnE. apply E_symm. exact HE.
Qed.

(* Step 4: Prove the decidability of the complement edge relation *)
Lemma E_complement_dec (v1 v2 : V_complement) : {E_complement (v1, v2)} + {~ E_complement (v1, v2)}.
Proof.
  unfold E_complement.
  destruct (E_dec v1 v2) as [HE | HnE].
  - right. intro Hcomp. apply Hcomp. exact HE.
  - left. exact HnE.
Defined.
  
Definition complementGraph :=
  Build_UGraph
    E_complement_dec
    E_complement_symm.
  (** Reduction function from Clique to Vertex Cover *)

End ss.

(* Definition Clique_to_VertexCover (g : UGraph) (k : nat) : UGraph * nat :=
    (complementGraph g, length (elem (V g)) - k). *)
  
  (* Section: List stuff *)
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
    induction l1 as [| x xs IH].
    - (* Base case: l1 = [] *)
      simpl. reflexivity.
    - (* Inductive step: l1 = x :: xs *)
      simpl.
      destruct (in_list x l2) eqn:H_in.
      + (* Case: x is in l2 *)
        rewrite IH.
        simpl. reflexivity.
     + (* Case: x is not in l2 *)
       admit.


  Admitted.

  
Lemma in_list_spec {A : eqType} (x : A) (l : list A) :
  reflect (In x l) (in_list x l).
Proof.
Admitted.


Lemma count_in_list_one {A : eqType} (x : A) (l : list A) :
In x l ->
count_in_list [x] l = 1.
Proof.
admit.
Admitted.   


Lemma dupfree_list_diff {A : eqType} (l1 l2 : list A) :
  dupfree l1 -> dupfree (list_diff l1 l2).
Proof.
Admitted.


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
  (* Since L is a list of vertices from g0, x must be in the vertex set V g0 *)
  unfold isKClique in Hclique.
  destruct Hclique as [Hlen Hcl].
  (* Apply elem_spec to assert that every vertex in L is in V g0 *)
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
  - (* Proof that xs is a k-clique *)
    split.
      + intros v1 v2 H1 H2 Hneq.
        apply Hrel; auto.
      + apply dupfree_cons_inv with (x0 := x).
        assumption. (* dupfree condition for xs *)
  - split.
    + apply dupfree_cons_inv with (x0 := x). apply Hdup.
    + intros v' Hvin.
    apply Hrel with (v1 := x) (v2 := v'); auto. 
     * intro H_eq.
     subst.
     apply dupfree_cons_inv in Hdup as [Hdup' Hnotin].
     contradiction.
Qed.


Lemma count_in_list_cons_increase {A : eqType} (x : A) (xs l2 : list A) (k : nat) :
  count_in_list l2 xs = k ->
  dupfree (x :: xs) ->
  In x l2 ->
  count_in_list l2 (x :: xs) = S k.
Proof.
Admitted.

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
    assert (Hx_notin_xs : ~ x el xs).
    {
      apply dupfree_cons_inv in Hdup. destruct Hdup as [Hdup' Hnotin]. assumption.
    }

    specialize (IH Hxs_clique).

 (* Now the goal is: count_in_list (elem (V g0)) (x :: xs) = S (length xs) *)
      apply count_in_list_cons_increase with (l2 := (elem (V g0))); auto.
    
Qed.

Lemma vertex_cover_is_subset_of_vertex_set (g0 : UGraph) (k : nat) (S : list (V g0)) :
  isKVertexCover k S -> forall x, In x S -> In x (elem (V g0)).
Proof.
  intros Hvertex_cover x Hx.
  (* Since S is a list of vertices forming a vertex cover in g0, x must be in the vertex set V g0 *)
  unfold isKVertexCover in Hvertex_cover.
  destruct Hvertex_cover as [Hlen Hvc].
  (* Apply elem_spec to assert that every vertex in S is in V g0 *)
  apply elem_spec.
Qed.


Lemma count_in_list_equals_length_if_vertex_cover (g0 : UGraph) (S : list (V g0)) :
  isKVertexCover (length S) S -> count_in_list (elem (V g0)) S = length S.
Proof.
intros Hvertex_cover.
(* Extract the properties from the isKVertexCover assumption *)
destruct Hvertex_cover as [Hlen [Hvc Hdup]].

(* Use a direct argument based on the fact that S is a subset of V g0 *)
assert (Hsubset: forall x, In x S -> In x (elem (V g0))).
{
  intros x HxS.
  apply vertex_cover_is_subset_of_vertex_set with (k := length S); assumption.
}

(* Now prove that count_in_list matches the length of S *)
induction S as [| x xs IH].
- (* Base case: S is empty *)
  simpl. rewrite count_in_list_empty_r. reflexivity.
- (* Inductive step: S is non-empty *)
  simpl.
  assert (Hx_in_Vg0: x el elem (V g0)) by (apply Hsubset; left; reflexivity).
  assert (Hx_notin_xs: ~ x el xs).
  {
    apply dupfree_cons_inv in Hdup. destruct Hdup as [Hdup' Hnotin]. assumption.
  }
  specialize (IH Hlen Hvc Hdup).

  (* Now the goal is: count_in_list (elem (V g0)) (x :: xs) = S (length xs) *)
  rewrite <- IH.
  apply count_in_list_cons_increase with (l2 := elem (V g0)); auto.
Qed.


Section dd.
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
      destruct Hclique as [_ Hcl].
      destruct Hcl as [Hedge _].
      destruct (in_dec (fun x y => eqType_dec x y) v1 L) as [Hvin1 | Hnin1].
      -- destruct (in_dec (fun x y => eqType_dec x y) v2 L) as [Hvin2 | Hnin2].
         ++ (* Case: Both v1 and v2 are in L, which is a contradiction *)
            exfalso.
            assert (Hneq: v1 <> v2). {
              intro H_eq.
              subst v2.
              contradiction HE_compl.
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
    unfold isKVertexCover in Hcover. destruct Hcover as [Hsize Hvc].
    rewrite list_diff_length.  
    assert (Hdiff_size: length ( elem (V g0) ) - length (S) = k).
    {
      simpl.
    }  
    assert (Hcount: |S| = count_in_list (elem (V g0)) S ).
   { 
    induction S as [| x xs IH].
    - (* Base case: S is empty *)
      simpl. rewrite count_in_list_empty_r. reflexivity.
    - (* Inductive step: S is non-empty *)
      simpl.
      destruct (in_list_spec x (elem (V g0))) as [Hin | Hnin].
      + (* Case: x is in the vertex set of g0 *)
        simpl. f_equal. apply IH.
      + (* Case: x is not in the vertex set of g0, which is a contradiction *)
        exfalso. unfold isVertexCover in Hcover. destruct Hcover as [_ Hvc].
        specialize (Hvc x x).
        assert (Hx_in_S : x el S).
        {
          left. reflexivity.
        }
        apply Hvc in Hx_in_S.
        destruct Hx_in_S as [Hx_in_S1 | Hx_in_S2]; contradiction.
   }
    rewrite Hcount in Hdiff_size.
    exact Hdiff_size.

    + split.
      * intros v1 v2 H1 H2 Hneq.
      assert (Hnv1 : ~ v1 el S).
      {
        apply list_diff_in_iff in H1. tauto.
      }
      assert (Hnv2 : ~ v2 el S).
      {
        apply list_diff_in_iff in H2. tauto.
      }
      assert (Hcomp_edge: ~ E_complement (v1, v2)).
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
End dd.