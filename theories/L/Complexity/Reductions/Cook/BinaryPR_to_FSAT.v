From PslBase Require Import Base. 
From Undecidability.L.Complexity Require Import Tactics MorePrelim. 
From Undecidability.L.Datatypes Require Import LLists LLNat LBool LProd LOptions. 
From Undecidability.L.Complexity.Problems Require Import FSAT Cook.BinaryPR.
Require Import Lia. 

(** * Reduction of BinaryPR to FSAT *)
(** High-level overview:
We lay out the BinaryPR computation in a tableau which has (steps + 1) lines, where steps is the number of steps of the BPR instance, 
and each line has a length which is equal to the length of the BPR strings.
Each cell of the tableau corresponds to one symbol of a BPR string and is encoded using a single Boolean variable in the FSAT instance.

The FSAT formula consists of three gadgets, encoding:
- the constraint on the initial string
- the validity of rewrites 
- the final constraints.

The constraint on the initial string is straightforward to encode: We just have a big AND over the positions of the string.

For the validity of rewrites, we have a AND consisting of a subformula for each of the rewrites.
Each rewrite in turn forces that the successor string evolves validly from the current string - we have an AND over the offsets of the string
at which rewrite windows have to hold. 
For each of the offsets, we then have a disjunction over all rewrite windows. 
That a rewrite window holds at a position is encoded similarly to the initial string.

For the final constraint, we have a disjunction over the final strings and a nested disjunction over all positions at which a string can be a substring.
*)

Section fixInstance. 
  Variable (bpr : BinaryPR). 
  
  Notation offset := (offset bpr). 
  Notation width := (width bpr). 
  Notation init := (init bpr). 
  Notation windows := (windows bpr).
  Notation final := (final bpr).
  Notation steps := (steps bpr). 

  Context (A : BinaryPR_wellformed bpr). 
  Notation llength := (length init). 
  Implicit Types (a : assgn) (v : var). 

  (** convenience functions for creating formulas *)
  Notation Ffalse := (¬Ftrue). 
  Fixpoint listOr (l : list formula) := match l with
    | [] => Ffalse 
    | a :: l => a ∨ listOr l 
    end. 

  Fixpoint listAnd (l : list formula) := match l with 
    | [] => Ftrue
    | a :: l => a ∧ listAnd l
    end.  

  Lemma listOr_sat_iff l a : satisfies a (listOr l) <-> exists f, f el l /\ satisfies a f. 
  Proof. 
    induction l; cbn. 
    - unfold satisfies. cbn. split; [congruence | intros (f & [] & _)]. 
    - unfold satisfies. rewrite evalFormula_or_iff, IHl. split.
      + intros [ H | (f & H1 & H2)]; [exists a0; eauto | exists f; eauto].  
      + intros (f & [-> | H1] & H2); [now left | right; exists f; eauto]. 
  Qed.

  Lemma listAnd_sat_iff l a : satisfies a (listAnd l) <-> forall f, f el l -> satisfies a f. 
  Proof. 
    induction l; cbn. 
    - unfold satisfies. cbn. split; [intros _ f [] | intros _; easy]. 
    - unfold satisfies. rewrite evalFormula_and_iff, IHl. split.
      + intros (H1 & H2) f [-> | H3%H2]; eauto.
      + intros H; split; [ apply H | intros f H1; apply H]; eauto.
  Qed.

  (** generate the list of values assigned to the variables by a in range [lower, lower + len) *)
  Fixpoint explicitAssignment a lower len := 
    match len with
      | 0 => [] 
      | S len => explicitAssignment a lower len ++ [list_in_decb Nat.eqb a (lower + len)]
    end. 

  Lemma explicitAssignment_length a lower len : |explicitAssignment a lower len| = len. 
  Proof. 
    revert lower. induction len; intros; cbn. 
    - reflexivity. 
    - rewrite app_length, IHlen. now cbn.
  Qed. 

  Lemma explicitAssignment_nth a lower len k : 
     k < len -> nth_error (explicitAssignment a lower len) k = Some (evalVar a (lower + k)). 
  Proof. 
    intros. induction len. 
    - lia. 
    - cbn. destruct (le_lt_dec len k).
      + assert (len = k) as <- by lia.
        rewrite nth_error_app2; rewrite explicitAssignment_length; [ rewrite Nat.sub_diag; cbn | lia]. easy.
      + rewrite nth_error_app1; [ | rewrite explicitAssignment_length; easy ]. now apply IHlen. 
  Qed. 

  Lemma explicitAssignment_app a l1 len1 len2: explicitAssignment a l1 (len1 + len2) = explicitAssignment a l1 len1 ++ explicitAssignment a (l1 + len1) len2. 
  Proof. 
    induction len2; cbn. 
    - now rewrite Nat.add_0_r, app_nil_r. 
    - rewrite Nat.add_succ_r. cbn. rewrite IHlen2, app_assoc. easy. 
  Qed. 

  (*from an explicit assignment, we can go back to an assignment *)
  (*s is the variable index at which the explicit assignment is starting *)
  Lemma expAssgn_to_assgn s b : 
    {a & forall x, x el a <-> x >= s /\ nth_error b (x - s) = Some true}.
  Proof. 
    revert s. 
    induction b; cbn; intros. 
    - exists []. intros x. destruct (x-s); cbn; easy. 
    - destruct (IHb (S s)) as (assgn & IH). destruct a. 
      + exists (s :: assgn). intros x. split.
        * intros [-> | H]; [ rewrite Nat.sub_diag; easy | ]. 
          apply IH in H as (H1 & H2). split; [ lia | ]. 
          now eapply nth_error_step.
        * intros (H1 & H2). apply le_lt_eq_dec in H1 as [H1 | ->].
          -- right. apply IH. split; [ lia | ]. eapply nth_error_step, H2. lia. 
          -- now left. 
      + exists assgn. intros x. split.
        * intros (H1 & H2)%IH. split; [ lia | rewrite <- nth_error_step; easy]. 
        * intros (H1 & H2). apply le_lt_eq_dec in H1 as [H1 | ->]. 
          -- apply IH. split; [ lia | ]. apply nth_error_step in H2; easy.  
          -- rewrite Nat.sub_diag in H2. cbn in H2. congruence. 
  Qed. 

  Lemma expAssgn_to_assgn_inv a s b : (forall x, x el a <-> x >= s /\ nth_error b (x -s) = Some true) 
    -> explicitAssignment a s (|b|) = b. 
  Proof. 
    intros. apply list_eq_nth_error. split; [ apply explicitAssignment_length | ].
    intros k H1. rewrite explicitAssignment_length in H1. 
    rewrite explicitAssignment_nth by apply H1. 
    unfold evalVar. destruct list_in_decb eqn:H2. 
    - apply list_in_decb_iff in H2; [ | intros; now rewrite Nat.eqb_eq ].
      apply H in H2 as (_ & H2). now replace (s + k - s) with k in H2 by lia.
    - apply list_in_decb_iff' in H2; [ | intros; now rewrite Nat.eqb_eq].
      (*we do a case analysis, thus we do not need XM *)
      destruct (nth_error b k) eqn:H3. 
      + destruct b0; [ | easy]. exfalso; apply H2. apply H. 
        replace (s + k - s) with k by lia. easy.
      + apply nth_error_none in H3. lia.
  Qed.

  (*we define what it means for a formula to encode a predicate *)
  Definition predicate := list bool -> Prop. 
  Implicit Type (p : predicate).
  Definition encodesPredicateAt (start : nat) (l : nat) f p:= forall a, satisfies a f <-> p (explicitAssignment a start l). 

  (*given an explicitAssignment, we can project out a range of variables, given by [start, start+len) *)
  Definition projVars start len (l : list bool) := firstn len (skipn start l). 

  Lemma projVars_length l s m : |l| >= (s + m) -> |projVars s m l| = m. 
  Proof. 
    intros. unfold projVars. rewrite firstn_length. rewrite skipn_length. lia. 
  Qed. 

  Lemma projVars_app1 l1 l2 m : |l1| = m -> projVars 0 m (l1 ++ l2) = l1.
  Proof. 
    intros. unfold projVars. cbn. rewrite firstn_app. subst. 
    now rewrite Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
  Qed. 

  Lemma projVars_app2 l1 l2 u m : |l1| = u -> projVars u m (l1 ++ l2) = projVars 0 m l2. 
  Proof. 
    intros. unfold projVars. rewrite skipn_app; [ | easy]. now cbn. 
  Qed. 

  Lemma projVars_app3 l1 l2 u1 u2 m : |l1| = u1 -> projVars (u1 + u2) m (l1 ++ l2) = projVars u2 m l2. 
  Proof. 
    intros. unfold projVars. erewrite skipn_add; [ easy| lia]. 
  Qed. 

  Lemma projVars_all l m : m = |l| -> projVars 0 m l = l. 
  Proof.
    intros. unfold projVars. cbn. rewrite H. apply firstn_all. 
  Qed. 

  Lemma projVars_comp l1 l2 len1 len2 m: projVars l1 len1 (projVars l2 len2 m) = projVars (l1 + l2) (min len1 (len2 - l1)) m. 
  Proof. 
    unfold projVars. intros. 
    rewrite skipn_firstn_skipn. rewrite firstn_firstn. reflexivity. 
  Qed. 

  Lemma projVars_add s l1 l2 m : projVars s (l1 + l2) m = projVars s l1 m ++ projVars (s + l1) l2 m. 
  Proof. 
    unfold projVars. rewrite firstn_add, skipn_skipn. now rewrite Nat.add_comm. 
  Qed.

  Lemma projVars_length_le start l m: |projVars start l m| <= |m|. 
  Proof. 
    unfold projVars. 
    rewrite firstn_length. rewrite skipn_length. lia. 
  Qed. 

  Lemma projVars_length_le2 start l m : |projVars start l m| <= l.
  Proof. 
    unfold projVars. rewrite firstn_length, skipn_length. lia. 
  Qed. 

  Lemma projVars_in_ge start l m : start <= |m| -> projVars start (|l|) m = l -> |m| >= start + |l|. 
  Proof. 
    intros H0 H. unfold projVars in H. rewrite <- H, firstn_length, skipn_length. lia.
  Qed. 

  (*encodings of two predicates can be combined*)
  Definition combinedLength start1 start2 l1 l2 := max (start1 +l1) (start2 + l2) - min start1 start2. 
  Definition combinedStart start1 start2 := min start1 start2. 

  (** from the combined assignment for the combination of two formulas, we can restore an assignment for the first formula *)
  Lemma projVars_combined1 s1 s2 l1 l2 a: explicitAssignment a s1 l1 = projVars (s1 - combinedStart s1 s2) l1 (explicitAssignment a (combinedStart s1 s2) (combinedLength s1 s2 l1 l2)).
  Proof. 
    unfold projVars. 
    apply list_eq_nth_error. split. 
    - rewrite explicitAssignment_length. unfold combinedStart, combinedLength. rewrite firstn_length. 
      rewrite skipn_length. rewrite explicitAssignment_length. lia. 
    - intros. rewrite explicitAssignment_length in H. unfold combinedStart, combinedLength. 
      rewrite nth_error_firstn; [ | apply H].  
      rewrite nth_error_skipn. rewrite !explicitAssignment_nth; [easy | lia | lia]. 
  Qed. 

  (*...and for the second *)
  Lemma projVars_combined2 s1 s2 l1 l2 a: explicitAssignment a s2 l2 = projVars (s2 - combinedStart s1 s2) l2 (explicitAssignment a (combinedStart s1 s2) (combinedLength s1 s2 l1 l2)). 
  Proof. 
    unfold combinedStart, combinedLength. rewrite Nat.min_comm. rewrite Nat.max_comm. apply projVars_combined1. 
  Qed. 

  (*two formulae can be combined via ∧ *)
  Lemma encodesPredicate_and start1 start2 l1 l2 f1 f2 p1 p2 : 
    encodesPredicateAt start1 l1 f1 p1 -> encodesPredicateAt start2 l2 f2 p2 
    -> encodesPredicateAt (combinedStart start1 start2) (combinedLength start1 start2 l1 l2) (f1 ∧ f2) (fun m => (p1 (projVars (start1 - combinedStart start1 start2) l1 m) /\ p2 (projVars (start2 - combinedStart start1 start2) l2 m))). 
  Proof. 
    intros G1 G2. 
    intros a. split; intros H. 
    + apply evalFormula_and_iff in H as (H1 & H2). 
      rewrite <- projVars_combined1, <- projVars_combined2. 
      unfold encodesPredicateAt in G1, G2. rewrite <- G1, <- G2. easy. 
    + rewrite <- projVars_combined1, <- projVars_combined2 in H. 
      unfold satisfies. apply evalFormula_and_iff. 
      split; [apply G1, H | apply G2, H]. 
  Qed. 

  (*...and with ∨*)
  Lemma encodesPredicate_or start1 start2 l1 l2 f1 f2 p1 p2 : 
    encodesPredicateAt start1 l1 f1 p1 -> encodesPredicateAt start2 l2 f2 p2 
    -> encodesPredicateAt (combinedStart start1 start2) (combinedLength start1 start2 l1 l2) (f1 ∨ f2) (fun m => (p1 (projVars (start1 - combinedStart start1 start2) l1 m) \/ p2 (projVars (start2 - combinedStart start1 start2) l2 m))).
  Proof. 
    intros G1 G2. 
    intros a. split; intros H. 
    + apply evalFormula_or_iff in H as [H | H]; 
      rewrite <- projVars_combined1, <- projVars_combined2;
      unfold encodesPredicateAt in G1, G2; rewrite <- G1, <- G2; easy. 
    + rewrite <- projVars_combined1, <- projVars_combined2 in H. 
      unfold satisfies. apply evalFormula_or_iff. 
      destruct H as [H | H]; [left; apply G1, H | right; apply G2, H].
  Qed. 

  (** next, we do the same for lists of formulas where the individual formulas are placed in a regular pattern starting at an index s with an offset step *)
  Fixpoint tabulate_step (step s n : nat) := 
    match n with 
      | 0 => [] 
      | S n => s :: tabulate_step step (step + s) n
    end. 
  Definition tabulate_formula s step n (t : nat -> formula) := map t (tabulate_step step s n). 

  Lemma in_tabulate_step_iff step s n x : x el tabulate_step step s n <-> exists i, i < n /\ x = s + step * i. 
  Proof. 
    revert s. induction n; cbn; intros.
    - split; [easy | intros (i & H & _); lia ].
    - split. 
      + intros [-> | H%IHn]; [exists 0; lia | ].
        destruct H as (i & H1 & ->). exists (S i). lia. 
      + intros (i & H1 & H2). 
        destruct i. 
        * now left. 
        * right. apply IHn. exists i. lia. 
  Qed.

  Lemma in_tabulate_formula_iff s step n t f: 
    f el tabulate_formula s step n t <-> exists i, i < n /\ f = t (s + step * i). 
  Proof. 
    unfold tabulate_formula. rewrite in_map_iff. setoid_rewrite in_tabulate_step_iff. 
    split. 
    - intros (x & <- & (i & H1 & ->)). exists i. eauto.
    - intros (i & H1 & ->). exists (s + step * i). eauto.
  Qed.

  Fact projVars_mul_offset a s step i l n: i < n -> explicitAssignment a (s + step * i) l = projVars (step * i) l (explicitAssignment a s (step * n + (l - step))). 
  Proof. 
    intros H. apply list_eq_nth_error. 
    split. 
    - rewrite projVars_length; rewrite !explicitAssignment_length; [lia | ]. nia.
    - rewrite explicitAssignment_length. intros k H1. 
      unfold projVars. rewrite nth_error_firstn by apply H1. 
      rewrite nth_error_skipn. rewrite !explicitAssignment_nth. 
      + easy.
      + nia. 
      + apply H1. 
  Qed.

  (* t : length -> start -> formula *)
  Lemma encodesPredicate_listOr_tabulate l (t : nat -> formula) p : 
    (forall s, encodesPredicateAt s l (t s) p)
    -> forall s step n, encodesPredicateAt s (step * n + (l - step)) (listOr (tabulate_formula s step n t)) (fun m => exists i, i < n /\ p (projVars (step * i) l m)). 
  Proof. 
    (* we have to add l - step for the case that l > step; this is the case when creating the rewrite windows, for instance *)
    intros H s step n. unfold encodesPredicateAt. intros a. 
    rewrite listOr_sat_iff. setoid_rewrite in_tabulate_formula_iff. 
    split.
    - intros (f & (i & H1 & ->) & H2). exists i. split; [easy | ]. 
      specialize (H (s + step * i)). apply H in H2. 
      rewrite <- projVars_mul_offset by apply H1. apply H2. 
    - intros (i & H1 & H2). exists (t (s + step * i)). split. 
      + exists i. eauto.
      + apply H. erewrite projVars_mul_offset by apply H1. apply H2. 
  Qed.

  Lemma encodesPredicate_listAnd_tabulate l (t : nat -> formula) p : 
    (forall s, encodesPredicateAt s l (t s) p)
    -> forall s step n, encodesPredicateAt s (step * n + (l - step)) (listAnd (tabulate_formula s step n t)) (fun m => forall i, i < n -> p (projVars (step * i) l m)). 
  Proof. 
    intros H s step n. unfold encodesPredicateAt. intros a. 
    rewrite listAnd_sat_iff. setoid_rewrite in_tabulate_formula_iff. 
    split.
    - intros H1 i H2. rewrite <- projVars_mul_offset by apply H2. 
      apply H, H1. exists i; eauto. 
    - intros H1 f (i & H2 & ->). apply H. 
      erewrite projVars_mul_offset by apply H2. now apply H1. 
  Qed.

  (** similarly, we can combine multiple formulas at the same position *)
  Lemma encodesPredicate_listOr_map (X : Type) s l (es : list X) (p : X -> predicate) (f : X -> formula) : 
    (forall e, e el es -> encodesPredicateAt s l (f e) (p e))
    -> encodesPredicateAt s l (listOr (map f es)) (fun m => exists e, e el es /\ p e m). 
  Proof. 
    intros H. unfold encodesPredicateAt. intros a. 
    rewrite listOr_sat_iff. setoid_rewrite in_map_iff. 
    split. 
    - intros (fo & (x & <- & Hel) & H1). apply (H _ Hel) in H1. eauto.
    - intros (x & Hel & H1). apply (H _ Hel) in H1. exists (f x). 
      split; eauto.
  Qed.

  Lemma encodesPredicate_listAnd_map (X : Type) s l (es : list X) (p : X -> predicate) (f : X -> formula) : 
    (forall e, e el es -> encodesPredicateAt s l (f e) (p e))
    -> encodesPredicateAt s l (listAnd (map f es)) (fun m => forall e, e el es -> p e m). 
  Proof. 
    intros H. unfold encodesPredicateAt. intros a. 
    rewrite listAnd_sat_iff. setoid_rewrite in_map_iff. 
    split. 
    - intros H1 e Hel. apply (H _ Hel). apply H1. eauto. 
    - intros H1 fo (x & <- & Hel). apply (H _ Hel). now apply H1. 
  Qed.

  (*encoding of single literals *)
  Definition encodeLiteral v (sign : bool) : formula := if sign then v else ¬ v. 

  Lemma encodeLiteral_correct v sign : forall a, satisfies a (encodeLiteral v sign) <-> evalVar a v = sign. 
  Proof. 
    intros. unfold satisfies, encodeLiteral. destruct sign; cbn; [ tauto |simp_bool; tauto ]. 
  Qed. 

  Lemma encodeLiteral_encodesPredicate v sign : encodesPredicateAt v 1 (encodeLiteral v sign) (fun l => l = [sign]). 
  Proof. 
    intros. split; intros. 
    + apply encodeLiteral_correct in H. specialize (explicitAssignment_length a v 1) as H1. 
      assert (0 < 1) as H2 by lia. 
      specialize (@explicitAssignment_nth a v 1 0 H2) as H3. 
      destruct explicitAssignment as [ | s l]; cbn in H1; [ congruence | destruct l; [ | cbn in H1; congruence]]. 
      cbn in H3. now inv H3. 
    + apply encodeLiteral_correct. assert (0 < 1) as H2 by lia.
      specialize (@explicitAssignment_nth a v 1 0 H2) as H1. 
      rewrite H in H1; cbn in H1. now inv H1. 
  Qed. 

  (*for predicates which are equivalent, encoding is equivalent *)
  Lemma encodesPredicateAt_extensional s l f p1 p2 : (forall m, |m| = l -> p1 m <-> p2 m) -> encodesPredicateAt s l f p1 <-> encodesPredicateAt s l f p2. 
  Proof. 
    intros. unfold encodesPredicateAt. split; intros; specialize (H (explicitAssignment a s l) (explicitAssignment_length _ _ _)); [now rewrite <- H | now rewrite H]. 
  Qed. 

  (*a procedure that tries to simplify parts of the terms introduced by the combination lemmas for ∧ and ∨ *)
  Ltac encodesPredicateAt_comp_simp H := 
    unfold combinedStart, combinedLength in H;
    try (rewrite Nat.min_l in H by nia); try (rewrite Nat.min_r in H by nia);
    try (rewrite Nat.max_l in H by nia); try (rewrite Nat.max_r in H by nia);
    try rewrite !Nat.sub_diag in H.
  
  (*encoding of lists *)
  Fixpoint encodeListAt (startA : nat) (l : list bool) :=
    match l with 
    | [] => Ftrue
    | x :: l => (encodeLiteral startA x) ∧ (encodeListAt (1 + startA) l)
    end. 

  Lemma encodeListAt_encodesPredicate start l : encodesPredicateAt start (|l|) (encodeListAt start l) (fun m => m = l).
  Proof. 
    revert start. induction l; intros. 
    - cbn. split; [eauto | ]. unfold satisfies. intros; easy. 
    - cbn. specialize (@encodesPredicate_and start (S start) 1 (|l|) (encodeLiteral start a) (encodeListAt (S start) l) _ _ (encodeLiteral_encodesPredicate start a) (IHl (S start))) as H1.
      encodesPredicateAt_comp_simp H1. 
      replace (S start - start) with 1 in H1 by lia. 
      replace (S start + (|l|) - start) with (S (|l|)) in H1 by lia.
      eapply encodesPredicateAt_extensional; [ | apply H1]. 
      intros m H0. unfold projVars. 
      destruct m; cbn; [split; intros; easy | ]. 
      split. 
      + intros H. inv H. now rewrite firstn_all.
      + intros (H2 & H3). inv H2. f_equal. apply Nat.succ_inj in H0. now apply firstn_all_inv. 
  Qed. 

  (** encoding of windows *)
  (** startA is the position at which the premise is placed, startB the position at which the conclusion is placed *)
  Definition encodeWindowAt (startA startB : nat) (win : PRWin bool) := encodeListAt startA (prem win) ∧ encodeListAt startB (conc win). 

  Lemma encodeWindowAt_encodesPredicate start len win : 
    win el windows -> encodesPredicateAt start (len + width) (encodeWindowAt start (start + len) win) (fun m => projVars 0 width m = prem win /\ projVars len width m = conc win). 
  Proof. 
    intros H0. 
    specialize (encodesPredicate_and (encodeListAt_encodesPredicate start (prem win)) (encodeListAt_encodesPredicate (start + len) (conc win))) as H. 
    destruct A as (_ & _ & _ & A0 & A1 & _). apply A1 in H0 as (H0 & H0').
    encodesPredicateAt_comp_simp H. 
    rewrite !H0 in H. rewrite !H0' in H.
    replace (start + len + width - start) with (len + width) in H by lia. 
    replace (start + len - start) with len in H by lia.
    unfold encodeWindowAt. eapply encodesPredicateAt_extensional; [ | apply H].
    tauto.
  Qed.

  (** encoding of the disjunction of all windows of the BinaryPR instance  *)
  Definition encodeWindowsAt (startA startB : nat) := listOr (map (encodeWindowAt startA startB) windows). 

  Lemma encodeWindowsAt_encodesPredicate len start : len >= width -> encodesPredicateAt start (len + width) (encodeWindowsAt start (start + len)) (fun m => exists win, win el windows /\ projVars 0 width m = prem win /\ projVars len width m = conc win). 
  Proof. 
    intros F0. apply encodesPredicate_listOr_map. 
    intros win Hel. apply encodeWindowAt_encodesPredicate, Hel. 
  Qed.

  (*encoding of all windows of one line of the tableau *)
  (*we only need to place a window every offset fields, but subtracting offset isn't structurally recursive *)
  (*therefore we use a stepindex (initalise to the same value as l) *)
  Fixpoint encodeWindowsInLine' (stepindex l : nat) (startA startB : nat) := 
    if l <? width then Ftrue 
                  else match stepindex with 
                    | 0 => Ftrue
                    | S stepindex => encodeWindowsAt startA startB ∧ encodeWindowsInLine' stepindex (l - offset) (startA + offset) (startB + offset)
                    end.

  Lemma encodeWindowsInLineP_stepindex_monotone' index startA startB : forall n, n <= index -> encodeWindowsInLine' index n startA startB = encodeWindowsInLine' (S index) n startA startB. 
  Proof. 
    destruct A as (A1 & A2 & _).
    revert startA startB.
    induction index; intros. 
    - unfold encodeWindowsInLine'. assert (n = 0) as -> by lia. cbn; destruct width; [ lia | easy ].
    - unfold encodeWindowsInLine'. destruct (Nat.ltb n width); [ easy | ]. fold encodeWindowsInLine'. 
      erewrite IHindex by lia. easy. 
  Qed. 

  Lemma encodeWindowsInLineP_stepindex_monotone index index' startA startB : index' >= index -> encodeWindowsInLine' index index startA startB = encodeWindowsInLine' index' index startA startB. 
  Proof. 
    intros. revert index H.
    induction index'; intros. 
    - assert (index = 0) as -> by lia. easy.
    - destruct (nat_eq_dec (S index') index). 
      + now rewrite e.
      + assert (index' >= index) as H1 by lia. rewrite <- encodeWindowsInLineP_stepindex_monotone' by lia. now apply IHindex'.
  Qed.

  Lemma encodeWindowsInLineP_encodesPredicate start l : l <= llength -> (exists k, l = k * offset) -> encodesPredicateAt start (l + llength) (encodeWindowsInLine' l l start (start + llength)) (fun m => valid offset width windows (projVars 0 l m) (projVars llength l m)). 
  Proof. 
    intros A0.
    (*need strong induction *)
    destruct A as (A1 & A4 & A2 & A5 & A7 & A3). 
    revert start A0.  
    apply complete_induction with (x := l). clear l. intros l IH. intros. 

    (*case analysis on the stepindex *)
    destruct l.
    - (*we use that width > 0 *)
      unfold encodeWindowsInLine'. rewrite (proj2 (Nat.ltb_lt _ _) A1). 
      intros a. split; [ intros; constructor | intros _; unfold satisfies; eauto].  
    - destruct (le_lt_dec width (S l)). 
      + assert (~ (S l) < width) as H3%Nat.ltb_nlt by lia. cbn -[projVars]; setoid_rewrite H3. 
        destruct offset as [ | offset]; [ lia | ].
        (* we use the IH for l - offset *)
 
        assert (S l - S offset < S l) as H1 by lia. apply IH with (start := start + S offset) in H1. 2: nia. 
        2: { destruct H as (k & H). destruct k; [ lia | ]. exists k. lia. }
        clear H IH. 
        assert (llength >= width) as H0 by lia.
        apply (encodeWindowsAt_encodesPredicate start) in H0. 

        specialize (encodesPredicate_and H0 H1) as H2. clear H1 H0.
        encodesPredicateAt_comp_simp H2. 

        replace (start + S offset + llength) with (start + llength + S offset) in H2 by lia. 
        replace (start + S offset + (S l - S offset + llength) - start) with (S (l + llength)) in H2. 
        2: { destruct A2 as (? & A2 & A6). nia. }
        
        rewrite encodeWindowsInLineP_stepindex_monotone with (index' := l) in H2; [ | lia].
        eapply encodesPredicateAt_extensional; [ | apply H2].

        clear H2 H3. 
        intros. 
        destruct A2 as (k & A2 & A2').
        assert (S l = S offset + (S l - S offset)) as H0 by nia.  
        (*we now show the two directions of the equivalence, which is a bit technical*)
        split; intros. 
        * rewrite H0 in H1. clear H0. 
          rewrite !projVars_add in H1. inv H1.
          (*the first two cases are contradictory *)
          2 : { exfalso. apply list_eq_length in H0. rewrite !app_length in H0. rewrite !projVars_length in H0; [ | easy | easy]. nia. }
          1: { exfalso. apply list_eq_length in H3. rewrite !app_length in H3. rewrite projVars_length in H3; [ | cbn; nia]. cbn in H3. lia. } 

          apply app_eq_length in H2 as (-> & ->); [ | rewrite projVars_length; [easy | nia] ].
          apply app_eq_length in H0 as (-> & ->); [ | rewrite projVars_length; [easy | nia]]. 
          split.
          -- exists win. rewrite !projVars_comp; cbn. rewrite !Nat.min_l by lia. 
             rewrite !Nat.add_0_r.
             clear H3 H4 H5. rewrite <- !projVars_add in H7. 
             replace (S offset + (l - offset)) with (width + (S l - width)) in H7 by nia. 
             rewrite !projVars_add in H7.
             split; [ easy | split ]; apply A7 in H6 as (H6 & H6'). 
             ++ destruct H7 as ((b & H7) & _). eapply app_eq_length in H7; [ easy| rewrite projVars_length; easy ]. 
             ++ destruct H7 as (_ & (b & H7)). eapply app_eq_length in H7; [ easy | rewrite projVars_length; easy].
          -- clear H7 H6. 
             rewrite !projVars_comp. replace (start + S offset - start) with (S offset) by lia. rewrite !Nat.min_l by lia. 
             apply H3. 
        * (*other direction of the equivalence *)
          destruct H1 as (H1 & H2).  
          rewrite H0, !projVars_add. 
          destruct H1 as (win & H1 & F1 & F2). 
          econstructor 3. 
          -- rewrite !projVars_comp in H2. rewrite !Nat.min_l in H2 by lia.
             replace (start + S offset - start) with (S offset) in H2 by lia. 
             apply H2. 
          -- rewrite projVars_length; lia. 
          -- rewrite projVars_length; lia. 
          -- clear H2. apply H1. 
          -- clear H2. rewrite <- !projVars_add. 
             replace (S offset + (S l - S offset)) with (width + (S l - width)) by lia. 
             rewrite !projVars_add. 
             rewrite projVars_comp in F1, F2. rewrite !Nat.min_l in F1, F2 by lia. 
             rewrite Nat.add_0_r in F2; cbn in F1, F2.
             rewrite F1, F2. split; unfold prefix; eauto. 
    + (*the case where the remaining string is too short for a rewrite window to hold - validity holds vacuously *)
      clear IH. assert ( (S l) < width) as H3%Nat.ltb_lt by lia. cbn -[projVars]; setoid_rewrite H3.
      intros a; split; [intros _ | ]. 
      * destruct H as (k & H). eapply valid_vacuous. 
        -- rewrite !projVars_length; [easy | rewrite explicitAssignment_length; lia | rewrite explicitAssignment_length; lia]. 
        -- rewrite projVars_length; [ easy | rewrite explicitAssignment_length; lia]. 
        -- rewrite projVars_length; [ | rewrite explicitAssignment_length; lia]. 
           (*here we need the assumption that l is a multiple of offset *)
           apply H. 
      * intros _; easy. 
  Qed.

  (** the above construction specialized to the setting we need: the conclusion starts exactly one line after the premise *)
  Definition encodeWindowsInLine start := encodeWindowsInLine' llength llength start (start + llength). 
  Lemma encodeWindowsInLine_encodesPredicate start : encodesPredicateAt start (llength + llength) (encodeWindowsInLine start) (fun m => valid offset width windows (projVars 0 llength m) (projVars llength llength m)). 
  Proof. 
    unfold encodeWindowsInLine.
    apply (@encodeWindowsInLineP_encodesPredicate start llength); [easy | apply A].
  Qed. 

  (*encoding of windows in all lines of the tableau *)
  Definition encodeWindowsInAllLines := listAnd (tabulate_formula 0 llength steps encodeWindowsInLine). 
  Lemma encodeWindowsInAllLines_encodesPredicate : encodesPredicateAt 0 ((S steps) * llength) encodeWindowsInAllLines 
    (fun m => (forall i, 0 <= i < steps -> valid offset width windows (projVars (i * llength) llength m) (projVars (S i * llength) llength m))). 
  Proof. 
    eapply encodesPredicateAt_extensional. 
    2: { unfold encodeWindowsInAllLines. 
         replace (S steps * llength) with (llength * steps + ((llength + llength) -llength)) by lia. 
         apply encodesPredicate_listAnd_tabulate. intros s. apply encodeWindowsInLine_encodesPredicate. 
    } 
    intros m Hlen. split. 
    - intros H i H1. specialize (H i ltac:(lia)). 
      rewrite !projVars_comp. rewrite !Nat.min_l by lia. cbn. rewrite Nat.mul_comm at 1. 
      replace (llength + llength * i) with (S i * llength) by lia. apply H. 
    - intros H i (_ & H1). specialize (H i H1). rewrite !projVars_comp in H. rewrite !Nat.min_l in H by lia. 
      cbn in H. cbn. rewrite Nat.mul_comm. apply H. 
  Qed.

  (*encode the substring constraint for a single string s *)
  (*should only be called for s satisfying |s| > 0; for s = nil, the breaking condition does not work as intended*)
  (*in principle, this is not a problem as the resulting formula is still equivalent to the desired formula, but this breaks monotonicity*)
  Fixpoint encodeSubstringInLine' (s : list bool) (stepindex l : nat) (start : nat) := 
    if l <? |s| then Ffalse
                  else match stepindex with 
                    | 0 => (match s with [] => Ftrue | _ => Ffalse end)
                    | S stepindex => encodeListAt start s ∨ encodeSubstringInLine' s stepindex (l - offset) (start + offset) 
                    end.

  (*the requirement |s| > 0 is needed for monotonicity *)
  Lemma encodeSubstringInLineP_stepindex_monotone' s index start : forall n, |s| > 0 -> n <= index -> encodeSubstringInLine' s index n start = encodeSubstringInLine' s (S index) n start. 
  Proof. 
    destruct A as (A1 & A2 & _).
    revert start.
    induction index; intros. 
    - unfold encodeSubstringInLine'. assert (n = 0) as -> by lia. cbn; destruct s; [ cbn in *; lia | easy ]. 
    - unfold encodeSubstringInLine'. destruct (Nat.ltb n (|s|)); [ easy | ]. fold encodeSubstringInLine'. 
      erewrite IHindex by lia. easy. 
  Qed. 

  Lemma encodeSubstringInLineP_stepindex_monotone s index1 index2 start : 
    |s| > 0 -> index2 >= index1 -> encodeSubstringInLine' s index1 index1 start = encodeSubstringInLine' s index2 index1 start.
  Proof. 
    intros. revert index1 H0. 
    induction index2; intros.
    - assert (index1 = 0) as -> by lia. easy.
    - destruct (nat_eq_dec (S index2) index1). 
      + now rewrite e.
      + assert (index2 >= index1) as H1 by lia. rewrite <- encodeSubstringInLineP_stepindex_monotone' by lia. now apply IHindex2.
  Qed. 

  Lemma encodeSubstringInLineP_encodesPredicate s start l : |s| > 0 -> l <= llength 
    -> (exists k, l = k * offset) -> encodesPredicateAt start l (encodeSubstringInLine' s l l start) (fun m => (exists k, k * offset <= l /\ projVars (k * offset) (|s|) m = s)). 
  Proof. 
    intros F.
    (*need strong induction *)
    destruct A as (A1 & A4 & A2 & A5 & A7 & A3). 
    revert start.  
    apply complete_induction with (x := l). clear l. intros l IH. intros. 

    destruct l.
    - cbn -[projVars]. destruct s; cbn -[projVars]. 
      + (*trivially true because of our requirement that |s| > 0*) cbn in F; easy. 
      + (*trivially false *)
        intros a; split.
        * unfold satisfies; cbn; congruence. 
        * intros (k & H1 & H2). destruct k; [clear H1 | nia]. cbn in H2. congruence. 
    - destruct (le_lt_dec (|s|) (S l)). 
      + (*in this case, we can apply the IH*)
        assert (~ (S l) < (|s|)) as H3%Nat.ltb_nlt by lia. cbn -[projVars]; setoid_rewrite H3. 
        destruct offset as [ | offset]; [ lia | ].
        (* we use the IH for l - offset *)
 
        assert (S l - S offset < S l) as H1 by lia. apply IH with (start := start + S offset) in H1; [ | nia | ]. 
        2: { destruct H0 as (k & H0). destruct k; [ lia | ]. exists k. lia. }
        clear H IH. 
        specialize (encodeListAt_encodesPredicate start s) as H2.
        specialize (encodesPredicate_or H2 H1) as H. clear H1 H2 H3.

        encodesPredicateAt_comp_simp H.
        destruct H0 as (k & H0).
        assert (k > 0) by nia. (*a hint for nia - without it, the following replace will not work *)
        replace (start + S offset + (S l - S offset) - start) with (S l) in H by nia.
        replace (start + S offset - start) with (S offset) in H by lia.

        rewrite encodeSubstringInLineP_stepindex_monotone with (index2 := l) in H; [ | apply F| lia].
        eapply encodesPredicateAt_extensional; [ | apply H]. clear H.
        intros. split.
        * intros (k0 & H2 & H3). 
          destruct k0; [ now left | right]. 
          exists k0. split; [ easy | ]. 
          rewrite projVars_comp. 
          cbn [Nat.mul] in H3.  
          enough (|s| <= l - offset - k0 * S offset).
          { rewrite Nat.min_l by lia. rewrite Nat.add_comm. apply H3. }
          apply projVars_in_ge in H3; nia.
        * intros H3. 
          destruct H3 as [H3 | (k0 & H3 & H4)]; [ exists 0; cbn; easy | ]. 
          exists (S k0). split; [ nia | ].
          rewrite projVars_comp in H4. 

          enough (|s| <= l - offset - k0 * S offset).
          { rewrite Nat.min_l in H4 by lia. cbn [Nat.mul]. rewrite <- Nat.add_comm. apply H4. }
          apply list_eq_length in H4. 
          match type of H4 with (|projVars ?a ?b ?c| = _) => specialize (projVars_length_le2 a b c) as H2 end.
          lia. 
    + (*the case where the remaining string is too short in order to place the substring constraint *)
      clear IH. assert ( (S l) < (|s|)) as H3%Nat.ltb_lt by lia. cbn -[projVars]; setoid_rewrite H3.
      intros a. unfold satisfies; cbn [negb evalFormula].
      split; [congruence | ]. 
      intros (k & H1 & H2). apply list_eq_length in H2. specialize (projVars_length_le (k * offset) (|s|) (explicitAssignment a start (S l))) as H4.
      rewrite explicitAssignment_length in H4. lia. 
  Qed.

  (*we now have to do a case analysis: if the substring which has to be checked is non-empty, we use the function defined above *)
  (*otherwise, the empty string is trivially a substring *)
  Definition encodeSubstringInLine s start l := match s with [] => Ftrue | _ => encodeSubstringInLine' s l l start end.

  Lemma encodeSubstringInLine_encodesPredicate s start l : l <= llength -> (exists k, l = k * offset) -> encodesPredicateAt start l (encodeSubstringInLine s start l) (fun m => (exists k, k * offset <= l /\ projVars (k * offset) (|s|) m = s)). 
  Proof. 
    intros. unfold encodeSubstringInLine. destruct s eqn:H1. 
    - unfold satisfies. cbn. intros; split.
      + intros _. exists 0; cbn; firstorder.
      + intros _. reflexivity. 
    - apply encodeSubstringInLineP_encodesPredicate; cbn; easy.
  Qed. 

  (** the final constraint now is a disjunction over all given substrings *)
  Definition encodeFinalConstraint (start : nat) := listOr (map (fun s => encodeSubstringInLine s start llength) final). 

  Lemma encodeFinalConstraint_encodesPredicate start : encodesPredicateAt start llength (encodeFinalConstraint start) (fun m => satFinal offset llength final m).
  Proof. 
    unfold encodeFinalConstraint. 
    eapply encodesPredicateAt_extensional; [ | apply encodesPredicate_listOr_map].
    2: { intros. apply encodeSubstringInLine_encodesPredicate; [easy | apply A]. }
    intros m H4. split. 
    - intros (subs & k & H1 & H2 & H3).
      exists subs. split; [ apply H1 | ]. 
      exists k. split; [ easy | ]. 
      destruct H3 as (b & H3). unfold projVars. rewrite H3. 
      rewrite firstn_app, firstn_all, Nat.sub_diag; cbn. now rewrite app_nil_r. 
    - intros (subs & H1 & (k & H2 & H3)).
      exists subs, k. split; [apply H1 | split; [ apply H2 | ]].
      unfold prefix. unfold projVars in H3. 
      setoid_rewrite <- firstn_skipn with (l := skipn (k * offset) m) (n:= |subs|).
      setoid_rewrite H3. eauto.
  Qed. 

  Definition encodeFinalConstraint' := encodeFinalConstraint (steps *llength).
  Lemma encodeFinalConstraint_encodesPredicate' : encodesPredicateAt (steps * llength) llength encodeFinalConstraint' (fun m => satFinal offset llength final m). 
  Proof. 
    apply encodeFinalConstraint_encodesPredicate. 
  Qed.

  (*encoding of the whole tableau: the initial constraint, window constraints and the final constraint are combined conjunctively *)
  Definition encodeTableau := encodeListAt 0 init ∧ encodeWindowsInAllLines ∧ encodeFinalConstraint'.
  Lemma encodeTableau_encodesPredicate : 
    encodesPredicateAt 0 (S steps * llength) encodeTableau 
    (fun m => projVars 0 llength m = init 
      /\ (forall i, 0 <= i < steps -> valid offset width windows (projVars (i * llength) llength m) (projVars (S i * llength) llength m)) 
      /\ satFinal offset llength final (projVars (steps * llength) llength m)). 
  Proof. 
    specialize (encodesPredicate_and (encodeListAt_encodesPredicate 0 init) encodeWindowsInAllLines_encodesPredicate) as H. 
    encodesPredicateAt_comp_simp H.  
    specialize (encodesPredicate_and H encodeFinalConstraint_encodesPredicate') as H1.
    clear H. 
    encodesPredicateAt_comp_simp H1. 
    unfold encodeTableau. 
    rewrite !Nat.sub_0_r in H1. cbn [Nat.add] in H1. 

    eapply encodesPredicateAt_extensional; [ clear H1| apply H1].
    intros m H4. 
    setoid_rewrite projVars_comp. rewrite !Nat.min_l by nia. 
    setoid_rewrite Nat.add_0_r.  
    split. 
    - intros (H1 & H2 & H3). 
      repeat split; [easy | | easy].
      intros. rewrite !Nat.min_l by nia. rewrite !projVars_comp. rewrite !Nat.min_l by nia. 
      rewrite !Nat.add_0_r. now apply H2.
    - rewrite !and_assoc. intros (H1 & H2 & H3). split; [easy |split;[ | easy]]. 
      intros. specialize (H2 i H). rewrite !Nat.min_l in H2 by nia. 
      rewrite !projVars_comp in H2. rewrite !Nat.min_l in H2 by nia.
      rewrite !Nat.add_0_r in H2. apply H2.
  Qed. 
 
  (*from a proof that a sequence of rewrites is valid, we can restore a satisfying assignment for the encoded windows of the tableau (by concatenating the strings encountered during the sequence of rewrites)*)
  Lemma relpower_valid_to_assignment n x y: 
    relpower (valid offset width windows) n x y -> |x| = llength 
    -> exists m, |m| = (S n * llength) /\ projVars 0 llength m = x /\ projVars (n * llength) llength m = y 
      /\ (forall i, 0 <= i < n -> valid offset width windows (projVars (i * llength) llength m) (projVars (S i * llength) llength m)). 
  Proof. 
    induction 1. 
    - cbn. exists a. rewrite projVars_all; [ | lia]. easy.
    - intros. specialize (valid_length_inv H) as H2. rewrite H1 in H2; symmetry in H2. 
      apply IHrelpower in H2 as (m & H2 & H3 & H4 & H5). clear IHrelpower. 
      exists (a ++ m). repeat split. 
      + rewrite app_length. lia. 
      + rewrite projVars_app1; easy. 
      + cbn. rewrite projVars_app3; easy.
      + intros i H6. destruct i. 
        * cbn. rewrite Nat.add_0_r. setoid_rewrite projVars_app2 at 2; [ | easy]. 
          rewrite !projVars_app1; [ | easy]. rewrite H3. apply H.
        * assert (0 <= i < n) as H7 by lia. apply H5 in H7; clear H5 H6. 
          cbn. rewrite !projVars_app3; [ | easy | easy].  apply H7.
  Qed. 
  
  (*the reduction equivalence for the wellformed BinaryPR instance *)
  Lemma reduction_wf : FSAT encodeTableau <-> exists sf, relpower (valid offset width windows) steps init sf /\ satFinal offset llength final sf. 
  Proof with (try (solve [rewrite explicitAssignment_length; cbn; nia | cbn; lia])). 
    specialize (encodeTableau_encodesPredicate) as H1. split; intros. 
    - destruct H as (a & H). apply H1 in H as (H3 & H4 & H5). 
      exists (projVars (steps * llength) llength (explicitAssignment a 0 (S steps * llength))). 
      split; [ | apply H5]. rewrite <- H3. clear H1 H3 H5. 

      cbn. rewrite projVars_length... rewrite explicitAssignment_app at 1... rewrite projVars_app1...
      rewrite Nat.add_comm. rewrite explicitAssignment_app, projVars_app2, projVars_all... 

      (*as the assignment is constructed by appending new lines, we use the reversed version of relpower *)
      apply relpower_relpowerRev. induction steps. 
      + cbn. constructor. 
      + econstructor. 
        * apply IHn. intros. specialize (H4 i). clear IHn. 
          replace (S (S n) * llength) with (i * llength + (llength + (S n - i) * llength)) in H4 at 1 by nia. 
          replace (S (S n) * llength) with (S i * llength + (llength + (n - i) * llength)) in H4 by nia. 
          rewrite explicitAssignment_app, projVars_app2 in H4...
          rewrite explicitAssignment_app, projVars_app1 in H4...
          rewrite explicitAssignment_app, projVars_app2 in H4...
          rewrite explicitAssignment_app, projVars_app1 in H4...
          
          replace (S n * llength) with (i * llength + (llength + (n - i) * llength)) at 1 by nia. 
          replace (S n * llength) with (S i * llength + (llength + (n - S i) * llength)) by nia. 
          rewrite explicitAssignment_app, projVars_app2...
          rewrite explicitAssignment_app, projVars_app1...
          rewrite explicitAssignment_app, projVars_app2...
          rewrite explicitAssignment_app, projVars_app1...
          now apply H4. 
        * specialize (H4 n). clear IHn. 
          cbn in H4. rewrite Nat.add_comm in H4. setoid_rewrite Nat.add_comm in H4 at 2. setoid_rewrite <- Nat.add_assoc in H4 at 1.
          rewrite explicitAssignment_app, projVars_app2 in H4... cbn in H4. 
          rewrite explicitAssignment_app, projVars_app1 in H4... 
          rewrite explicitAssignment_app, projVars_app2, projVars_all in H4... cbn in H4. now apply H4. 
    - destruct H as (sf & H3 & H4). unfold encodeTableau in *. 
      specialize (relpower_valid_to_assignment H3 eq_refl) as (expAssgn & H5 & H6 & H7 & H8). 
      destruct (expAssgn_to_assgn 0 expAssgn) as (a & H9).
      exists a. apply H1. clear H1. 
      apply expAssgn_to_assgn_inv in H9. rewrite H5 in H9. rewrite H9. easy.
  Qed. 
End fixInstance.

(*now the whole reduction including non-wellformed instances *)
Definition BinaryPR_wf_dec (bpr : BinaryPR) := 
  leb 1 (width bpr) 
  && leb 1 (offset bpr)
  && Nat.eqb (Nat.modulo (width bpr) (offset bpr)) 0
  && leb (width bpr) (|init bpr|)
  && forallb (PRWin_of_size_dec (width bpr)) (windows bpr)
  && Nat.eqb (Nat.modulo (|init bpr|) (offset bpr)) 0. 

Lemma BinaryPR_wf_dec_correct (bpr : BinaryPR) : BinaryPR_wf_dec bpr = true <-> BinaryPR_wellformed bpr. 
Proof. 
  unfold BinaryPR_wf_dec, BinaryPR_wellformed. rewrite !andb_true_iff, !and_assoc.
  rewrite !leb_iff. rewrite <- !(reflect_iff _ _ (Nat.eqb_spec _ _ )).  
  rewrite !forallb_forall. 
  setoid_rewrite PRWin_of_size_dec_correct. 
  split; intros; repeat match goal with [H : _ /\ _ |- _] => destruct H end; 
  repeat match goal with [ |- _ /\ _ ] => split end; try easy. 
  - apply Nat.mod_divide in H1 as (k & H1); [ | lia]. 
    exists k; split; [ | apply H1 ]. destruct k; cbn in *; lia.
  - apply Nat.mod_divide in H4 as (k & H4); [ | lia].  exists k; apply H4.  
  - apply Nat.mod_divide; [ lia | ]. destruct H1 as (k & _ & H1). exists k; apply H1.
  - apply Nat.mod_divide; [ lia | ]. apply H4. 
Qed. 

(*non-wellformed instances are mapped to a trivial no-instance *)
Definition trivialNoInstance := 0 ∧ ¬0. 
Lemma trivialNoInstance_isNoInstance : not (FSAT trivialNoInstance). 
Proof. 
  intros (a & H). unfold satisfies in H. cbn in H.  
  destruct (evalVar a 0); cbn in H; congruence. 
Qed. 

Definition reduction (bpr : BinaryPR) := if BinaryPR_wf_dec bpr then encodeTableau bpr else trivialNoInstance. 

Lemma BinaryPR_to_FSAT (bpr : BinaryPR) : BinaryPRLang bpr <-> FSAT (reduction bpr). 
Proof. 
  split. 
  - intros (H1 & H2). unfold reduction. rewrite (proj2 (BinaryPR_wf_dec_correct _) H1).
    now apply reduction_wf.
  - intros H. unfold reduction in H. destruct (BinaryPR_wf_dec) eqn:H1. 
    + apply BinaryPR_wf_dec_correct in H1. apply reduction_wf in H; easy. 
    + now apply trivialNoInstance_isNoInstance in H. 
Qed. 

(** *** extraction *)
From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Complexity Require Import PolyBounds. 
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LSum LLNat LLists. 
From Undecidability.L.Functions Require Import EqBool.

(** listAnd *)
Definition c__listAnd := 12. 
Definition listAnd_time (l : list formula) := (|l| + 1) * c__listAnd.
Instance term_listAnd : computableTime' listAnd (fun l _ => (listAnd_time l, tt)). 
Proof. 
  extract. solverec. all: unfold listAnd_time, c__listAnd; solverec. 
Qed.

Lemma listAnd_varsIn p l: (forall f, f el l -> formula_varsIn p f) -> formula_varsIn p (listAnd l). 
Proof. 
  unfold formula_varsIn. intros H; induction l; cbn.
  - intros v H1. inv H1.  
  - intros v H1. inv H1; [eapply H; eauto | eapply IHl; eauto]. 
Qed. 

Lemma listAnd_size l : formula_size (listAnd l) <= sumn (map formula_size l) + |l| + 1. 
Proof. 
  induction l; cbn; [lia | rewrite IHl; lia].
Qed. 

(** listOr *)
Definition c__listOr := 12.
Definition listOr_time (l : list formula) := (|l| + 1) * c__listOr.
Instance term_listOr : computableTime' listOr (fun l _ => (listOr_time l, tt)). 
Proof. 
  extract. solverec. all: unfold listOr_time, c__listOr; solverec. 
Qed.

Lemma listOr_varsIn p l: (forall f, f el l -> formula_varsIn p f) -> formula_varsIn p (listOr l). 
Proof. 
  unfold formula_varsIn. intros H; induction l; cbn.
  - intros v H1. inv H1. inv H2.  
  - intros v H1. inv H1; [eapply H; eauto | eapply IHl; eauto]. 
Qed. 

Lemma listOr_size l : formula_size (listOr l) <= sumn (map formula_size l) + |l| + 2. 
Proof. 
  induction l; cbn; [lia | rewrite IHl; lia].
Qed. 

(** tabulate_step *)
Definition c__tabulateStep := 13 + c__add1.
Definition tabulate_step_time (step n : nat) := n * (add_time step + c__tabulateStep) + c__tabulateStep.
Instance term_tabulate_step : computableTime' tabulate_step (fun step _ => (5, fun s _ => (1, fun n _ => (tabulate_step_time step n, tt)))). 
Proof. 
  extract. solverec. 
  all: unfold tabulate_step_time, c__tabulateStep; solverec. 
Qed.

Definition poly__tabulateStep n := n * ((n + 1) * c__add + c__tabulateStep) + c__tabulateStep.
Lemma tabulate_step_time_bound step n : tabulate_step_time step n <= poly__tabulateStep (size (enc step) + size (enc n)). 
Proof. 
  unfold tabulate_step_time. rewrite size_nat_enc_r with (n := n) at 1. 
  unfold add_time. rewrite size_nat_enc_r with (n := step) at 1. 
  unfold poly__tabulateStep; solverec.  
Qed.
Lemma tabulate_step_poly : monotonic poly__tabulateStep /\ inOPoly poly__tabulateStep.
Proof. 
  unfold poly__tabulateStep; split; smpl_inO. 
Qed.

Lemma tabulate_step_length step s n: |tabulate_step step s n| = n.
Proof. 
  revert step s. induction n; cbn; intros; [lia | rewrite IHn; lia]. 
Qed. 

(** tabulate_formula *)
Definition c__tabulateFormula := 8. 
Definition tabulate_formula_time (s step n : nat) (tf : nat -> nat) := tabulate_step_time step n + map_time tf (tabulate_step step s n) + c__tabulateFormula.
Instance term_tabulate_formula : computableTime' tabulate_formula (fun s _ => (1, fun step _ => (1, fun n _ => (1, fun t tf => (tabulate_formula_time s step n (callTime tf), tt))))). 
Proof. 
  extract. solverec. 
  unfold tabulate_formula_time, c__tabulateFormula; solverec. 
Qed.  

Lemma formula_varsIn_monotonic (p1 p2 : nat -> Prop) : (forall n, p1 n -> p2 n) -> forall f, formula_varsIn p1 f -> formula_varsIn p2 f. 
Proof. 
  intros H f. unfold formula_varsIn. eauto.
Qed. 

Lemma tabulate_formula_varsIn s step n t (g : nat -> nat): 
  (forall start, formula_varsIn (fun n => n < g start) (t start))
  -> monotonic g
  -> forall f, f el tabulate_formula s step n t -> formula_varsIn (fun v => v < g (s + step * (n -1))) f. 
Proof. 
  intros H H0 f Hel. unfold tabulate_formula in Hel. apply in_map_iff in Hel as (i & <- & Hel). 
  apply in_tabulate_step_iff in Hel as (i' & H1 & ->). 
  eapply formula_varsIn_monotonic. 
  2: apply H. 
  cbn. intros n' Hn'. unfold monotonic in H0. specialize (H0 (s + step * i') (s + step * (n -1)) ltac:(nia)). nia. 
Qed. 

Lemma tabulate_formula_length s step n t : |tabulate_formula s step n t| = n. 
Proof. 
  revert s step. induction n; cbn; intros; [lia | ]. 
  unfold tabulate_formula in IHn. now rewrite IHn. 
Qed. 

(** encodeLiteral *)
Definition c__encodeLiteral := 6. 
Instance term_encodeLiteral : computableTime' encodeLiteral (fun n _ => (1, fun b _ => (c__encodeLiteral, tt))). 
Proof. 
  extract. solverec. all: unfold c__encodeLiteral; solverec. 
Qed.

Lemma encodeLiteral_size v b : formula_size (encodeLiteral v b) <= 2. 
Proof. 
  unfold encodeLiteral. destruct b; cbn; lia. 
Qed. 

Ltac varsIn_inv := 
  repeat match goal with 
    | [ H: formula_varsIn ?f |- _] => inv H
    | [ H: varInFormula ?v ?f|- _]=> inv H
  end. 

Lemma encodeLiteral_varsIn v b : formula_varsIn (fun n => n = v) (encodeLiteral v b).  
Proof. 
  unfold encodeLiteral. destruct b; cbn; intros v' H; varsIn_inv; lia. 
Qed. 

(** encodeListAt *)
Definition c__encodeListAt := c__encodeLiteral + c__add1 + add_time 1 + 15.
Definition encodeListAt_time (l : list bool) := (|l| + 1) * c__encodeListAt. 
Instance term_encodeListAt : computableTime' encodeListAt (fun s _ => (5, fun l _ => (encodeListAt_time l, tt))). 
Proof. 
  extract. solverec. 
  all: unfold encodeListAt_time, c__encodeListAt; solverec.  
Qed.

Definition poly__encodeListAt n := (n + 1) * c__encodeListAt.
Lemma encodeListAt_time_bound l : encodeListAt_time l <= poly__encodeListAt (size (enc l)). 
Proof. 
  unfold encodeListAt_time. rewrite list_size_length. 
  unfold poly__encodeListAt; solverec. 
Qed. 
Lemma encodeListAt_poly : monotonic poly__encodeListAt /\ inOPoly poly__encodeListAt. 
Proof. 
  unfold poly__encodeListAt; split; smpl_inO. 
Qed.

Lemma encodeListAt_varsIn start l: formula_varsIn (fun n => n >= start /\ n < start + |l|) (encodeListAt start l). 
Proof. 
  revert start; induction l; cbn; intros. 
  - intros v H; varsIn_inv.  
  - intros v H. inv H. 
    + apply encodeLiteral_varsIn in H1. lia. 
    + apply IHl in H1. lia. 
Qed. 

Lemma encodeListAt_size start l : formula_size (encodeListAt start l) <= 3 * (|l|) + 1. 
Proof. 
  revert start; induction l; cbn -[Nat.mul]; intros; [lia | rewrite IHl]. rewrite encodeLiteral_size. lia. 
Qed. 
  
(** encodeWindowAt *)
Definition c__encodeWindowAt := FlatPR.cnst_prem + FlatPR.cnst_conc + 13.
Definition encodeWindowAt_time (win : PRWin bool) := encodeListAt_time (prem win) + encodeListAt_time (conc win) + c__encodeWindowAt.
Instance term_encodeWindowAt : computableTime' encodeWindowAt (fun s1 _ => (1, fun s2 _ => (1, fun win _ => (encodeWindowAt_time win, tt)))). 
Proof. 
  extract. solverec. 
  unfold encodeWindowAt_time, c__encodeWindowAt; solverec. 
Qed.

Definition poly__encodeWindowAt k := (k + 1) * c__encodeListAt * 2 + c__encodeWindowAt.
Lemma encodeWindowAt_time_bound win k: PRWin_of_size win k -> encodeWindowAt_time win <= poly__encodeWindowAt k. 
Proof. 
  unfold PRWin_of_size. intros [H1 H2]. 
  unfold encodeWindowAt_time. unfold encodeListAt_time. rewrite H1, H2. 
  unfold poly__encodeWindowAt; solverec.
Qed. 
Lemma encodeWindowAt_poly : monotonic poly__encodeWindowAt /\ inOPoly poly__encodeWindowAt. 
Proof. 
  unfold poly__encodeWindowAt; split; smpl_inO. 
Qed. 

Lemma encodeWindowAt_varsIn s1 s2 k win : PRWin_of_size win k -> formula_varsIn (fun n => (n >= s1 /\ n < s1 + k) \/ (n >= s2 /\ n < s2 + k)) (encodeWindowAt s1 s2 win). 
Proof. 
  intros [H1 H2]. unfold encodeWindowAt. intros v H. inv H.  
  - apply encodeListAt_varsIn in H3. lia. 
  - apply encodeListAt_varsIn in H3. lia. 
Qed. 

Lemma encodeWindowAt_size s1 s2 k win : PRWin_of_size win k -> formula_size (encodeWindowAt s1 s2 win) <= 6 * k + 3. 
Proof. 
  intros [H1 H2]. unfold encodeWindowAt. cbn -[Nat.mul]. rewrite !encodeListAt_size. rewrite H1, H2. nia. 
Qed. 

(** encodeWindowsAt *)
Definition c__encodeWindowsAt := 4 + c__windows.
Definition encodeWindowsAt_time (bpr : BinaryPR) (s1 s2 : nat) := map_time encodeWindowAt_time (windows bpr) + listOr_time (map (encodeWindowAt s1 s2) (windows bpr)) + c__encodeWindowsAt.
Instance term_encodeWindowsAt : computableTime' encodeWindowsAt (fun bpr _ => (1, fun s1 _ => (1, fun s2 _ => (encodeWindowsAt_time bpr s1 s2, tt)))). 
Proof. 
  extract. solverec. 
  unfold encodeWindowsAt_time, c__encodeWindowsAt; solverec. 
Qed.
  
Definition poly__encodeWindowsAt n := n * (poly__encodeWindowAt n + c__map) + c__map + (n + 1) * c__listOr + c__encodeWindowsAt.
Lemma encodeWindowsAt_time_bound bpr s1 s2: 
  BinaryPR_wellformed bpr 
  -> encodeWindowsAt_time bpr s1 s2 <= poly__encodeWindowsAt (size (enc bpr)). 
Proof. 
  intros H. unfold encodeWindowsAt_time. 
  rewrite map_time_mono. 2: { intros win H1. apply H in H1. instantiate (1 := fun _ => _). cbn. 
    rewrite encodeWindowAt_time_bound by apply H1. reflexivity. 
  } 
  rewrite map_time_const.
  unfold listOr_time. rewrite map_length. 
  poly_mono encodeWindowAt_poly. 2: { rewrite size_nat_enc_r. instantiate (1 := size (enc bpr)). rewrite BinaryPR_enc_size. lia. }
  rewrite list_size_length. replace_le (size (enc (windows bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
  unfold poly__encodeWindowsAt. solverec.   
Qed.
Lemma encodeWindowsAt_poly : monotonic poly__encodeWindowsAt /\ inOPoly poly__encodeWindowsAt. 
Proof. 
  unfold poly__encodeWindowsAt; split; smpl_inO; apply encodeWindowAt_poly. 
Qed.

Lemma encodeWindowsAt_varsIn s1 s2 bpr : 
  BinaryPR_wellformed bpr
  -> formula_varsIn (fun n => (n >= s1 /\ n < s1 + width bpr) \/ (n >= s2 /\ n < s2 + width bpr)) (encodeWindowsAt bpr s1 s2). 
Proof. 
  intros (_ & _ & _ & _ & H1 & _). 
  unfold encodeWindowsAt. apply listOr_varsIn. 
  intros f (win & <- & Hel)%in_map_iff. apply encodeWindowAt_varsIn, H1, Hel. 
Qed. 

Lemma encodeWindowsAt_size s1 s2 bpr : 
  BinaryPR_wellformed bpr
  -> formula_size (encodeWindowsAt bpr s1 s2) <= |windows bpr| * (6 * width bpr + 4) + 2. 
Proof. 
  intros (_ &_  & _ & _ & H1 & _). 
  unfold encodeWindowsAt. rewrite listOr_size. 
  rewrite sumn_map_mono. 2: { intros f (win & <- & Hel)%in_map_iff. instantiate (1 := fun _ => _); cbn -[formula_size].
    rewrite encodeWindowAt_size by apply H1, Hel. reflexivity. 
  } 
  rewrite sumn_map_const, !map_length. nia. 
Qed. 

(** encodeWindowsInLine' *)
Definition c__encodeWindowsInLineP := c__width + c__sub1 + 3 * c__offset + 2 * c__add1 + 24.
Fixpoint encodeWindowsInLineP_time (bpr : BinaryPR) (stepindex l startA startB : nat) := 
  match stepindex with 
  | 0 => 0 
  | S stepi => encodeWindowsAt_time bpr startA startB + sub_time l (offset bpr) + add_time startA + add_time startB + encodeWindowsInLineP_time bpr stepi (l - offset bpr) (startA + offset bpr) (startB + offset bpr)
  end + ltb_time l (width bpr) + c__encodeWindowsInLineP.
Instance term_encodeWindowsInLine': computableTime' encodeWindowsInLine' (fun bpr _ => (1, fun stepi _ => (5, fun l _ => (1, fun s1 _ => (5, fun s2 _ => (encodeWindowsInLineP_time bpr stepi l s1 s2, tt)))))). 
Proof. 
  extract. 
  solverec. all: unfold c__encodeWindowsInLineP; solverec. 
Qed.

(** we first bound the components that can be accounted for by the pr instance and bound the start indices inductively; 
    we have the invariant that start' <= start + stepindex * offset for every start' obtained by recursion*)
Definition poly__encodeWindowsInLineP1 n := poly__encodeWindowsAt n + (n + 1) * c__sub + (c__leb * (1 + n) + c__ltb) + c__encodeWindowsInLineP.
Lemma encodeWindowsInLineP_time_bound1 bpr stepindex l startA startB : 
  BinaryPR_wellformed bpr 
  -> encodeWindowsInLineP_time bpr stepindex l startA startB <= (stepindex + 1) * poly__encodeWindowsInLineP1 (size (enc bpr)) 
    + stepindex * (stepindex * (offset bpr) + startA + stepindex * (offset bpr) + startB + 2) * c__add. 
Proof. 
  intros H.
  revert l startA startB. unfold encodeWindowsInLineP_time. induction stepindex; intros.
  - unfold ltb_time, leb_time. rewrite Nat.le_min_r. 
    rewrite size_nat_enc_r with (n := width bpr) at 1. 
    replace_le (size (enc (width bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; cbn; lia). 
    unfold poly__encodeWindowsInLineP1. leq_crossout. 
  - rewrite IHstepindex. clear IHstepindex. 
    rewrite encodeWindowsAt_time_bound by apply H. 
    unfold sub_time. rewrite Nat.le_min_r. 
    unfold ltb_time, leb_time. rewrite Nat.le_min_r. 
    rewrite size_nat_enc_r with (n := offset bpr) at 1. 
    replace_le (size (enc (offset bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; cbn; lia). 
    rewrite size_nat_enc_r with (n := width bpr) at 1. 
    replace_le (size (enc (width bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; cbn; lia). 
    unfold poly__encodeWindowsInLineP1. unfold add_time. nia.  
Qed.
Lemma encodeWindowsInLineP1_poly : monotonic poly__encodeWindowsInLineP1 /\ inOPoly poly__encodeWindowsInLineP1. 
Proof. 
  unfold poly__encodeWindowsInLineP1; split; smpl_inO; apply encodeWindowsAt_poly. 
Qed.

(** in a second step, we also bound the numbers by their encoding size *)
Definition poly__encodeWindowsInLine' n := (n + 1) * poly__encodeWindowsInLineP1 n + n * (n * n + n + 1) * c__add * 2.
Lemma encodeWindowsInLineP_time_bound bpr stepindex l startA startB : 
  BinaryPR_wellformed bpr -> encodeWindowsInLineP_time bpr stepindex l startA startB <= poly__encodeWindowsInLine' (size (enc bpr) + size (enc stepindex) + size (enc startA) + size (enc startB)). 
Proof. 
  intros H. rewrite encodeWindowsInLineP_time_bound1 by easy.
  rewrite size_nat_enc_r with (n := stepindex) at 1 2 3 4. 
  rewrite size_nat_enc_r with (n := offset bpr) at 1 2. 
  replace_le (size (enc (offset bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
  rewrite size_nat_enc_r with (n := startA) at 1. 
  rewrite size_nat_enc_r with (n := startB) at 1. 
  pose (g := size (enc bpr) + size (enc stepindex) + size (enc startA) + size (enc startB)). 
  poly_mono encodeWindowsInLineP1_poly. 2: { instantiate (1 := g). subst g; lia. }
  replace_le (size (enc stepindex)) with g by (subst g; lia) at 1 2 3 4. 
  replace_le (size (enc bpr)) with g by (subst g; lia) at 1 2. 
  replace_le (size (enc startA)) with g by (subst g; lia) at 1. replace_le (size (enc startB)) with g by (subst g; lia) at 1. 
  fold g. 
  unfold poly__encodeWindowsInLine'. nia. 
Qed.
Lemma encodeWindowsInLineP_poly : monotonic poly__encodeWindowsInLine' /\ inOPoly poly__encodeWindowsInLine'. 
Proof. 
  unfold poly__encodeWindowsInLine'; split; smpl_inO; apply encodeWindowsInLineP1_poly. 
Qed. 

Lemma encodeWindowsInLineP_varsIn bpr stepi l startA startB : 
  BinaryPR_wellformed bpr
  -> formula_varsIn (fun n => (n >= startA /\ n < startA + l) \/ (n >= startB /\ n < startB + l)) (encodeWindowsInLine' bpr stepi l startA startB). 
Proof. 
  intros H0. revert startA startB l. induction stepi; cbn; intros. 
  - destruct width; [ | destruct Nat.leb]; cbn; intros a H1; inv H1. 
  - destruct width eqn:H1; [destruct H0; lia | ]. 
    destruct leb eqn:H2. 
    + apply Nat.leb_le in H2. intros a H. inv H. 
    + apply leb_complete_conv in H2. intros a H. inv H. 
      * apply encodeWindowsAt_varsIn in H4; [ | apply H0]. rewrite !H1 in H4. nia. 
      * apply IHstepi in H4. nia.  
Qed. 

(* a more precise bound could be obtained by replacing stepi with div l (offset bpr) *)
Lemma encodeWindowsInLineP_size bpr stepi l startA startB : 
  BinaryPR_wellformed bpr -> formula_size (encodeWindowsInLine' bpr stepi l startA startB) <= stepi * (|windows bpr| * (6 * width bpr + 4) + 3) + 1.
Proof. 
  intros H0. revert l startA startB. induction stepi; cbn -[Nat.mul Nat.add]; intros. 
  - destruct width; [ | destruct leb]; cbn; lia. 
  - destruct width eqn:H1; [ destruct H0; lia | ]. 
    destruct leb eqn:H2. 
    + cbn. nia. 
    + apply leb_complete_conv in H2. cbn [formula_size]. rewrite IHstepi. clear IHstepi. 
      rewrite encodeWindowsAt_size by apply H0. nia. 
Qed. 

(** encodeWindowsInLine *)
Definition c__encodeWindowsInLine := 3 * c__init + 3 * c__length + c__add1 + 13.
Definition encodeWindowsInLine_time (bpr : BinaryPR) (s : nat) := 
  3 * c__length * (| init bpr |) + add_time s +
  encodeWindowsInLineP_time bpr (| init bpr |) (| init bpr |) s (s + (| init bpr |)) + c__encodeWindowsInLine.
Instance term_encodeWindowsInLine :computableTime' encodeWindowsInLine (fun bpr _ => (1, fun s _ => (encodeWindowsInLine_time bpr s, tt))). 
Proof. 
  extract. solverec. 
  unfold encodeWindowsInLine_time, c__encodeWindowsInLine. solverec. 
Qed.

Definition poly__encodeWindowsInLine n := 3 * c__length * n + (n + 1) * c__add + poly__encodeWindowsInLine' (n * (c__natsizeS + 2) + c__natsizeO) + c__encodeWindowsInLine. 
Lemma encodeWindowsInLine_time_bound bpr s : 
  BinaryPR_wellformed bpr
  -> encodeWindowsInLine_time bpr s <= poly__encodeWindowsInLine (size (enc bpr) + size (enc s)). 
Proof. 
  intros H. unfold encodeWindowsInLine_time. 
  rewrite encodeWindowsInLineP_time_bound by easy.
  poly_mono encodeWindowsInLineP_poly. 
  2: { setoid_rewrite size_nat_enc at 3. rewrite list_size_enc_length, list_size_length. 
       rewrite size_nat_enc_r with (n := s) at 2. 
       replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
       instantiate (1 := (size (enc bpr) + size (enc s)) * ( c__natsizeS + 2) + c__natsizeO). lia. 
  } 
  rewrite list_size_length. replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
  unfold add_time. rewrite size_nat_enc_r with (n := s) at 1. 
  unfold poly__encodeWindowsInLine; solverec.  
Qed.
Lemma encodeWindowsInLine_poly : monotonic poly__encodeWindowsInLine /\ inOPoly poly__encodeWindowsInLine. 
Proof. 
  unfold poly__encodeWindowsInLine; split; smpl_inO.
  - apply encodeWindowsInLineP_poly.
  - apply inOPoly_comp; smpl_inO; apply encodeWindowsInLineP_poly. 
Qed. 

Lemma encodeWindowsInLine_varsIn bpr s : 
  BinaryPR_wellformed bpr
  -> formula_varsIn (fun n => (n >= s /\ n < s + 2 * (|init bpr|))) (encodeWindowsInLine bpr s). 
Proof. 
  intros H. eapply formula_varsIn_monotonic. 
  2: { unfold encodeWindowsInLine. apply encodeWindowsInLineP_varsIn, H. }
  cbn. intros n. lia. 
Qed. 

Lemma encodeWindowsInLine_size bpr s: 
  BinaryPR_wellformed bpr
  -> formula_size (encodeWindowsInLine bpr s) <= (|init bpr|) * (|windows bpr| * (6 * width bpr + 4) + 3) +1. 
Proof.  apply encodeWindowsInLineP_size.  Qed. 
  
(** encodeWindowsInAllLines *)
Definition c__encodeWindowsInAllLines := c__init + c__length + c__steps + 5.
Definition encodeWindowsInAllLines_time (bpr : BinaryPR) := c__length * (|init bpr|) + tabulate_formula_time 0 (|init bpr|) (steps bpr) (encodeWindowsInLine_time bpr) + listAnd_time (tabulate_formula 0 (|init bpr|) (steps bpr) (encodeWindowsInLine bpr)) + c__encodeWindowsInAllLines.
Instance term_encodeWindowsInAllLines : computableTime' encodeWindowsInAllLines (fun bpr _ => (encodeWindowsInAllLines_time bpr, tt)). 
Proof. 
  extract. solverec. 
  unfold encodeWindowsInAllLines_time, c__encodeWindowsInAllLines. nia.  
Qed.

Fact nat_size_mul a b: size (enc (a * b)) <= size (enc a) * size (enc b). 
Proof. 
  rewrite !size_nat_enc. unfold c__natsizeS. nia. 
Qed.

Definition poly__encodeWindowsInAllLines n := 
  c__length * n + (poly__tabulateStep n + (n * (poly__encodeWindowsInLine (n + n * n) + c__map) + c__map)) + c__tabulateFormula + (n + 1) * c__listAnd + c__encodeWindowsInAllLines. 
Lemma encodeWindowsInAllLines_time_bound bpr : BinaryPR_wellformed bpr -> encodeWindowsInAllLines_time bpr <= poly__encodeWindowsInAllLines (size (enc bpr)). 
Proof. 
  intros H. unfold encodeWindowsInAllLines_time. 
  rewrite list_size_length at 1. replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
  unfold tabulate_formula_time. rewrite tabulate_step_time_bound. 
  poly_mono tabulate_step_poly. 2: { rewrite list_size_enc_length. instantiate (1 := size (enc bpr)). rewrite BinaryPR_enc_size; lia. }
  rewrite map_time_mono. 
  2: { intros start Hel. instantiate (1 := fun _ => _). cbn -[Nat.add Nat.mul]. 
       rewrite encodeWindowsInLine_time_bound by apply H. 
       apply in_tabulate_step_iff in Hel as (i & H1 & ->). 
       poly_mono encodeWindowsInLine_poly. 
       2: { rewrite nat_size_le with (a := 0 + (|init bpr|) * i). 2: { instantiate (1 := (|init bpr|) * steps bpr). nia. }
            rewrite nat_size_mul. rewrite list_size_enc_length. 
            replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
            replace_le (size (enc (steps bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
            reflexivity. 
       } 
       reflexivity. 
  } 
  rewrite map_time_const. 
  rewrite tabulate_step_length. 
  unfold listAnd_time, tabulate_formula. rewrite map_length, tabulate_step_length. 
  rewrite size_nat_enc_r with (n := steps bpr) at 1 2. replace_le (size (enc (steps bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia).
  unfold poly__encodeWindowsInAllLines. nia.
Qed. 
Lemma encodeWindowsInAllLines_poly : monotonic poly__encodeWindowsInAllLines /\ inOPoly poly__encodeWindowsInAllLines. 
Proof. 
  unfold poly__encodeWindowsInAllLines; split; smpl_inO; try apply inOPoly_comp; smpl_inO; first [apply tabulate_step_poly | apply encodeWindowsInLine_poly]. 
Qed. 

Lemma encodeWindowsInAllLines_varsIn bpr :
  BinaryPR_wellformed bpr 
  -> formula_varsIn (fun n => n < (1 + steps bpr) * (|init bpr|)) (encodeWindowsInAllLines bpr). 
Proof. 
  intros H. unfold encodeWindowsInAllLines. apply listAnd_varsIn. 
  intros f H1. destruct steps; [now cbn in H1 | ]. 
  eapply tabulate_formula_varsIn in H1. 
  2: { intros s. eapply formula_varsIn_monotonic. 2: apply encodeWindowsInLine_varsIn, H. 
       intros n'. cbn. lia. 
  } 
  2: smpl_inO. 
  cbn in H1. eapply formula_varsIn_monotonic. 2 : apply H1. intros n'. cbn. 
  nia. 
Qed. 

Lemma encodeWindowsInAllLines_size bpr : 
  BinaryPR_wellformed bpr
  -> formula_size (encodeWindowsInAllLines bpr) <= ((steps bpr) * ((|init bpr|) * (|windows bpr| * (6 * width bpr + 4) + 3) +2)) + 1.
Proof. 
  intros H. unfold encodeWindowsInAllLines. rewrite listAnd_size. 
  rewrite tabulate_formula_length. 
  rewrite sumn_map_mono. 2: { intros f H1. unfold tabulate_formula in H1. apply in_map_iff in H1 as (i & <- & H1). 
    instantiate (1 := fun _ => _). cbn. rewrite encodeWindowsInLine_size by apply H. reflexivity. 
  } 
  rewrite sumn_map_const, tabulate_formula_length. nia. 
Qed. 

(** encodeSubstringInLine' *)
Definition c__encodeSubstringInLine' := c__length +  23 + c__sub1 + 2 * c__offset.
Fixpoint encodeSubstringInLineP_time (bpr : BinaryPR) (s : list bool) (stepindex l start : nat) := 
 match stepindex with 
  | 0 => 0 
  | S stepi => encodeListAt_time s +  sub_time l (offset bpr) + c__add1 + add_time start + encodeSubstringInLineP_time bpr s stepi (l - offset bpr) (start + offset bpr)
 end + c__length * (|s|) + ltb_time l (|s|) + c__encodeSubstringInLine'. 
Instance term_encodeSubstringInLine' : computableTime' encodeSubstringInLine' (fun bpr _ => (1, fun s _ => (5, fun stepi _ => (1, fun l _ => (1, fun start _ => (encodeSubstringInLineP_time bpr s stepi l start, tt)))))). 
Proof. 
  extract. solverec. 
  all: unfold encodeSubstringInLineP_time, c__encodeSubstringInLine'. all: solverec. 
Qed.

Definition poly__encodeSubstringInLineP1 n := poly__encodeListAt n + (n + 1) * c__sub + c__add1 + c__length * n + (c__leb * (1 + n) + c__ltb) + c__encodeSubstringInLine'.
Lemma encodeSubstringInLineP_time_bound1 bpr s stepindex l start : 
  BinaryPR_wellformed bpr 
  -> encodeSubstringInLineP_time bpr s stepindex l start <= (stepindex + 1) * poly__encodeSubstringInLineP1 (size (enc bpr) + size (enc s)) + stepindex * (stepindex * (offset bpr) + start + 1) * c__add.
Proof. 
  intros H.
  revert l start. unfold encodeSubstringInLineP_time. induction stepindex; intros.
  - unfold ltb_time, leb_time. rewrite Nat.le_min_r. 
    rewrite list_size_length. 
    unfold poly__encodeSubstringInLineP1. nia. 
  - rewrite IHstepindex. clear IHstepindex. 
    rewrite encodeListAt_time_bound. 
    unfold sub_time. rewrite Nat.le_min_r. 
    unfold ltb_time, leb_time. rewrite Nat.le_min_r. 
    rewrite list_size_length. 
    rewrite size_nat_enc_r with (n := offset bpr) at 1. 
    replace_le (size (enc (offset bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; cbn; lia). 
    poly_mono encodeListAt_poly. 2: { instantiate (1 := size (enc bpr) + size (enc s)). lia. }
    unfold poly__encodeSubstringInLineP1. unfold add_time. nia.  
Qed.
Lemma encodeSubstringInLineP_poly1 : monotonic poly__encodeSubstringInLineP1 /\ inOPoly poly__encodeSubstringInLineP1. 
Proof. 
  unfold poly__encodeSubstringInLineP1; split; smpl_inO; apply encodeListAt_poly. 
Qed.

Definition poly__encodeSubstringInLine' n := (n + 1) * poly__encodeSubstringInLineP1 n + n * (n * n + n + 1) * c__add. 
Lemma encodeSubstringInLineP_time_bound bpr s stepindex l start : 
  BinaryPR_wellformed bpr -> encodeSubstringInLineP_time bpr s stepindex l start <= poly__encodeSubstringInLine' (size (enc bpr) + size (enc s) + size (enc stepindex) + size (enc start)). 
Proof. 
  intros H. rewrite encodeSubstringInLineP_time_bound1 by apply H. 
  pose (g := size (enc bpr) + size (enc s) + size (enc stepindex) + size (enc start)).
  poly_mono encodeSubstringInLineP_poly1. 2 : { instantiate (1 := g). subst g; lia. }
  rewrite size_nat_enc_r with (n := stepindex) at 1 2 3. 
  rewrite size_nat_enc_r with (n := offset bpr). replace_le (size (enc (offset bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
  rewrite size_nat_enc_r with (n := start) at 1. 
  replace_le (size (enc stepindex)) with g by (unfold g; lia) at 1 2 3.  
  replace_le (size (enc bpr)) with g by (unfold g; lia) at 1. 
  replace_le (size (enc start)) with g by (unfold g; lia) at 1. 
  fold g.  unfold poly__encodeSubstringInLine'.  nia.  
Qed.
Lemma encodeSubstringInLineP_poly : monotonic poly__encodeSubstringInLine' /\ inOPoly poly__encodeSubstringInLine'. 
Proof. 
  unfold poly__encodeSubstringInLine'; split; smpl_inO; apply encodeSubstringInLineP_poly1. 
Qed.

Lemma encodeSubstringInLineP_varsIn bpr s stepindex l start: formula_varsIn (fun n => n >= start /\ n < start + l) (encodeSubstringInLine' bpr s stepindex l start). 
Proof. 
  revert l start. induction stepindex; cbn; intros. 
  - destruct s; cbn.
    + intros a H. inv H. 
    + destruct leb; intros a H; varsIn_inv. 
  - destruct s; cbn. 
    + intros a H1. inv H1; [varsIn_inv | ]. 
      apply IHstepindex in H0. lia. 
    + destruct leb eqn:H2; [intros a H; varsIn_inv | ]. 
      apply leb_complete_conv in H2. 
      intros a H. inv H. 
      * apply (@encodeListAt_varsIn start (b :: s)) in H1. cbn in H1. nia. 
      * apply IHstepindex in H1. nia. 
Qed. 

Lemma encodeSubstringInLineP_size bpr s stepindex l start : formula_size (encodeSubstringInLine' bpr s stepindex l start) <= stepindex * (3 * |s| + 1) + 2. 
Proof. 
  revert l start. induction stepindex; cbn; intros. 
  - destruct s; cbn; [lia | ]. destruct leb; cbn; lia. 
  - destruct s; cbn. 
    + rewrite IHstepindex. cbn. nia. 
    + destruct leb eqn:H1; cbn -[Nat.add Nat.mul]; [lia | ]. rewrite IHstepindex. 
      rewrite encodeListAt_size, encodeLiteral_size. cbn. nia. 
Qed. 

(** encodeSubstringInLine *)
Definition c__encodeSubstringInLine := 14. 
Definition encodeSubstringInLine_time (bpr : BinaryPR) (s : list bool) (start l : nat) := encodeSubstringInLineP_time bpr s l l start + c__encodeSubstringInLine. 
Instance term_encodeSubstringInLine : computableTime' encodeSubstringInLine (fun bpr _ => (1, fun s _ => (1, fun start _ => (1, fun l _ => (encodeSubstringInLine_time bpr s start l, tt))))). 
Proof. 
  extract. solverec. all: unfold encodeSubstringInLine_time, c__encodeSubstringInLine; solverec. 
Qed.

Lemma encodeSubstringInLine_varsIn bpr s start l: formula_varsIn (fun n => n >= start /\ n < start + l) (encodeSubstringInLine bpr s start l).
Proof. 
  unfold encodeSubstringInLine. destruct s. 
  - intros a H. inv H. 
  - apply encodeSubstringInLineP_varsIn. 
Qed. 

Lemma encodeSubstringInLine_size bpr s start l : formula_size (encodeSubstringInLine bpr s start l) <= l * (3 * |s| + 1) + 2.
Proof. 
  unfold encodeSubstringInLine. destruct s. 
  - cbn. lia. 
  - apply encodeSubstringInLineP_size. 
Qed. 

(** encodeFinalConstraint *)
Definition encodeFinalConstraint_step (bpr : BinaryPR) (start : nat) (s : list bool) := encodeSubstringInLine bpr s start (|init bpr|). 

Definition c__encodeFinalConstraintStep := c__init + c__length + 4.
Definition encodeFinalConstraint_step_time (bpr : BinaryPR) (start : nat) (s : list bool) := c__length * (|init bpr|) + encodeSubstringInLine_time bpr s start (|init bpr|) + c__encodeFinalConstraintStep.
Instance term_encodeFinalConstraint_step : computableTime' encodeFinalConstraint_step (fun bpr _ => (1, fun start _ => (1, fun s _ => (encodeFinalConstraint_step_time bpr start s, tt)))). 
Proof. 
  extract. solverec. 
  unfold encodeFinalConstraint_step_time, c__encodeFinalConstraintStep; solverec.   
Qed. 

Definition c__encodeFinalConstraint := c__final + 4. 
Definition encodeFinalConstraint_time (bpr : BinaryPR) (start : nat) :=  map_time (encodeFinalConstraint_step_time bpr start) (final bpr) + listOr_time (map (encodeFinalConstraint_step bpr start) (final bpr)) + c__encodeFinalConstraint.
Instance term_encodeFinalConstraint : computableTime' encodeFinalConstraint (fun bpr _ => (1, fun start _ => (encodeFinalConstraint_time bpr start, tt))). 
Proof. 
  apply computableTimeExt with (x := fun bpr start => listOr (map (encodeFinalConstraint_step bpr start) (final bpr))). 
  1: easy.
  extract. solverec. 
  unfold encodeFinalConstraint_time, c__encodeFinalConstraint; solverec. 
Qed.

Definition poly__encodeFinalConstraint n := n * (c__length * n + poly__encodeSubstringInLine' (2 * n) + c__encodeSubstringInLine + c__encodeFinalConstraintStep + c__map) + c__map + (n + 1) * c__listOr + c__encodeFinalConstraint. 
Lemma encodeFinalConstraint_time_bound bpr start : 
  BinaryPR_wellformed bpr 
  -> encodeFinalConstraint_time bpr start <= poly__encodeFinalConstraint (size (enc bpr) + size (enc start)). 
Proof. 
  intros H. unfold encodeFinalConstraint_time. 
  rewrite map_time_mono. 
  2: { intros l Hel. unfold encodeFinalConstraint_step_time, encodeSubstringInLine_time.  
       instantiate (1 := fun _ => _). cbn -[Nat.mul Nat.add]. 
       rewrite encodeSubstringInLineP_time_bound by apply H.
       rewrite list_size_length at 1. replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
       poly_mono encodeSubstringInLineP_poly. 
       2: { instantiate (1 := 2 * (size (enc bpr) + size (enc start))). 
            rewrite (list_el_size_bound Hel), list_size_enc_length. 
            cbn. rewrite BinaryPR_enc_size at 2. lia. 
       } 
       reflexivity. 
  }
  rewrite map_time_const, list_size_length. unfold listOr_time. rewrite map_length, list_size_length. 
  replace_le (size (enc (final bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia).
  unfold poly__encodeFinalConstraint; nia.  
Qed. 
Lemma encodeFinalConstraint_poly : monotonic poly__encodeFinalConstraint /\ inOPoly poly__encodeFinalConstraint. 
Proof. 
  unfold poly__encodeFinalConstraint; split; smpl_inO. 
  - apply encodeSubstringInLineP_poly. 
  - apply inOPoly_comp; smpl_inO; apply encodeSubstringInLineP_poly. 
Qed. 

Lemma encodeFinalConstraint_varsIn bpr start : formula_varsIn (fun n => n >= start /\ n < start + (|init bpr|)) (encodeFinalConstraint bpr start).
Proof. 
  unfold encodeFinalConstraint. apply listOr_varsIn. 
  intros f (s & <- & Hel)%in_map_iff. apply encodeSubstringInLine_varsIn. 
Qed. 

Lemma encodeFinalConstraint_size bpr start : 
  formula_size (encodeFinalConstraint bpr start)<= sumn (map (fun s => ((|init bpr|) * (3 * |s| + 1) + 2)) (final bpr)) + (|final bpr|) + 2.
Proof. 
  unfold encodeFinalConstraint. rewrite listOr_size. 
  rewrite map_map, sumn_map_mono. 
  2: { intros x _. instantiate (1 := fun x => _ ). cbn. rewrite encodeSubstringInLine_size. reflexivity. }
  rewrite map_length. lia. 
Qed. 

(**encodeTableau *)
Definition c__encodeTableau := 2 * c__init + c__steps + c__mult1 + c__length + 11.
Definition encodeTableau_time (bpr : BinaryPR) := encodeListAt_time (init bpr) + encodeWindowsInAllLines_time bpr + c__length * (|init bpr|) + mult_time (steps bpr) (|init bpr|) + encodeFinalConstraint_time bpr (steps bpr * (|init bpr|)) + c__encodeTableau. 
Instance term_encodeTableau : computableTime' encodeTableau (fun bpr _ => (encodeTableau_time bpr, tt)). 
Proof. 
  unfold encodeTableau, encodeFinalConstraint'. extract. solverec. 
  unfold encodeTableau_time, c__encodeTableau. solverec. 
Qed. 

Definition poly__encodeTableau n := poly__encodeListAt n + poly__encodeWindowsInAllLines n + c__length * n + (n * n * c__mult + c__mult * (n + 1)) + poly__encodeFinalConstraint (n + n * n) + c__encodeTableau.
Lemma encodeTableau_time_bound bpr : BinaryPR_wellformed bpr -> encodeTableau_time bpr <= poly__encodeTableau (size (enc bpr)). 
Proof. 
  intros H. unfold encodeTableau_time. 
  rewrite encodeListAt_time_bound. poly_mono encodeListAt_poly. 2: { instantiate (1:= size (enc bpr)). rewrite BinaryPR_enc_size; lia. }
  rewrite encodeWindowsInAllLines_time_bound by apply H.     
  rewrite encodeFinalConstraint_time_bound by apply H. 
  poly_mono encodeFinalConstraint_poly. 
  2: { rewrite nat_size_mul. rewrite list_size_enc_length. 
       replace_le (size (enc (steps bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
       replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
       reflexivity. 
  } 
  unfold mult_time. rewrite list_size_length at 1 2. rewrite size_nat_enc_r with (n := steps bpr). 
  replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia) at 1 2. 
  replace_le (size (enc (steps bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia) at 1 2.
  unfold poly__encodeTableau; nia. 
Qed.
Lemma encodeTableau_poly : monotonic poly__encodeTableau /\ inOPoly poly__encodeTableau. 
Proof. 
  unfold poly__encodeTableau; split; smpl_inO; try apply inOPoly_comp; smpl_inO; first [apply encodeListAt_poly | apply encodeWindowsInAllLines_poly | apply encodeFinalConstraint_poly]. 
Qed. 

Lemma encodeTableau_varsIn bpr: BinaryPR_wellformed bpr -> formula_varsIn (fun n => n < (1 + steps bpr) * (|init bpr|)) (encodeTableau bpr). 
Proof. 
  intros H. 
  unfold encodeWindowsInAllLines. intros a H1. inv H1. 
  - inv H2. 
    + apply encodeListAt_varsIn in H1. nia. 
    + apply encodeWindowsInAllLines_varsIn in H1; [ | apply H]. nia. 
  - unfold encodeFinalConstraint' in H2. apply encodeFinalConstraint_varsIn in H2. nia. 
Qed. 

Lemma encodeTableau_size : {f : nat -> nat & (forall bpr, BinaryPR_wellformed bpr -> formula_size (encodeTableau bpr) <= f (size (enc bpr))) /\ monotonic f /\ inOPoly f}. 
Proof. 
  eexists. split; [ | split]. 
  - intros bpr H. unfold encodeTableau. cbn. 
    rewrite encodeListAt_size. rewrite encodeWindowsInAllLines_size by apply H. 
    unfold encodeFinalConstraint'. rewrite encodeFinalConstraint_size. 
    rewrite !list_size_length. rewrite sumn_map_mono. 
    2: { intros s Hel. instantiate (1 := fun _ => _). cbn -[Nat.mul Nat.add]. 
         rewrite list_size_length with (l := s). rewrite list_size_length. 
         replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
         erewrite list_el_size_bound with (a := s) by apply Hel.
         replace_le (size (enc (final bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
         reflexivity. 
    } 
    rewrite sumn_map_const. rewrite list_size_length. 
    replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
    replace_le (size (enc (final bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia).
    replace_le (size (enc (windows bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia).
    rewrite size_nat_enc_r with (n := width bpr). 
    replace_le (size (enc (width bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia).
    rewrite size_nat_enc_r with (n := steps bpr). 
    replace_le (size (enc (steps bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia).
    instantiate (1 := fun n => _). cbn -[Nat.add Nat.mul]. generalize (size (enc bpr)). reflexivity. 
  - smpl_inO. 
  - smpl_inO. 
Defined. 

Lemma encodeTableau_enc_size : {f : nat -> nat & (forall bpr, BinaryPR_wellformed bpr -> size (enc (encodeTableau bpr)) <= f (size (enc bpr))) /\ inOPoly f /\ monotonic f}.
Proof. 
  destruct encodeTableau_size as (f' & H1 & H2 & H3). 
  eexists. split; [ | split]. 
  - intros bpr H. rewrite formula_enc_size_bound. 
        rewrite H1 by apply H. erewrite formula_varsIn_bound. 
    2: { eapply formula_varsIn_monotonic. 2: apply encodeTableau_varsIn, H. intros n. cbn. apply Nat.lt_le_incl. }
    instantiate (1 := fun n => _). cbn -[Nat.add Nat.mul]. 
    rewrite list_size_length. replace_le (size (enc (init bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia). 
    rewrite size_nat_enc_r with (n := steps bpr). replace_le (size (enc (steps bpr))) with (size (enc bpr)) by (rewrite BinaryPR_enc_size; lia).
    generalize (size (enc bpr)). reflexivity. 
  - smpl_inO. 
  - smpl_inO. 
Qed. 

(** BinaryPR_wf_dec *)

Definition c__BinaryPRWfDec := 3 * c__leb2 + 4 * c__width + 3 * c__offset + 2 * 5 + 2 * c__init + 2 * c__length + c__windows + 32 + 4 * c__leb + 2 * c__eqbComp nat * size (enc 0).
Definition BinaryPR_wf_dec_time x := 2 * c__length * (|init x|) + leb_time (width x) (|init x|) + forallb_time (@FlatPR.PRWin_of_size_dec_time bool (width x)) (windows x) + modulo_time (|init x|) (offset x) + modulo_time (width x) (offset x) + c__BinaryPRWfDec.  
Instance term_BinaryPR_wf_dec : computableTime' BinaryPR_wf_dec (fun bpr _ => (BinaryPR_wf_dec_time bpr, tt)). 
Proof. 
  extract. solverec. 
  unfold BinaryPR_wf_dec_time, c__BinaryPRWfDec, leb_time. rewrite !eqbTime_le_r. 
  do 2 rewrite Nat.le_min_l. leq_crossout. 
Qed. 

Definition c__BinaryPRWfDecBound := 2*(2 * c__length + c__leb + FlatPR.c__prwinOfSizeDecBound + c__forallb + 2 * c__moduloBound + c__BinaryPRWfDec).
Definition poly__BinaryPRWfDec n := (n*n + 2* n + 1) * c__BinaryPRWfDecBound.
Lemma BinaryPR_wf_dec_time_bound fpr : 
  BinaryPR_wf_dec_time fpr <= poly__BinaryPRWfDec (size (enc fpr)). 
Proof. 
  unfold BinaryPR_wf_dec_time. rewrite leb_time_bound_l. 
  rewrite !modulo_time_bound. rewrite list_size_enc_length.
  rewrite list_size_length.
  erewrite forallb_time_bound_env.
  2: {
    split; [intros | ].
    - specialize (FlatPR.PRWin_of_size_dec_time_bound (X := bool) y a) as H1.
      instantiate (2:= fun n => (n + 1) * FlatPR.c__prwinOfSizeDecBound). nia. 
    - smpl_inO. 
  }
  rewrite list_size_length. 
  replace_le (size(enc (windows fpr))) with (size (enc fpr)) by (rewrite BinaryPR_enc_size; lia). 
  replace_le (size(enc (init fpr))) with (size (enc fpr)) by (rewrite BinaryPR_enc_size; lia). 
  replace_le (size(enc (width fpr))) with (size (enc fpr)) by (rewrite BinaryPR_enc_size; lia). 
  replace_le (size(enc(offset fpr))) with (size (enc fpr)) by (rewrite BinaryPR_enc_size; lia). 
  unfold poly__BinaryPRWfDec, c__BinaryPRWfDecBound. nia.
Qed. 
Lemma BinaryPR_wf_dec_poly : monotonic poly__BinaryPRWfDec /\ inOPoly poly__BinaryPRWfDec.
Proof. 
  unfold poly__BinaryPRWfDec; split; smpl_inO. 
Qed. 

(** reduction *)
Definition c__reduction := 4. 
Definition reduction_time (bpr : BinaryPR) := (if BinaryPR_wf_dec bpr then  encodeTableau_time bpr else 0) +BinaryPR_wf_dec_time bpr + c__reduction. 
Instance term_reduction : computableTime' reduction (fun bpr _ => (reduction_time bpr, tt)). 
Proof. 
  extract. unfold reduction_time, c__reduction; solverec. 
Qed. 

(** full reduction statement *)
Theorem BinaryPR_to_FSAT_poly : reducesPolyMO (unrestrictedP BinaryPRLang) (unrestrictedP FSAT). 
Proof. 
  eapply reducesPolyMO_intro_unrestricted with (f := reduction). 
  - exists (fun n => poly__encodeTableau n + poly__BinaryPRWfDec n + c__reduction). 
    + eexists. 
      eapply computesTime_timeLeq. 2: { apply term_reduction. }
      intros bpr _. cbn -[Nat.add Nat.mul]. split; [ | easy]. 
      unfold reduction_time. destruct BinaryPR_wf_dec eqn:H1. 
      * apply BinaryPR_wf_dec_correct in H1. rewrite encodeTableau_time_bound, BinaryPR_wf_dec_time_bound by easy. 
        generalize (size (enc bpr)). reflexivity. 
      * rewrite BinaryPR_wf_dec_time_bound. lia. 
    + smpl_inO; first [apply encodeTableau_poly | apply BinaryPR_wf_dec_poly]. 
    + smpl_inO; first [apply encodeTableau_poly | apply BinaryPR_wf_dec_poly]. 
    + destruct encodeTableau_enc_size as (f & H1 & H2 & H3). 
      exists (fun n => f n + size (enc trivialNoInstance)). 
      * intros bpr. unfold reduction. destruct BinaryPR_wf_dec eqn:H4. 
        -- apply BinaryPR_wf_dec_correct in H4. rewrite H1 by apply H4. lia. 
        -- lia. 
      * smpl_inO. 
      * smpl_inO. 
  - apply BinaryPR_to_FSAT. 
Qed. 
