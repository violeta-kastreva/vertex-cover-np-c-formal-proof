From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TapeDecode TMunflatten TMflatten.
From Undecidability.L.Complexity.Problems Require Import TMGenNP_fixed_mTM Cook.GenNP.
From Undecidability.L.Functions Require Import EqBool.

From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Complexity Require Import PolyBounds FlatFinTypes MorePrelim.
From Undecidability.L.Datatypes Require Import LProd LOptions LBool LSum LLNat LLists LFinType.

(** * Reduction of GenNP with fixed TM to GenNP with variable TM *)

Lemma execFlatTM_isValidFlatTapes M tp steps c' tp' : execFlatTM M tp steps = Some (c', tp') -> isValidFlatTapes (sig M) (tapes M) tp' = true.
Proof. 
  intros H%execFlatTM_correct.
  destruct H as (sig & n & M' & c0 & c0' & H0 & H1 & H2 & H). 
  inv H. apply flatteningTapeIsValid in Ht. 
  destruct H0. rewrite eq__tapes, eq__sig. apply Ht. 
Qed. 

Section fixTM. 
  Variable (sig : finType).
  Variable (M : mTM sig 1). 

  (*Variable (H : registered sig). *)
  Let reg_sig := @registered_finType sig.
  Existing Instance reg_sig.
  
  Let eqb_sig := eqbFinType_inst (X:=sig).
  Existing Instance eqb_sig.

  Definition flatM := flattenTM M. 

  Definition reduction (p : list sig * nat * nat) := 
    let '(ts, maxSize, steps) := p in (flatM, map index (ts : list sig), maxSize, steps). 

  Definition c__reduction := (16 + 2 * c__map).
  Definition reduction_time (ts : list sig) := (|ts| + 1) * c__reduction.
  Instance term_reduction : computableTime' reduction (fun p _ => (let '(ts, maxSize, steps) := p in reduction_time ts, tt)). 
  Proof. 
    extract. solverec. 
    rewrite map_time_const. unfold reduction_time, c__reduction. nia. 
  Defined.  

  Lemma reduction_correct p : TMGenNP_fixed_singleTapeTM M p <-> FlatFunSingleTMGenNP (reduction p). 
  Proof. 
    unfold TMGenNP_fixed_singleTapeTM, FlatFunSingleTMGenNP. destruct p as ((ts & maxSize) & steps). split.
    - intros (certfin & H1 & (res & H2)). 
      cbn. split; [ | split; [easy | ]]. 
      { unfold list_ofFlatType. intros a (a' & <- & H4)%in_map_iff. apply index_le. }
      unfold execTM in H2. 
      destruct loopM eqn:H3; [ | cbn in H2; congruence].
      exists (map index certfin), (flattenConfig m). split; [ |split].
      + intros a (a' & <- & H4)%in_map_iff. apply index_le.  
      + now rewrite map_length.
      + apply execFlatTM_correct. 
        exists sig, 1, M, (initc M [|initTape_singleTapeTM (ts ++ certfin)|]), m. 
        split; [apply flattenTM_isFlatteningTMOf | split; [ | split; [apply H3 | apply flattenConfig_isFlatteningConfigOf]]]. 
        rewrite <- map_app. apply isFlatteningConfigOf_iff. 
        exists [initTape_singleTapeTM (map index (ts ++ certfin))]. split. 
        * apply isFlatteningTapesOf_iff. cbn. generalize (ts ++ certfin). intros l. destruct l; cbn; easy. 
        * cbn. easy.
    - cbn. intros (_ & _ & (cert & f & H1 & H2 & H3)). 
      destruct (finRepr_exists_list ltac:(reflexivity) H1) as (fincert & H4). 
      exists fincert. split. 
      { rewrite H4, map_length in H2. apply H2. }
      unfold execFlatTM in H3. destruct isValidFlatTM, isValidFlatTapes; cbn in H3; try congruence. 
      assert (isFlatteningConfigOf (index (TM.start M), [initTape_singleTapeTM (map index ts ++ cert)]) (initc M [|initTape_singleTapeTM (ts ++ fincert)|])) as Hconf. 
      { 
        apply isFlatteningConfigOf_iff. 
        exists [initTape_singleTapeTM (map index ts ++ cert)]. cbn. split; [ | easy].
        apply isFlatteningTapesOf_iff. cbn. rewrite H4, <- map_app. 
        generalize (ts ++ fincert). intros l. destruct l; cbn; easy.
      } 
      specialize (loopMflat_correct steps (flattenTM_isFlatteningTMOf M) Hconf) as H5. 
      unfold flatM in H3. rewrite H3 in H5. 
      destruct loopM eqn:H6; [ | cbn in H5; tauto].
      exists (ctapes m). unfold execTM. rewrite H6. cbn. easy.
  Qed. 
  
  (*We use that the finType is constant so that only the length of ts is relevant for our analysis. *)
  Definition c__sizeInputIndex := ((|elem sig|) * c__natsizeS + c__natsizeO + c__listsizeCons).
  Proposition size_input_index (ts : list sig) : size (enc (map index ts)) <= c__sizeInputIndex * size (enc ts) + c__listsizeNil.
  Proof. 
    rewrite list_size_of_el. 
    2: { 
      intros a (a' & <- & H)%in_map_iff. rewrite size_nat_enc. rewrite index_leq. reflexivity. 
    }
    rewrite map_length. setoid_rewrite list_size_length at 2. setoid_rewrite list_size_length at 2. 
    unfold c__sizeInputIndex. nia.  
  Qed. 

  Lemma TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP : 
    reducesPolyMO (unrestrictedP (TMGenNP_fixed_singleTapeTM M)) (unrestrictedP FlatFunSingleTMGenNP). 
  Proof. 
    apply reducesPolyMO_intro_unrestricted with (f := reduction). 
    - evar (f : nat -> nat). exists f. 
      + eexists. eapply computesTime_timeLeq. 2: apply term_reduction. 
        cbn. intros ((ts & ?) & ?) _. split; [ | easy]. 
        unfold reduction_time. rewrite list_size_length. 
        replace_le (size (enc ts)) with (size (enc (ts, n, n0))) by (rewrite !size_prod; cbn; nia). 
        generalize (size (enc (ts, n, n0))). intros n'. 
        [f]: intros n. subst f. cbn. reflexivity. 
      + subst f. smpl_inO. 
      + subst f. smpl_inO. 
      + evar (g : nat -> nat). exists g. 
        * intros ((ts & maxSize) & steps). cbn. 
          rewrite !size_prod. cbn. rewrite size_input_index.  
          instantiate (g := fun n => size (enc flatM) + c__listsizeNil + 8 + (c__sizeInputIndex + 1) * n). 
          subst g. cbn. nia. 
        * subst g. smpl_inO. 
        * subst g. smpl_inO. 
    - apply reduction_correct. 
  Qed. 
End fixTM. 

