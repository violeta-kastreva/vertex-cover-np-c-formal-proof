From Undecidability.TM Require Import TM.
From Undecidability.L.TM Require Import TMflat TMflatEnc TMflatFun TMEncoding TMunflatten TapeFuns.
From Undecidability.L.Datatypes Require Import LNat LProd Lists LOptions.
 
From Undecidability.L.Complexity Require Import ONotation Monotonic.
From Undecidability.L Require Import Tactics.LTactics Functions.Decoding TMflatFun.
From Undecidability Require Import L.Functions.EqBool.

Definition haltConfFlat_time (c : nat) := 20 * c + 21.

Instance term_haltConfFlat : computableTime' haltConfFlat (fun f _ => (1, fun c _ => (haltConfFlat_time (fst c),tt))).
Proof.
  extract. unfold haltConfFlat_time. solverec.
Qed.


Definition zipWith_time {X Y} (fT : X -> Y -> nat) (xs:list X) (ys:list Y) := sumn (zipWith (fun x y => fT x y + 18) xs ys) + 9.
Instance term_zipWith A B C `{registered A} `{registered B} `{registered C}:
  computableTime' (@zipWith A B C) (fun _ fT => (1, fun xs _ => (5,fun ys _ => (zipWith_time (callTime2 fT) xs ys, tt)))).
Proof.
  extract. unfold zipWith_time. solverec.
Qed.

Lemma zipWith_time_const {X Y} c (xs:list X) (ys : list Y):
  zipWith_time (fun _ _ => c) xs ys = min (length xs) (length ys) * (c + 18) + 9.
Proof.
  induction xs in ys |-*;cbn. nia. destruct ys;cbn. nia.
  unfold zipWith_time in *.
  specialize (IHxs ys). nia.
Qed.



From Undecidability.L Require Import Functions.FinTypeLookup.
Definition stepFlat_time (f : nat) (c:mconfigFlat) := 153 * (| snd c |) + f * size (enc (fst c, map (current (sig:=nat)) (snd c))) * c__eqbComp (nat * list (option nat)) + 24 * f + 89.

Instance term_stepFlat : computableTime' stepFlat (fun f _ => (1, fun c _ => (stepFlat_time (length f) c,tt))).
Proof.
  unfold stepFlat.
  extract.
  solverec.
  rewrite map_time_const,zipWith_time_const, lookupTime_leq.
  rewrite Nat.le_min_l.
  unfold stepFlat_time.
  nia.
Qed.

Definition loopMflat_time M c k := loopTime (stepFlat (trans M)) (fun (c0 : mconfigFlat) (_ : unit) => (stepFlat_time (| trans M |) c0, tt)) (haltConfFlat (halt M))
    (fun (c0 : nat * list (tape nat)) (_ : unit) => (haltConfFlat_time (fst c0), tt)) c k.


Instance term_loopMflat : computableTime' loopMflat (fun M _ => (23,fun c  _ => (5, fun k _ => (loopMflat_time M c k,tt)))).
Proof.
  unfold loopMflat,loopMflat_time.
  extract. solverec.
Qed.

Lemma haltConfFlat_time_le s states:
  s <= states -> haltConfFlat_time s <= haltConfFlat_time states.
Proof.
  unfold haltConfFlat_time. lia.
Qed.

Definition stepFlat_timeNice n st sig f :=
  153 * n + f * (st * 4 + 4 + (n * (4 * sig + 19) + 4) + 4) * c__eqbComp (nat * list (option nat)) + 24 * f + 89.

Lemma stepFlat_time_nice M f c:
  validFlatConf M c ->
  stepFlat_time f c <= stepFlat_timeNice M.(tapes) M.(states) M.(sig) f.
Proof.
  intros H.
  unfold stepFlat_time.
  destruct c as (s,t);cbn [fst snd]. destruct H as (eqt&?&?).
  rewrite size_prod;cbn [fst snd].
  rewrite size_nat_enc.
  rewrite size_list. rewrite sumn_le_bound with (c:=4*M.(sig) + 19).
  2:{ rewrite map_map. intros ? (?&<-&?)%in_map_iff. rewrite size_option.
      rewrite Forall_forall in H. apply H in H1.
      destruct x;cbn. 1-3:lia. rewrite size_nat_enc. destruct (H1 n).
      cbn;eauto. all:nia. }
  rewrite !map_length.
  rewrite eqt. unfold stepFlat_timeNice. nia.
Qed.

Definition loopMflat_timeNice M k := 
  k * (stepFlat_timeNice M.(tapes) M.(states) M.(sig) (length M.(trans))  + haltConfFlat_time M.(states) + 13) + haltConfFlat_time M.(states) + 7.

Lemma validFlatConf_step M c c' :
  validFlatTM M -> validFlatConf M c -> stepFlat (M.(trans)) c = c' ->  validFlatConf M c'.
Admitted. 

Lemma loopMflat_time_nice M c k:
  validFlatTM M  -> validFlatConf M c
  -> loopMflat_time M c k <= loopMflat_timeNice M k.
Proof.
  intros HM Hc.
  unfold loopMflat_time.
  induction k in c,Hc|-*;
  destruct c as (s,t); inversion Hc as (?&?&?);cbn [fst snd].
  all:cbn [loopTime fst snd].
  {rewrite haltConfFlat_time_le with (states:=M.(states)). all:unfold loopMflat_timeNice; try nia. }
  destruct stepFlat as (s',t') eqn:eq.
  assert (validFlatConf M (s', t')) by eauto using validFlatConf_step.  
  setoid_rewrite IHk. 2:easy. 
  rewrite haltConfFlat_time_le with (states:=M.(states)). 2:nia.
  rewrite (stepFlat_time_nice (M:=M)). 2:easy. 
  unfold loopMflat_timeNice; nia.
Qed.



Definition sizeOfmTapesFlat_time sig (t : list (tape sig))
  := sumn (map (@sizeOfTape _) t) * 55 + length t * 58 + 8.

Instance term_sizeOfmTapesFlat sig {H:registered sig}:
  computableTime' (@sizeOfmTapesFlat sig) (fun t _ => (sizeOfmTapesFlat_time t,tt)).
Proof.
  assert (H' : extEq
                 (fix sizeOfmTapesFlat (ts : list (tape sig)) : nat :=
                    match ts with
                    | [] => 0
                    | t :: ts0 => Init.Nat.max (sizeOfTape t) (sizeOfmTapesFlat ts0)
                    end) (sizeOfmTapesFlat (sig:=sig))).
  { intros x. induction x;hnf;cbn. all:easy. }
  cbn [extEq] in H'.
  
  eapply computableTimeExt. exact H'.
  extract. unfold sizeOfmTapesFlat_time. solverec. 
Qed.

Definition sizeOfmTapesFlat_timeSize n := n * 57.
Lemma sizeOfmTapesFlat_timeBySize {sig} `{registered sig} (t:list (tape sig)) :
  sizeOfmTapesFlat_time t <= sizeOfmTapesFlat_timeSize (size (enc t)).
Proof.
  unfold sizeOfmTapesFlat_time,sizeOfmTapesFlat_timeSize.
  rewrite size_list.
  induction t.
  all:cbn [map sumn length].
  now nia.
  rewrite sizeOfTape_by_size. nia.
Qed.


Definition allSameEntry_helper {X Y} eqbX eqbY `{_:eqbClass (X:=X) eqbX} `{eqbClass (X:=Y) eqbY}
  := fun x y '(x', y') => implb (eqbX x (x':X)) (eqbY y (y':Y)).

Instance term_allSameEntry_helper {X Y} {HX:registered X} {HY:registered Y}
         `{eqbCompT X (R:=HX)} `{eqbCompT Y (R:=HY)}
  :
    computableTime' (@allSameEntry_helper X Y _ _ _ _)
                    (fun x _ => (1,fun y _ =>(1,fun xy _ => (eqbTime (X:=X) (size (enc x)) (size (enc (fst xy))) + eqbTime (X:=Y) (size (enc y)) (size (enc (snd xy))) + 18,tt)))).
Proof.
  unfold allSameEntry_helper. unfold implb. extract. solverec.
Qed.

Definition allSameEntry_time X Y {HX:registered X} {HY:registered Y}
           `{eqbCompT X (R:=HX)} `{eqbCompT Y (R:=HY)} l x y :=
  l * (x*c__eqbComp X + y* c__eqbComp Y + 42) + 12.

Arguments allSameEntry_time : clear implicits.
Arguments allSameEntry_time _ _ {_ _ _ _ _ _ _ _} _ _.


Lemma allSameEntry_time_le X Y {HX:registered X} {HY:registered Y}
           `{eqbCompT X (R:=HX)} `{eqbCompT Y (R:=HY)} l l' x x' y y' :
  l <= l' -> x <= x' -> y <= y'
  -> allSameEntry_time X Y l x y <= allSameEntry_time X Y l' x' y'.
Proof. unfold allSameEntry_time. intros -> -> ->. nia. Qed.


Instance term_allSameEntry X Y {HX:registered X} {HY:registered Y}
         `{eqbCompT X (R:=HX)} `{eqbCompT Y (R:=HY)}:
  computableTime' (@allSameEntry X Y _ _ _ _) (
                    fun x _ => (1,
                             fun y _ => (1,
                                      fun f _ =>(
                                          allSameEntry_time X Y (length f) (size (enc x)) (size (enc y)),tt)))).

Proof.
  unfold allSameEntry.
  change (fun (x : X) (y : Y) (f : list (X * Y)) => forallb (fun '(x', y') => implb (eqb0 x x') (eqb1 y y')) f)with
      (fun (x : X) (y : Y) f => forallb (allSameEntry_helper x y)  f).
  extract.
  recRel_prettify2. 1-2:easy.
  clear.
  rename x1 into f. unfold allSameEntry_time.
  
  change 12 with (8+4) at 3. rewrite !Nat.add_assoc. eapply plus_le_compat_r.
  
  induction f as [ | [x' y'] f].
  { easy. }
  cbn - [plus mult] . rewrite IHf.
  do 2 rewrite eqbTime_le_l.  clear. ring_simplify. 
  nia.
Qed.


Definition isInjFinfuncTable_time X Y {HX:registered X} {HY:registered Y}
           `{eqbCompT X (R:=HX)} `{eqbCompT Y (R:=HY)} l sf :=
  l * (allSameEntry_time X Y l sf sf + 21) + 8.

Instance term_isInjFinfuncTable X Y {HX:registered X} {HY:registered Y}
         `{eqbCompT X (R:=HX)} `{eqbCompT Y (R:=HY)}:
  computableTime' (@isInjFinfuncTable X Y _ _ _ _) (fun f _ => (isInjFinfuncTable_time (X:=X) (Y:=Y) (length f) (size (enc f)),tt)).
Proof.
  unfold isInjFinfuncTable. cbn. extract. unfold isInjFinfuncTable_time.
  solverec. subst.
  rewrite size_list_cons.
  setoid_rewrite <- allSameEntry_time_le with (l:=length l) (x:=(size (enc x))) (y:=size(enc y)) at 4.
  2:nia.
  2,3:now rewrite size_prod;cbn [fst snd];nia.
  setoid_rewrite <- allSameEntry_time_le with (l:=length l) (x:=(size (enc l))) (y:=size(enc l)) at 3.
  all:try nia.
Qed.

Definition isBoundRead sig := fun a : option nat => match a with
                                               | Some a0 => a0 <? sig
                                               | None => true
                                               end.
Definition isBoundWrite sig := (fun a : option nat * move => match fst a with
                                                        | Some a0 => a0 <? sig
                                                        | None => true
                                                        end).



Instance term_isBoundRead:
  computableTime' isBoundRead (fun sig _ => (1, fun s _ => (size (enc s) * 4,tt))).
Proof.
  unfold isBoundRead,Nat.ltb. extract. solverec.
  
  all:rewrite size_option.
  all:try rewrite size_nat_enc. all:solverec. 
Qed.

Instance term_isBoundWrite:
  computableTime' isBoundWrite (fun sig _ => (1, fun s _ => (size (enc s) * 4,tt))).
Proof.
  unfold isBoundWrite,Nat.ltb. extract.
  recRel_prettify2.
  all:try rewrite size_prod;cbn [fst snd] in *;subst;repeat rewrite size_option,!size_nat_enc. all:solverec. 
Qed.

Definition isBoundEntry sig n states: (nat * list (option nat) * (nat * list (option nat * move))) -> bool:= 
  (fun '(s, v, (s', v')) =>
     (s <? states)
       && (| v | =? n)
       && forallb (isBoundRead sig) v
       && (s' <? states) && (| v' | =? n) &&
       forallb (isBoundWrite sig) v').


Instance term_isBoundEntry:
  computableTime' isBoundEntry (fun sig _ => (1,
                                           fun n _ => (1,
                                                    fun states _ => (1,
                                                                  fun e _ => 
                                                                    (size (enc e)* (8+c__eqbComp nat),tt))))).
Proof.
  unfold isBoundEntry, Nat.ltb. extract. 
  
  recRel_prettify2. 1-3:nia. 
  all:rewrite !size_prod;cbn [fst snd].
  all:rewrite !forallb_time_eq. 
  all:rewrite !size_list.
  
  
  all:rewrite !sumn_map_add,!sumn_map_mult_c_r,!sumn_map_c.
  all:unfold eqbTime.
  all:rewrite !Nat.le_min_l.
  all:rewrite !size_nat_enc. all:zify. all:clear; nia. 
Qed.

Instance term_isBoundTransTable:
  computableTime' isBoundTransTable (fun _ _ => (1,
                                              fun _ _ => (1,
                                                       fun _ _ => (1,
                                                                fun f _ => 
                                                                  (size (enc f)* (8+c__eqbComp nat),tt))))).
Proof.
  unfold isBoundTransTable.
  eapply computableTimeExt with (x:=fun sig n states f => forallb (isBoundEntry sig n states) f).
  {reflexivity. }
  extract.
  solverec.
  rewrite forallb_time_eq.
  rewrite !size_list.
  rewrite !sumn_map_mult_c_r.
  rewrite !sumn_map_add, !sumn_map_c.
  all:ring_simplify. zify. clear; nia.
Qed.

Definition time_isValidFlatTrans lf sf := isInjFinfuncTable_time (X:=nat * list (option nat)) (Y:=(nat * list (option nat * move))) lf sf + sf * (c__eqbComp nat + 8) + 9.

Instance term_isValidFlatTrans:
  computableTime' (isValidFlatTrans)
                  (fun _ _ => (1,
                   fun _ _ => (1,
                   fun _ _ => (1,
                   fun f _ => 
                    (time_isValidFlatTrans (length f)(size (enc f)),tt))))).
Proof.
  unfold isInjFinfuncTable. cbn. extract.
  solverec. unfold time_isValidFlatTrans. nia.
Qed.

Definition isValidFlatTM_time lf sf st:= time_isValidFlatTrans lf sf+ st*14 + 77.

Instance term_isValidFlatTM : computableTime' isValidFlatTM (fun M _ => (isValidFlatTM_time (length (trans M)) (size (enc (trans M))) (states M),tt)).
Proof.
  unfold isValidFlatTM. unfold Nat.ltb.
  extract. unfold isValidFlatTM_time. solverec.
Qed.

Definition  isValidFlatTape_time (sig:nat) (t:nat) :=
  t * (sig * 14 + 29 + 44) + 37.

Lemma isValidFlatTape_time_le sig t t' :
  t <= t' -> isValidFlatTape_time sig t <= isValidFlatTape_time sig t'.
Proof. unfold isValidFlatTape_time. intros ->. nia. Qed. 


Instance term_isValidFlatTape : computableTime' isValidFlatTape
            (fun sig _ => (1, fun t _ => (isValidFlatTape_time sig (sizeOfTape t),tt))).
Proof.
  pose (f x y:= Nat.ltb y x).
  unfold isValidFlatTape.
  refine (_:computableTime' (fun (sig : nat) (t : tape nat) => forallb (f sig) (tapeToList t)) _).
  
  assert (computableTime' f (fun x _ =>(1, fun y _ => (Init.Nat.min y x * 14 + 29, tt)))).
  { unfold f,Init.Nat.ltb. extract. solverec. }

  extract. solverec.
  evar (c:nat).
  rewrite forallb_time_eq,sumn_le_bound with (c:=c).
  2:{ intros ? (?&<-&?)%in_map_iff. rewrite Nat.le_min_r. unfold c;reflexivity. }
  rewrite map_length. fold (sizeOfTape x0).
  unfold isValidFlatTape_time,c. lia.
Qed.

Definition  isValidFlatTapes_time (sig lt mt :nat) := lt*(isValidFlatTape_time sig mt + 30) + 28.


Instance term_isValidFlatTapes : computableTime' isValidFlatTapes (fun sig _ => (1, fun n _ => (1,fun t _ => (isValidFlatTapes_time sig n (sizeOfmTapesFlat t),tt)))).
Proof.
  unfold isValidFlatTapes.
  eapply computableTimeExt with (x:= fun sig n t => if lengthEq t n then forallb (isValidFlatTape sig) t else false).
  {intros ? ? ?;hnf. now rewrite lengthEq_spec. }
  extract. unfold isValidFlatTapes_time,lengthEq_time.
  solverec.
  rewrite <- lengthEq_spec in H. apply beq_nat_true in H. subst.
  evar (c:nat).
  rename x1 into t.
  rewrite forallb_time_eq,sumn_le_bound with (c:=c).
  2:{ intros ? (?&<-&?)%in_map_iff.
      rewrite isValidFlatTape_time_le with (t':=sizeOfmTapesFlat t).
      1:now unfold c;reflexivity.
      clear - H. induction t;inv H. all:now cbn.
  }
  rewrite map_length. unfold c. nia.
Qed.

Definition execFlatTM_time (M:TM) (t:nat) (k:nat) :=
 isValidFlatTM_time (length M.(trans)) (size (enc M.(trans))) M.(states) + isValidFlatTapes_time M.(sig) M.(tapes) t + loopMflat_timeNice M k + 66 .

Instance term_execFlatTM: computableTime' execFlatTM (fun M _ => (1,fun t _ => (1,fun k _ => (execFlatTM_time M (sizeOfmTapesFlat t) k,tt)))).
Proof.
  extract. unfold execFlatTM_time. recRel_prettify.
  intros M _. split. easy.
  intros t _. split. easy.
  intros k _. split. 2:now repeat destruct _.
  destruct (isValidFlatTM_spec M). 2:nia.
  destruct isValidFlatTapes eqn:Ht. 2:nia.
  rewrite loopMflat_time_nice.
  -nia.
  -easy.
  -unfold isValidFlatTapes in Ht.  hnf.
   destruct (Nat.eqb_spec (length t) (tapes M)). 2:easy.
   split. easy.
   split.
   +apply Forall_forall. rewrite forallb_forall in Ht. intros ? H'. specialize (Ht _ H'). now destruct (isValidFlatTape_spec (sig M) x).
   +destruct v. easy.
Qed.

Lemma execFlat_poly : {f : nat -> nat & (forall M t k, execFlatTM_time M t k <= f (size (enc M) +t + k)) /\ inOPoly f /\ monotonic f}.
Proof.
  unfold execFlatTM_time,isValidFlatTM_time,time_isValidFlatTrans,isInjFinfuncTable_time,allSameEntry_time,loopMflat_timeNice,haltConfFlat_time,isValidFlatTapes_time,isValidFlatTape_time,stepFlat_timeNice.
  eexists (fun x => _). split.
  {
    intros M t k.
    remember ( (size (enc M) + t + k)) as x.
    assert (Hf : (size (enc (trans M)) <= x)).
    { subst x. rewrite size_TM. destruct M. cbn. lia. }
    rewrite Hf. 

    assert ( Hlt : | trans M | <= x).
    { rewrite <- Hf. rewrite size_list_enc_r. lia. }
    rewrite Hlt.

    assert (Hn : tapes M <= x).
    { subst x. rewrite size_TM. destruct M. cbn. rewrite size_nat_enc_r with (n:=tapes) at 1. lia. }
    rewrite Hn.

    assert (Hst : states M <= x).
    { subst x. rewrite size_TM. destruct M. cbn. rewrite size_nat_enc_r with (n:=states) at 1. lia. }
    rewrite Hst.

    assert (Hsig : sig M <= x).
    { subst x. rewrite size_TM. destruct M. cbn. rewrite size_nat_enc_r with (n:=sig) at 1. lia. }
    rewrite Hsig.
    
    assert (Ht : t <= x) by lia.
    rewrite Ht.

    assert (Hk : k <= x) by lia.
    rewrite Hk. 
    clear. reflexivity.
  }
  split. all:smpl_inO.
Qed.
