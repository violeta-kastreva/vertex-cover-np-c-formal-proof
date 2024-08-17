From Undecidability.L.Complexity Require Import NP.
From Undecidability.TM Require TM ProgrammingTools CaseList CaseBool Code.Decode Code.DecodeList.
From Undecidability.TM Require Import TM SizeBounds.

From Undecidability.L.Complexity  Require Import UpToCNary.

From Undecidability.L.AbstractMachines Require Import FlatPro.Programs.
     
Unset Printing Coercions.

From Undecidability.LAM Require Alphabets.

From Coq Require Import Lia Ring Arith.

From Undecidability Require Import Code.ListTM_concat_repeat.
Module BoollistToEnc.

  Definition enc_bool_perElem (b:bool) := [lamT;lamT;varT 0;lamT; lamT; varT (if b then 1 else 0); retT; retT;appT].
  Definition enc_bool_nil := [lamT; lamT; varT 1; retT; retT].
  Definition enc_bool_closing :=  [appT; retT; retT].

  Lemma enc_bool_explicit (bs : list bool):
    compile (Computable.enc bs) = flat_map enc_bool_perElem bs ++ enc_bool_nil ++ concat (repeat enc_bool_closing (length bs)).
  Proof.
    unfold Computable.enc. cbn. unfold Lists.list_enc. cbn. unfold LBool.bool_enc.
    induction bs as [ | b bs]. reflexivity.
    cbn - [concat repeat]. rewrite IHbs. replace (S (| bs |)) with (|bs|+1) by nia.
    destruct b;cbn - [concat repeat]. all:repeat (autorewrite with list; cbn - [concat repeat]). all:repeat f_equal.
    all:rewrite repeat_add_app,concat_app. all:easy.
  Qed.

  Lemma enc_bool_perElem_size :( fun b => Code.size (enc_bool_perElem b)) <=c (fun _ => 1).
  Proof.
    eexists. intros []. all:cbv - [mult]. now rewrite Nat.mul_1_r. easy.
  Qed.

  Lemma boollist_size :( fun (bs:list bool) => Code.size bs) <=c (fun bs => length bs + 1).
  Proof.
    eexists. intros bs. rewrite size_list. erewrite (MoreBase.sumn_map_le_pointwise (f2:=fun _ => _)).
    2:{ intros [] ?;cbv. all:reflexivity. } setoid_rewrite MoreList.sumn_map_c. instantiate (1:=2). nia.
  Qed.

  Arguments enc_bool_perElem : simpl never.
  Arguments enc_bool_nil : simpl never.
  Arguments enc_bool_closing : simpl never.


  Section M.
    Import ProgrammingTools Combinators ListTM CaseList CaseBool.
    Import Alphabets.


    Variable (sig : finType).
    (* Hypothesis (defX: inhabitedC sigX). *)

    (* We use the FinType instance of bool, as it has a Case-machine *)
    
    Context `{retr__list : Retract (sigList bool) sig}
            `{retr__Pro : Retract Alphabets.sigPro sig}
            `{retr__nat : Retract sigNat sig}.
    Local Instance retr__bool : Retract bool sig := ComposeRetract retr__list (Retract_sigList_X _).
    
    Check _ : codable sig (list bool).
    Check _ : codable sig bool.

    (* Tapes: 
       0: bs (input)
       1: result 
       2: intern (constant for ConcatRepeat [0])
       3: intern (length of bs for concatReepat [1])
     *)
    
    Definition Rel : pRel sig^+ unit 4 :=
      ignoreParam
        (fun tin 'tout =>
           forall (bs : list bool),
             tin[@Fin0] ≃ bs 
             -> isRight tin[@Fin1]
             -> isRight tin[@Fin2]
             -> isRight tin[@Fin3]
             -> isRight tout[@Fin0]
               /\ tout[@Fin1]  ≃ compile (Computable.enc (rev bs))
               /\ isRight tout[@Fin2]
               /\ isRight tout[@Fin3]).

    (* für step (prepend the bs-dependent symbols) 
               Tapes: 
       0: bs (input)
       1: result 
       2: head of bs
       3: intern (length of bs for concatReepat [1])
     *)

    Definition M__step : pTM sig^+ (option unit) 4 :=
      If (LiftTapes (ChangeAlphabet (CaseList.CaseList _) retr__list) [|Fin0;Fin2|])
         (Switch (LiftTapes (ChangeAlphabet CaseBool retr__bool) [|Fin2|])
                 (fun b => LiftTapes (ChangeAlphabet (WriteValue (encode (enc_bool_perElem b))) _) [| Fin2|];;
                                  LiftTapes (ChangeAlphabet (App' _) _) [|Fin2;Fin1|];;
                                  Return (LiftTapes (Reset _) [|Fin2|]) None))
         (Return (LiftTapes (Reset _) [|Fin0|]) (Some tt)).

    Definition Rel__step : pRel sig^+ (option unit) 4 :=
      (fun tin '(yout,tout) =>
         forall (bs : list bool) (res : Pro),
           tin[@Fin0] ≃ bs 
           -> tin[@Fin1] ≃ res
           -> isRight tin[@Fin2]
           -> match bs,yout with
               [],  Some _ => isRight tout[@Fin0] /\ tout[@Fin1] = tin[@Fin1]
             | (b::bs),None => tout[@Fin0] ≃ bs /\ tout[@Fin1] ≃ enc_bool_perElem b++res
             | _,_ => False
             end
             /\ isRight tout[@Fin2]
             /\ tout[@Fin3] = tin[@Fin3]).

    
    Lemma Realises__step : M__step ⊨ Rel__step .
    Proof.
      eapply Realise_monotone.
      {unfold M__step. TM_Correct_noSwitchAuto. TM_Correct.
       2,3: now (notypeclasses refine (@Reset_Realise _ _ _ _ _);shelve).
       intros b. TM_Correct. 2:now (notypeclasses refine (@Reset_Realise _ _ _ _ _);shelve).
       now apply App'_Realise. }
      intros t (y,t') H. cbn. 
      intros bs res Hbs Hres Ht2. 
      destruct H as [H|H].
      -cbn in H. TMSimp. modpon H;[]. destruct bs. now exfalso.
       TMSimp. modpon H0;[]. modpon H1;[]. modpon H2;[]. modpon H3;[]. TMSimp.
       repeat (simple apply conj). all:try contains_ext. 2:reflexivity. now isRight_mono. 
      -cbn in H. TMSimp. modpon H;[]. destruct bs. 2:easy. TMSimp.
       modpon H0;[]. modpon H1; [].
       repeat (simple apply conj). all:try now isRight_mono. all:reflexivity.
    Qed.

    Definition Ter' time: tRel sig^+ 4 :=
      (fun tin k =>
         exists (bs : list bool) (res : Pro),
           tin[@Fin0] ≃ bs 
           /\ tin[@Fin1] ≃ res
           /\ isRight tin[@Fin2]
           /\ time (length bs) <= k ).
    
    Import PrettyBounds.BaseCode MoreList.
    Lemma _Terminates__step :
      { time : UpToC (fun l => 1) &
               projT1 M__step ↓ (Ter' time)}.
    Proof.
      evar (c1 : nat). evar (c0 : nat).
      exists_UpToC (fun k => max c0 c1).
      eapply TerminatesIn_monotone.
      { unfold M__step. TM_Correct_noSwitchAuto. TM_Correct.
        intros b. TM_Correct. all: eauto 1 using App'_Terminates,App'_Realise.
        all: now (notypeclasses refine (@Reset_Terminates _ _ _ _ _);shelve).
      }
      intros tin k H. hnf in H. destruct H as (bs&res&Hbs&Hres&Htin2&Hl).
      cbn -[plus]. eexists _,( match bs with [] => _ | _ => _ end).
      split. 1:{ eexists bs;split. 2:split. all:simpl_surject. now contains_ext. now simpl_surject. reflexivity. }
      split.
      2:{ intros tout b (H&Hrem). TMSimp. modpon H.
          destruct b,bs. all:try now (exfalso;assumption).
          all:TMSimp;simpl_surject.
          2:{ do 2 eexists. now contains_ext. unfold Reset_steps. cbv -[mult plus]. reflexivity. }
          infTer 4. intros ? H1. modpon H1. TMSimp.
          infTer 4. intros H2. modpon H2.  TMSimp.
          infTer 4. intros ? ? H3. modpon H3.  TMSimp.
          unfold App'_T. cbn.
          infTer 6. 1,2:now simpl_surject;contains_ext.
          { eassert (HApp:=proj2_sig (App'_steps_nice _) (enc_bool_perElem b)). hnf in HApp.
            erewrite HApp. rewrite (correct__leUpToC enc_bool_perElem_size). reflexivity.
          }
          intros ? ? H4. modpon H4. TMSimp.
          eexists. split. now contains_ext.
          unfold Reset_steps. rewrite (correct__leUpToC enc_bool_perElem_size). reflexivity.
      }
      2:now smpl_upToC_solve.
      { rewrite <- Hl. destruct bs.
        -rewrite <- Nat.le_max_l. unfold c0. reflexivity.
        -rewrite <- Nat.le_max_r. unfold c1.
         change (encode_list Encode_Com (enc_bool_perElem b)) with (encode (enc_bool_perElem b)).
         setoid_rewrite (correct__leUpToC enc_bool_perElem_size) at 1 2. 
         unfold CaseList_steps,CaseList_steps_cons. rewrite Encode_bool_hasSize. reflexivity.
      }
    Qed.

    Definition Terminates__step := projT2 _Terminates__step.

    Definition M__loop : pTM sig^+ unit 4 := While M__step.

    Definition Rel__loop : pRel sig^+ (unit) 4 :=
      (fun tin '(yout,tout) =>
         forall (bs : list bool) (res : Pro),
           tin[@Fin0] ≃ bs 
           -> tin[@Fin1] ≃ res
           -> isRight tin[@Fin2]
           -> isRight tout[@Fin0]
             /\ tout[@Fin1] ≃ flat_map enc_bool_perElem (rev bs)++res
             /\ isRight tout[@Fin2]
             /\ tout[@Fin3] = tin[@Fin3]).

    Lemma Realises__loop : M__loop ⊨ Rel__loop .
    Proof.
      eapply Realise_monotone.
      {unfold M__loop. TM_Correct_noSwitchAuto. TM_Correct. apply Realises__step. }
      eapply WhileInduction;intros;hnf;intros bs res Hbs Hres Ht2.
      -hnf in HLastStep. modpon HLastStep. destruct bs. 2:easy.
       TMSimp. easy.
      -hnf in HStar. modpon HStar. destruct bs. easy. TMSimp. modpon HLastStep. TMSimp.
       repeat (simple apply conj). 1,3:now isRight_mono. 2:reflexivity.
       {setoid_rewrite flat_map_concat_map. setoid_rewrite flat_map_concat_map in HLastStep0. 
        rewrite map_app,concat_app. cbn. autorewrite with list. cbn. contains_ext. } 
    Qed.
    
    Import PrettyBounds.BaseCode MoreList.
    Lemma _Terminates__loop :
      { time : UpToC (fun l => l + 1) &
               projT1 M__loop ↓ (Ter' time)}.
    Proof.
      evar (c1 : nat). evar (c2 : nat).
      exists_UpToC (fun l => l * c1 + c2). 2:now smpl_upToC_solve.
      eapply TerminatesIn_monotone.
      -unfold M__loop. TM_Correct. now apply Realises__step. now apply Terminates__step.
      -apply WhileCoInduction. unfold Ter'.
       intros tin k (bs&res&Hbs&Hres&Hxtin2&Hk).
       eexists. split.
       { exists bs,res. repeat simple apply conj. 1-3:eassumption. rewrite UpToC_le. reflexivity. }
       unfold Rel__step. intros ymid tmid Hstep. modpon Hstep.
       destruct ymid as [[]| ],bs. all:try now exfalso;eassumption.
       +cbn [length]. rewrite <- Hk, Nat.mul_0_l, Nat.mul_1_r,!Nat.add_0_l. unfold c2. reflexivity.
       +TMSimp.
        eexists. split.
        *repeat simple eapply ex_intro. repeat simple apply conj. 1-2:now contains_ext. now isRight_mono. reflexivity.
        *rewrite <- Hk. ring_simplify. set (c' := c__leUpToC).
         replace c1 with (c'+1). 2:now unfold c',c1. nia.
    Qed.

    Definition Terminates__loop := projT2 _Terminates__loop.

    
    Definition M : pTM sig^+ unit 4 :=
      LiftTapes (Length retr__list retr__nat) [|Fin0;Fin3;Fin1;Fin2|];; (*0: still bs, 3:length bs, 1,2:right *)
                LiftTapes (ChangeAlphabet (WriteValue (encode ([] : Pro))) retr__Pro) [|Fin1|];; (* 1:res *)
                LiftTapes (ChangeAlphabet (WriteValue (encode (enc_bool_closing))) retr__Pro) [|Fin2|];; (* 2:const for repeat *)
                LiftTapes (ConcatRepeat.M retr__Pro retr__nat) [|Fin2;Fin3;Fin1|];; (* 2:cnst for repeat, 3:length/empty, 1:res *)
                LiftTapes (Reset _) [|Fin2|];;(*2: empty*)
                LiftTapes (ChangeAlphabet (WriteValue (encode  (enc_bool_nil))) retr__Pro ) [|Fin2|];;(*2:nil*)
                LiftTapes (ChangeAlphabet (App' _) retr__Pro) [|Fin2;Fin1|];;(* 1 : res with nil part *)
                LiftTapes (Reset _) [|Fin2|];;(*2: empty*)
                M__loop.

    Lemma Realises : M ⊨ Rel .
    Proof.
      eapply Realise_monotone.
      {unfold M. TM_Correct_noSwitchAuto. TM_Correct.
       all:eauto 1 using Length_Computes, ConcatRepeat.Realises,  App'_Realise,Realises__loop, Realises__step.
       all:now (notypeclasses refine (@Reset_Realise _ _ _ _ _);shelve). }
      intros tin (yout,tout) H. hnf. intros bs Hbs Htin1 Htin2 Htin3.
      hnf in H. cbn in H. TMSimp. modpon H;[]. specialize H0 with (x:=[]). modpon H0;[].
      modpon H1;[]. modpon H2;[]. modpon H3;[].  modpon H4;[]. modpon H5;[]. modpon H6;[].
      modpon H7;[]. TMSimp.  repeat (simple apply conj). 1,3,4:now isRight_mono.
      { rewrite enc_bool_explicit,rev_length. autorewrite with list in H14. contains_ext. }
    Qed.

    
    Definition Ter time: tRel sig^+ 4 :=
      (fun tin k =>
         exists (bs : list bool),
           tin[@Fin0] ≃ bs 
           /\ isRight tin[@Fin1]
           /\ isRight tin[@Fin2]
           /\ isRight tin[@Fin3]
           /\ time (length bs) <= k ).

    Lemma _Terminates :
      { time : UpToC (fun l => l + 1) &
               projT1 M ↓ Ter time}.
    Proof.
      eexists_UpToC time.
      eapply TerminatesIn_monotone.
      { unfold M. TM_Correct.
        all: eauto 2 using App'_Terminates,App'_Realise,Length_Computes,ConcatRepeat.Realises,ConcatRepeat.Terminates,Length_Terminates,Realises__loop.
        all: try now (notypeclasses refine (@Reset_Terminates _ _ _ _ _);shelve).
        all: try now (notypeclasses refine (@Reset_Realise _ _ _ _ _);shelve).
        simple apply Terminates__loop. }
      intros tin k H. hnf in H. destruct H as (bs&Hbs&Hres&Htin2&Htin3&Hl).
      cbn -[plus]. infTer 3.
      { unfold Length_T. cbn. eexists. repeat simple apply conj. now contains_ext. 1-3:now isRight_mono.
        assert (H':=proj2_sig (Length_steps_nice _) bs). hnf in H'. rewrite H',(correct__leUpToC boollist_size). reflexivity.
      }
      2:{ intros tout _ (H&Hrem). TMSimp. modpon H.
          infTer 5. intros t1 _ (Ht1&Ht1Rem). TMSimp. specialize (Ht1 []). modpon Ht1;[].
          infTer 5. intros t2 _ (Ht2&Ht2Rem). TMSimp. modpon Ht2;[].
          unfold ConcatRepeat.Ter. cbn. 
          infTer 5. 1:{ repeat simple apply conj. 1,2,3:now contains_ext.  rewrite UpToC_le. reflexivity. }
          intros t3 _ (Ht3&Ht3Rem). TMSimp. modpon Ht3;[]. rewrite app_nil_r in Ht4. 
          infTer 5. now contains_ext. intros t4 _ (Htp4&Ht4Rem). TMSimp. modpon Htp4;[].
          infTer 5. intros t5 _ (Htp5&Ht5Rem). TMSimp. modpon Htp5;[].
          infTer 5. 1:{unfold App'_T. cbn. eexists _,_.  repeat simple apply conj. 1,2:simpl_surject;now contains_ext.
                       eassert (H':=proj2_sig (App'_steps_nice _) enc_bool_nil). hnf in H'. rewrite H'. reflexivity.
          }
          intros t6 _ Ht6. modpon Ht6;[]. TMSimp.
          infTer 4. now contains_ext.
          { eassert (H':=proj2_sig (Reset_steps_nice) _ _ _ enc_bool_nil). hnf in H'. erewrite H'. reflexivity. }
          intros t7 _ Htp7. modpon Htp7;[]. hnf. TMSimp. 
          do 2 eexists. repeat simple apply conj. 1,2:now contains_ext. now isRight_mono.
          rewrite UpToC_le. reflexivity.
      }
      - rewrite <- Hl. set (l:=length bs). [time]:intros l.  unfold time. reflexivity.
      -unfold time. solve [smpl_upToC_solve].
    Qed.

    Definition Terminates := projT2 _Terminates.

  End M.
End BoollistToEnc.
