
            
From Undecidability Require Import MaxList.
From Undecidability Require Import TM.TM TM.Code.CodeTM.

(* MOVE : this file contains general lemmas from is all over the place... *)

Fixpoint vector_to_list (X : Type) (n : nat) (v : Vector.t X n) : list X :=
  match v with
  | Vector.nil _ => List.nil
  | Vector.cons _ x n v' => x :: vector_to_list v'
  end.


Lemma vector_to_list_correct (X : Type) (n : nat) (v : Vector.t X n) :
  vector_to_list v = Vector.to_list v.
Proof.
  induction v.
  - cbn. auto.
  - cbn. f_equal. auto.
Qed.

Lemma vector_to_list_length (X : Type) (n : nat) (v : Vector.t X n) :
  length (vector_to_list v) = n.
Proof.
  induction v.
  - cbn. auto.
  - cbn. f_equal. auto.
Qed.


Lemma vector_to_list_map (X Y : Type) (f : X -> Y) (n : nat) (v : Vector.t X n) :
  map f (vector_to_list v) = vector_to_list (Vector.map f v).
  induction v.
  - cbn. auto.
  - cbn. f_equal. auto.
Qed.

Lemma vector_to_list_cast (X : Type) (n1 n2 : nat) (H : n1 = n2) (v : Vector.t X n1) :
  vector_to_list (Vector.cast v H) = vector_to_list v.
Proof. subst. rename n2 into n. induction v as [ | x n v IH]; cbn; f_equal; auto. Qed.

Lemma vector_to_list_eta (X : Type) (n : nat) (v : Vector.t X (S n)) :
  Vector.hd v :: vector_to_list (Vector.tl v) = vector_to_list v.
Proof. destruct_vector. cbn. reflexivity. Qed.

Lemma vector_to_list_map2_eta (X Y Z : Type) (n : nat) (f : X -> Y -> Z) (xs : Vector.t X (S n)) (ys : Vector.t Y (S n)) :
  f (Vector.hd xs) (Vector.hd ys) :: vector_to_list (Vector.map2 f (Vector.tl xs) (Vector.tl ys)) =
  vector_to_list (Vector.map2 f xs ys).
Proof. now destruct_vector. Qed.

(** Technical compatibility lemma: Coq's standard library is soo inconsistent... *)
Lemma fold_left_vector_to_list (X Y : Type) (n : nat) (f : Y -> X -> Y) (v : Vector.t X n) (a : Y) :
  Vector.fold_left f a v = fold_left f (vector_to_list v) a.
Proof. revert a. induction v as [ | x n v IH]; intros; cbn in *; f_equal; auto. Qed.

Lemma max_list_rec_eq_foldl (a : nat) (xs : list nat) :
  fold_left max xs a = max_list_rec a xs.
Proof.
  revert a. induction xs as [ | x xs IH]; intros; cbn in *.
  - reflexivity.
  - rewrite IH. rewrite !max_list_rec_max. nia.
Qed.

Lemma sizeOfmTapes_max_list_map (sig : Type) (n : nat) (T : tapes sig n) :
  sizeOfmTapes T = max_list_map (@sizeOfTape _) (vector_to_list T).
Proof.
  unfold sizeOfmTapes.
  rewrite fold_left_vector_to_list.
  rewrite <- vector_to_list_map.
  unfold max_list_map, max_list.
  apply max_list_rec_eq_foldl.
Qed.

Lemma vector_to_list_In (X : Type) (n : nat) (xs : Vector.t X n) (x : X) :
  In x (vector_to_list xs) <-> Vector.In x xs.
Proof.
  split.
  - induction xs as [ | y n xs IH]; intros; cbn in *.
    + auto.
    + destruct H as [ <- | H].
      * now constructor.
      * now constructor; auto.
  - induction xs as [ | y n xs IH]; intros; cbn in *.
    + inv H.
    + apply In_cons in H as [<- | H].
      * now constructor.
      * now constructor; auto.
Qed.

(*MOVE*)
Lemma list_eq_nth_error X (xs ys : list X) :
  (forall n, nth_error xs n = nth_error ys n) -> xs = ys.
Proof.
  induction xs in ys|-*;destruct ys;cbn;intros H. 1:easy. 1-2:now specialize (H 0).
  generalize (H 0).  intros [= ->]. erewrite IHxs. easy. intros n'. now specialize (H (S n')).
Qed.

Lemma vector_nth_error_nat X n' i (xs : Vector.t X n') :
  nth_error (Vector.to_list xs) i = match lt_dec i n' with
                                      Specif.left H => Some (Vector.nth xs (Fin.of_nat_lt H))
                                    | _ => None
                                    end.
Proof.
  clear. rewrite <- vector_to_list_correct. induction xs in i|-*. now destruct i.
  cbn in *. destruct i;cbn. easy. rewrite IHxs. do 2 destruct lt_dec. 4:easy. now symmetry;erewrite Fin.of_nat_ext. all:exfalso;nia. 
Qed.


Lemma vector_nth_error_fin X n' i (xs : Vector.t X n') :
  nth_error (Vector.to_list xs) (proj1_sig (Fin.to_nat i)) = Some (Vector.nth xs i).
Proof.
  clear. rewrite <- vector_to_list_correct. induction xs in i|-*. now inv  i. cbn;rewrite vector_to_list_correct in *.
  cbn in *. edestruct (fin_destruct_S) as [ (i'&->)| -> ]. 2:now cbn.
  unshelve erewrite (_ : Fin.FS = Fin.R 1). reflexivity.
  setoid_rewrite (Fin.R_sanity 1 i'). cbn. easy.
Qed.


Lemma vector_app_to_list X k k' (xs : Vector.t X k) (ys : Vector.t X k'):
  vector_to_list (Vector.append xs ys) = vector_to_list xs ++ vector_to_list ys.
Proof.   
  induction xs. easy. cbn. congruence.
Qed.


Lemma sizeOfmTapes_upperBound (sig : Type) (n : nat) (tps : tapes sig n) :
  forall t, Vector.In t tps -> sizeOfTape t <= sizeOfmTapes tps.
Proof. intros. rewrite sizeOfmTapes_max_list_map. apply max_list_map_ge. now apply vector_to_list_In. Qed.

From Undecidability Require Import L.Prelim.MoreList.

Lemma max_list_sumn l : max_list l <= sumn l.
Proof.
  unfold max_list.
  induction l;cbn. 2:rewrite max_list_rec_max'. all:nia.
Qed.


Lemma right_sizeOfTape sig' (t:tape sig') :
  length (right t) <= sizeOfTape t.
Proof.
  destruct t;cbn. all:autorewrite with list;cbn. all:nia.
Qed.

Lemma length_tape_local_right sig' (t:tape sig') :
  length (tape_local (tape_move_right t)) <= sizeOfTape t.
Proof.
  destruct t;cbn.  1-3:nia. rewrite tape_local_move_right'. autorewrite with list;cbn. all:nia.
Qed.

Lemma size_list X sigX (cX: codable sigX X) (l:list X) :
  size _ l = sumn (map (size cX) l) + length l + 1.
Proof.
  unfold size. cbn. rewrite encode_list_concat.
  rewrite app_length, length_concat, map_map. cbn.
  change S with (fun x => 1 + x). rewrite sumn_map_add,sumn_map_c. setoid_rewrite map_length.
  cbn.  nia.
Qed.

Lemma destruct_vector1 (X : Type) (v : Vector.t X 1) :
  exists x, v = [| x |].
Proof. destruct_vector. eauto. Qed.
