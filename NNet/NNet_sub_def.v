From mathcomp
     Require Import ssreflect ssrnat ssrbool ssrfun eqtype seq div fintype
     tuple finfun bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section map2_def.

  Variable (X Y Z:Type).
  Variable (op:X -> Y -> Z).

  Fixpoint map2 fX fY (l1:seq X) (l2:seq Y) : seq Z :=
    match l1 , l2 with
    | [::] , _ => fY l2
    | _ , [::] => fX l1
    | x1 :: l1', x2 :: l2' => (op x1 x2) :: (map2 fX fY l1' l2')
    end.

  Lemma size_map2_maxn fX fY l1 l2:
    (forall l, size (fX l) = size l) ->
    (forall l, size (fY l) = size l) ->
    size (map2 fX fY l1 l2) = maxn (size l1) (size l2).
  Proof.
    move => HX HY.
    by elim : l1 l2 => [|x1 l1 IHl1][|x2 l2]//=; rewrite ?HX ?HY ?IHl1 ?maxnSS.
  Qed.

Lemma size_map2_minn l1 l2:
    size (map2 (fun => [::]) (fun => [::]) l1 l2) = minn (size l1) (size l2).
  Proof.
    elim : l1 l2 => [|x1 l1 IHl1][|x2 l2]//=. by rewrite IHl1 minnSS.
  Qed.

End map2_def.

Section seqop_def.

  Variable (X:Type).
  Variable (op:X -> X -> X).

  Definition seqop := map2 op (fun => [::]) (fun => [::]).

  Lemma seqop_zerol: left_zero [::] seqop.
  Proof. by case. Qed.

  Lemma seqop_zeror: right_zero [::] seqop.
  Proof. by case. Qed.

  Lemma seqopA: associative op -> associative seqop.
  Proof.
    rewrite /seqop => Hassoc.
    elim => [|x1 l1 IHl1][|x2 l2][|x3 l3]//=. by rewrite Hassoc IHl1.
  Qed.

  Lemma seqopC: commutative op -> commutative seqop.
  Proof.
    rewrite /seqop => Hcomm.
    elim => [| x1 l1 IHl1][|x2 l2] =>//=. by rewrite Hcomm IHl1.
  Qed.

  Lemma seqop_size: {morph size : x y / seqop x y >-> minn x y}.
  Proof. move => l1 l2. exact : size_map2_minn. Qed.

  Lemma seqop_idl i l:
    left_id i op -> seqop (iter (size l) (cons i) [::]) l = l.
  Proof. move => H. elim : l =>[|x l]//; by rewrite /seqop /= H =>->. Qed.

  Lemma seqop_idr i l:
    right_id i op -> seqop l (iter (size l) (cons i) [::]) = l.
  Proof. move => H. elim : l =>[|x l]//; by rewrite /seqop /= H =>->. Qed.
(*
  Lemma size_big_seqop_ord (n:nat) (F:'I_n -> seq X):
    size (\big[seqop/[::]]_(i < n) F i) = \max_(i < n) size (F i).
  Proof. apply : big_morph =>//. exact : seqop_size. Qed.
*)
End seqop_def.

(*
Canonical seqop_monoid (X:Type) (id:X) (op:Monoid.law id)
  := Monoid.Law (seqopA (Monoid.mulmA op)) (seqopidl op) (seqopidr op).
Canonical seqop_comoid (X:Type) (id:X) (op:Monoid.com_law id)
  := Monoid.ComLaw (seqopC (Monoid.mulmC op)).
*)
Notation "l1 +l l2" := (seqop addn l1 l2) (at level 60).

Lemma map_mulnS l n: map (muln n.+1) l = l +l map (muln n) l.
Proof. elim : l =>[|x l IHl]//=. by rewrite mulSn IHl. Qed.

Lemma map_muln_big l n:
  map (muln n) l = \big[seqop addn/iter (size l) (cons 0) [::]]_(i < n) l.
Proof.
  elim : n =>[|n IHn]/=.
  - rewrite big_ord0. by elim : l =>[|x l /=->].
  - by rewrite big_ord_recl -IHn map_mulnS.
Qed.

(*
Section seqrel_def.

  Variable (X:Type).
  Variable (rel:X -> X -> bool).
  Variable (f1 f2:seq X -> seq bool).

  Definition seqrel := fun l1 l2 => all id (map2 rel f1 f2 l1 l2).

  Lemma seqrel_refl: reflexive rel -> reflexive seqrel.
  Proof.
    move => Hrefl.
    elim => [|x l IHl] =>//. rewrite /seqrel /=. exact /andP.
  Qed.

  Lemma seqrel_antisymm:
    (forall l:seq X, l <> [::] -> all id (f1 l) && all id (f2 l) = false)
    -> antisymmetric rel -> antisymmetric seqrel.
  Proof.
    move => Hf Hantisymm.
    elim => [|x1 l1 IHl1][|x2 l2] =>//; rewrite /seqrel /=.
    - by rewrite andbC Hf.
    - by rewrite Hf.
    - case /andP; case /andP => Hx12 Hl12; case /andP => Hx21 Hl21.
      rewrite (Hantisymm x1 x2); last exact /andP.
        by rewrite (IHl1 l2); last exact /andP.
  Qed.

  Lemma seqrel_trans :
    (forall l:seq X, l <> [::] -> all id (f1 l) = false) \/
    (forall l:seq X, l <> [::] -> all id (f2 l) = false)
    -> (forall l1 l2:seq X, seqrel l1 l2 -> all id (f1 l2) -> all id (f1 l1))
    -> (forall l1 l2:seq X, seqrel l1 l2 -> all id (f2 l1) -> all id (f2 l2))
    -> transitive rel -> transitive seqrel.
  Proof.
    move => Hf Hf1 Hf2 Htrans.
    elim => [|x1 l1 IHl1][|x2 l2][|x3 l3] =>//.
    - rewrite /seqrel; by case : Hf =>->//.
    - move => H_1. move /Hf2. move : H_1. rewrite /seqrel /map2 => H_1. exact.
    - by move /Hf1.
    - rewrite /seqrel /=; case /andP => Hx21 Hl21. case /andP => Hx13 Hl13.
      apply /andP; split.
      + exact : Htrans Hx21 Hx13.
      + exact : IHl1.
  Qed.

End seqrel_def.

Section seqrel_FT_lemma.

  Variable (X:Type).
  Variable (rel:X -> X -> bool).

  Definition seqrelFT := seqrel rel (fun _=> [::false]) (fun _=> [::true]).

  Lemma seqrelFT_refl : reflexive rel -> reflexive seqrelFT.
  Proof. exact : seqrel_refl. Qed.

  Lemma seqrelFT_antisymm : antisymmetric rel -> antisymmetric seqrelFT.
  Proof. exact : seqrel_antisymm. Qed.

  Lemma seqrelFT_trans : transitive rel -> transitive seqrelFT.
  Proof. apply : seqrel_trans =>//. by left. Qed.

  Lemma seqrelFT_nil : forall l:seq X, seqrelFT [::] l.
  Proof. by case. Qed.

  Lemma seqrelFT_rcons :
    forall l1 l2:seq X, seqrelFT l1 l2 -> forall x:X, seqrelFT l1 (rcons l2 x).
  Proof.
    elim =>[|x1 l1 IHl1][|x2 l2]=>//. case /andP => Hlt. move /IHl1 => IH x /=.
    apply /andP. split =>//. exact : IH.
  Qed.

  Lemma seqleq_size : forall l1 l2:seq X, seqrelFT l1 l2 -> size l1 <= size l2.
  Proof. elim => [|x1 l1 IHl1][|x2 l2] =>//=. case /andP => Hlt. exact : IHl1.
  Qed.

End seqrel_FT_lemma.

Section seqleq_lemma.

  Definition seqleq := seqrelFT leq.
  Notation "l1 <=l l2" := (seqleq l1 l2) (at level 70).

  Lemma seqleq_refl : reflexive seqleq.
  Proof. exact : seqrelFT_refl. Qed.

  Lemma seqleq_antisymm : antisymmetric seqleq.
  Proof. apply : seqrelFT_antisymm. exact : anti_leq. Qed.

  Lemma seqleq_trans : transitive seqleq.
  Proof. apply : seqrelFT_trans. exact leq_trans. Qed.

  Lemma seqleq_seqaddnr : forall l1 l2:seq nat, l1 <=l l1 +l l2.
  Proof.
    elim => [|x1 l1 IHl1][|x2 l2] =>//=; first exact : seqleq_refl.
    apply /andP; split; first exact : leq_addr. exact : IHl1.
  Qed.

  Lemma seqleq_seqaddnl : forall l1 l2:seq nat, l2 <=l l1 +l l2.
  Proof. move => l1 l2; rewrite Monoid.mulmC; exact : seqleq_seqaddnr. Qed.

  Lemma seqleq_seqmaxnr : forall l1 l2:seq nat, l1 <=l seqop maxn l1 l2.
  Proof.
    elim => [|x1 l1 IHl1][|x2 l2]=>//=; first exact : seqleq_refl.
    apply /andP; split; first exact : leq_maxl. exact : IHl1.
  Qed.

  Lemma seqleq_seqmaxnl : forall l1 l2:seq nat, l2 <=l seqop maxn l1 l2.
  Proof. move => l1 l2; rewrite Monoid.mulmC; exact : seqleq_seqmaxnr. Qed.

  Lemma seqleq_seqaddn :
    forall l1 l2:seq nat, l1 <=l l2 <-> exists l:seq nat, l2 = l1 +l l.
  Proof.
    move => l1 l2. split.
    - elim : l1 l2 => [l2 Hleq|x1 l1 IHl1 [|x2 l2]]=>//.
      + exists l2. by rewrite seqopidl.
      + case /andP => Hx12. case /IHl1 => l Hl12.
        exists (x2 - x1 :: l) =>/=. by rewrite (subnKC Hx12) Hl12.
    - case => l ->. by rewrite seqleq_seqaddnr.
  Qed.

  Lemma seqleq_upperbound :forall l1 l2:seq nat, exists l, l1 <=l l /\ l2 <=l l.
  Proof.
    move => l1 l2. exists (l1 +l l2). split; first exact : seqleq_seqaddnr.
    exact : seqleq_seqaddnl.
  Qed.

  Lemma seqleq_seqmaxn_min :
    forall l1 l2 l:seq nat, l1 <=l l -> l2 <=l l -> seqop maxn l1 l2 <=l l.
  Proof.
    elim => [|x1 l1 IHl1][|x2 l2][|x l] =>//.
    case /andP => Hx1x' Hl1l'; case /andP => Hx2x' Hl2l'. apply /andP; split.
    - rewrite geq_max; by apply /andP.
    - exact : IHl1.
  Qed.

End seqleq_lemma.
*)
Lemma eq_bigmax (n:nat) (F:'I_n -> nat) (k:nat):
  n > 0 -> (forall i, F i = k) -> \max_(i < n) F i = k.
Proof.
  case : n F =>//.
  elim => [| n' IHn'] => F Htrue HF.
  - by rewrite big_ord_recl big_ord0 maxn0.
  - rewrite big_ord_recr HF IHn' =>//. exact : maxnn.
Qed.

