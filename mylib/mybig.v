From mathcomp
     Require Import all_ssreflect.
Require Export mylib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ***************************** *)
Section Sbigop_def.
  Variable (R:Type).

  Fixpoint Sbigop_def (op:R -> R -> R) x0 I (r:seq I) (P:pred I) F :=
    if r is x :: r' then if P x
                         then \big[op/(F x)]_(i <- rev r' | P i) F i
                         else Sbigop_def op x0 r' P F
    else x0.

  Definition Sbigop op x0 I (r:seq I) := Sbigop_def op x0 (rev r).

End Sbigop_def.

Notation "\Sbig [ op / x0 ]_ ( i <- r | P ) F" :=
  (Sbigop op x0 r (fun i => P) (fun i => F))
    (at level 36, F at level 36, op, x0 at level 10, i, r at level 50,
     format "'[' \Sbig [ op / x0 ]_ ( i <- r | P ) '/ ' F ']'") : big_scope.

Notation "\Sbig [ op / x0 ]_ ( i <- r ) F" :=
  (Sbigop op x0 r predT (fun i => F))
    (at level 36, F at level 36, op, x0 at level 10, i, r at level 50,
     format "\Sbig [ op / x0 ]_ ( i <- r ) F") : big_scope.

Notation "\Sbig [ op / x0 ]_ ( i | P ) F" :=
  (Sbigop op x0 (index_enum _) (fun i => P) (fun i => F))
    (at level 36, F at level 36, op, x0 at level 10, i at level 50,
     format "'[' \Sbig [ op / x0 ]_ ( i | P ) '/ ' F ']'") : big_scope.

Notation "\Sbig [ op / x0 ]_ i F" :=
  (Sbigop op x0 (index_enum _) predT (fun i => F))
    (at level 36, F at level 36, op, x0 at level 10, i at level 50,
     format "'[' \Sbig [ op / x0 ]_ i '/ ' F ']'") : big_scope.

Section Sbigop_basis.
  Variable (R:Type).
  Variable (op:R -> R -> R).
  Variable (x0:R).

  Lemma Sbig_big :
    right_id x0 op ->
    forall I r (P:pred I) F,
    \Sbig[op/x0]_(i <- r | P i) F i = \big[op/x0]_(i <- r | P i) F i.
  Proof.
    rewrite /Sbigop => Hid I r P F.
    elim /last_ind : r =>[|r x IHr]/=; first by rewrite big_nil.
    rewrite rev_rcons /= IHr -cats1 big_cat_nested big_cons big_nil revK.
    case : ifP =>//_. by rewrite Hid.
  Qed.

  Lemma Sbig_hasC I r (P:pred I) F :
    ~~ has P r -> \Sbig[op/x0]_(i <- r | P i) F i = x0.
  Proof.
    rewrite /Sbigop. elim /last_ind : r =>[|r x IHr]//.
    rewrite rev_rcons -cats1 has_cat /= orbF.
      by case /norP => /IHr ->/negPf ->.
  Qed.

  Lemma Sbig_nil I (P:pred I) F : \Sbig[op/x0]_(i <- [::] | P i) F i = x0.
  Proof. by apply : Sbig_hasC. Qed.

  Lemma Sbig_cons I x r (P:pred I) F :
    \Sbig[op/x0]_(i <- x :: r | P i) F i =
    if P x then if has P r then op (F x) (\Sbig[op/x0]_(i <- r | P i) F i)
                else F x
    else \Sbig[op/x0]_(i <- r | P i) F i.
  Proof.
    rewrite /Sbigop.
    elim /last_ind : r =>[/=|r y IHr];
      first by (case : ifP=>//_; exact : big_nil).
    rewrite -rcons_cons !rev_rcons /= IHr !revK big_cons has_rcons.
      by case : ifP.
  Qed.

End Sbigop_basis.

Section Sbigop.
  Variable (R:Type).
  Variable (op:R -> R -> R).
  Variable (x0:R).

  Lemma Sbig_cat_nested I r1 r2 (P:pred I) F:
    let x := \Sbig[op/x0]_(i <- r2 | P i) F i in
    \Sbig[op/x0]_(i <- r1 ++ r2 | P i) F i =
    if has P r2 then \big[op/x]_(i <- r1 | P i) F i
    else \Sbig[op/x0]_(i <- r1 | P i) F i.
  Proof.
    elim : r1 =>[|y r1 IHr1]/=.
    - rewrite Sbig_nil big_nil. case : ifP=>// /negbT. exact : Sbig_hasC.
    - rewrite !Sbig_cons big_cons IHr1 has_cat. case : ifP =>//_.
      by move : (has P r1) (has P r2) =>[][].
  Qed.

  Lemma Sbig_ind (K:R -> Type) I r (P:pred I) F:
    (forall x y, K x -> K y -> K (op x y)) ->
    (forall i, P i -> K (F i)) ->
    has P r -> K (\Sbig[op/x0]_(i <- r | P i) F i).
  Proof.
    move => Hop HP. elim : r =>[|x r IHr]//=.
    rewrite Sbig_cons. case : ifP =>//= /HP Hx _. case : ifP=>// /IHr.
    exact : Hop.
  Qed.

End Sbigop.

(* ***************************** *)
Module CTTpred.

  Structure class_of (V:Type) (R:rel V) (P:pred V) :=
    Class{
        _:{in P & &, transitive R};
        _:{in P &, total R};
        op:V -> V -> V;
        _:forall x y, op x y = if R x y then x else y
      }.

  Section Packing.
    Structure type V R := Pack {cttP; _:@class_of V R cttP}.
    Variable (V:Type) (R:rel V) (cT:type R).
    Definition class := let: Pack _ c := cT return class_of _ (cttP cT) in c.
    Definition predPredType : pred_sort _ := (cttP cT).
  End Packing.

  Module Exports.
    Definition CTTpred V R := (@type V R).
    Definition CTTop V R (P:@type V R) := @op _ _ _ (class P).
    Coercion cttP : type >-> pred.
    Coercion predPredType : type >-> pred_sort.
  End Exports.
End CTTpred.
Export CTTpred.Exports.

Section CTTpred_lemma.
  Variable (V:Type) (R:rel V).
  Variable (P:CTTpred R).
  Let op := @CTTop _ _ P.

  Lemma CTTtrans : {in P & &, transitive R}.
  Proof. by case : P => CtP []. Qed.

  Lemma CTTtotal : {in P &, total R}.
  Proof. by case : P => CtP []. Qed.

  Lemma CTTrefl : {in P, reflexive R}.
  Proof. move => x Hx. by case /orP : (CTTtotal Hx Hx). Qed.

  Lemma CTTop_def x y : op x y = if R x y then x else y.
  Proof. rewrite /op. by case : P => CtP []. Qed.

  Lemma CTTop_closed : {in P &, forall x y, op x y \in P}.
  Proof. move => x y Hx Hy. rewrite CTTop_def. by case : ifP. Qed.

  Lemma CTTopA : {in P & &, associative op}.
  Proof.
    move => x y z Hx Hy Hz. rewrite !CTTop_def.
    case Ryz : (R y z); case Rxy : (R x y);
    rewrite ?Ryz ?(CTTtrans Hy Hx Hz Rxy Ryz) =>//.
    move : Ryz (CTTtotal Hy Hz) Rxy =>->/=. case : ifP =>// Rxy.
    by move /(CTTtrans Hz Hx Hy Rxy) =>->.
  Qed.

  Lemma CTTopI : idempotent op.
  Proof. move => x. rewrite CTTop_def. by case : ifP. Qed.

  Lemma CTTorder_opl : {in P & &, forall x y z, R (op x y) z = R x z || R y z}.
  Proof.
    move => x y z Hx Hy Hz. rewrite CTTop_def. move : (CTTtotal Hx Hy).
    case : ifP =>[Hxy _|_/= Hyx]; first rewrite orbC.
    - case Hyz : (R y z) =>//=. exact : CTTtrans Hxy Hyz.
    - case Hxz : (R x z) =>//=. exact : CTTtrans Hyx Hxz.
  Qed.

  Lemma CTTorder_opr : {in P & &, forall x y z, R x (op y z) = R x y && R x z}.
  Proof.
    move => x y z Hx Hy Hz. rewrite CTTop_def. move : (CTTtotal Hy Hz).
    case : ifP =>[|_/=]; last rewrite andbC.
    - by case Hxy : (R x y) =>// /(CTTtrans _ _ _ Hxy)->.
    - by case Hxz : (R x z) =>// /(CTTtrans _ _ _ Hxz)->.
  Qed.

End CTTpred_lemma.

(* ***************************** *)
Section Sbigop_CTTpred.
  Variable (V:Type) (R:rel V).
  Variable (cttP:CTTpred R).
  Let op := @CTTop _ _ cttP.

  Variable (x0:V).
  Hypothesis (Hx0:x0 \in cttP).
  Variable (I:eqType) (P:pred I) (F:I -> V).
  Hypothesis (HP : forall x, P x -> (F x) \in cttP).

  Lemma Sbig_in_CTT r:
    \Sbig[op/x0]_(i <- r | P i) F i \in cttP.
  Proof.
    elim : r =>[|x r IHr]//=. rewrite Sbig_cons. case : ifP =>// /HP Hx.
    case : ifP =>//_. exact : CTTop_closed.
  Qed.

  Lemma Sbig_cat r1 r2:
    \Sbig[op/x0]_(i <- r1 ++ r2 | P i) F i =
    if has P r1
    then if has P r2 then op (\Sbig[op/x0]_(i <- r1 | P i) F i)
                             (\Sbig[op/x0]_(i <- r2 | P i) F i)
         else \Sbig[op/x0]_(i <- r1 | P i) F i
    else \Sbig[op/x0]_(i <- r2 | P i) F i.
  Proof.
    elim : r1 =>[|x r1 IHr1]//=. rewrite !Sbig_cons IHr1 has_cat.
    case : ifP =>//= /HP Hx. move : (has P r1) (has P r2) =>[][]//=.
    exact : (CTTopA Hx (Sbig_in_CTT _) (Sbig_in_CTT _)).
  Qed.

  Lemma CTT_Sbigl r M:
    M \in cttP ->
          {in r, forall x,
                P x -> R (F x) M -> R (\Sbig[op/x0]_(i <- r | P i) F i) M}.
  Proof.
    move => HM x. elim : r =>[|y r IHr]//. rewrite in_cons Sbig_cons.
    case /orP =>[/eqP<- Hx|Hxr Hx]; move /HP : Hx (Hx) => HFx.
    - move =>->. case : ifP =>//_ HxM.
      rewrite (CTTorder_opl _ (Sbig_in_CTT _))=>//. by rewrite HxM.
    - case : ifP =>[/HP Hy Hx HxM|_]; last exact : IHr.
      have : has P r; first by (apply /hasP; exists x). move =>->.
      rewrite (CTTorder_opl _ (Sbig_in_CTT _))=>//.
      by rewrite (IHr Hxr Hx HxM) orbT.
  Qed.

  Lemma CTT_SbiglP r M:
    M \in cttP -> has P r ->
          reflect (exists2 x, x \in r & P x /\ R (F x) M)
                  (R (\Sbig[op/x0]_(i <- r | P i) F i) M).
  Proof.
    move => HM Hhas. apply /(iffP idP) =>[|[x Hx []]]; last exact : CTT_Sbigl.
    elim : r Hhas =>[|x r IHr]//=. rewrite Sbig_cons.
    case : ifP =>[Hx _|_/IHr IH /IH [y Hy Hy2]];
      last by (exists y =>//; rewrite in_cons Hy orbT).
    case : ifP =>[Hhas|_ HRx];
      last by (exists x; first exact : mem_head; split).
    rewrite (CTTorder_opl (HP _) (Sbig_in_CTT _))=>//.
    case /orP =>[HRx|/(IHr Hhas) [y Hy Hy2]];
      first by (exists x; first exact : mem_head; split).
    exists y=>//. by rewrite in_cons Hy orbT.
  Qed.

  Lemma CTT_SbigrP r m:
    m \in cttP -> has P r ->
          reflect {in r, forall x, P x -> R m (F x)}
                  (R m (\Sbig[op/x0]_(i <- r | P i) F i)).
  Proof.
    move => Hm. elim : r =>[|x r IHr]//=. rewrite Sbig_cons.
    case : ifP =>[Hx _|Hx /= /IHr IH].
    - apply : (iffP idP) =>[|HR].
      + case : ifP =>[/IHr IH|/hasPn Hr HFx y];
          last by rewrite in_cons =>/orP [/eqP->|/Hr /negP].
        rewrite (CTTorder_opr Hm (HP Hx) (Sbig_in_CTT _))
                =>/andP [] Hfx /IH Hr y.
          by rewrite in_cons =>/orP [/eqP->|/Hr].
      + case : ifP =>[/IHr IH|_]; last exact : HR (mem_head _ _) Hx.
        rewrite (CTTorder_opr _ (HP _) (Sbig_in_CTT _))=>//.
        move : (HR x). rewrite in_cons eq_refl =>->//=. apply /IH => y Hy.
          by apply : HR; rewrite in_cons Hy orbT.
    - apply : (iffP idP) =>[/IH Hr y|Hr];
        first by (rewrite in_cons =>/orP [/eqP->|/Hr]//; rewrite Hx).
      apply /IH => y Hy. apply /Hr. by rewrite in_cons Hy orbT.
  Qed.

  Lemma CTT_Sbig_rel r:
    {in r, forall x, P x -> R (\Sbig[op/x0]_(i <- r | P i) F i) (F x)}.
  Proof.
    move => x Hx Px. exact : (CTT_Sbigl (HP _)) (CTTrefl (HP _)).
  Qed.

End Sbigop_CTTpred.

Section nat_CTTpred.

  Lemma leq_CTTop_def x y: minn x y = if x <= y then x else y.
  Proof.
    move : (leq_total x y). by case : ifP =>[/minn_idPl|_/=/minn_idPr].
  Qed.

  Definition leq_CTTpred_class_of :=
    @CTTpred.Class _ _ {:nat}
                  (fun _ _ _ _ _ _ Hxy Hyz => leq_trans Hxy Hyz)
                  (fun x y _ _ => leq_total x y) _ leq_CTTop_def.
  Canonical leq_CTTpred := CTTpred.Pack leq_CTTpred_class_of.

  Lemma geq_CTTop_def x y : maxn x y = if x >= y then x else y.
  Proof.
    move : (leq_total y x). by case : ifP =>[/maxn_idPl|_/=/maxn_idPr].
  Qed.

  Definition geq_CTTpred_class_of :=
    @CTTpred.Class _ geq {:nat}
                  (fun _ _ _ _ _ _ Hxy Hyz => leq_trans Hyz Hxy)
                  (fun x y _ _ => leq_total y x) _ geq_CTTop_def.
  Canonical geq_CTTpred := CTTpred.Pack geq_CTTpred_class_of.

End nat_CTTpred.

Notation "\min_ ( i <- r | P ) F" :=
(*  (\big[minn/(\max_(i <- r | P) F)]_(i <- r | P%B) F%N)*)
  (\Sbig[minn/0]_(i <- r | P) F)
    (at level 41, F at level 41, i, r at level 50,
     format "'[' \min_ ( i <- r | P ) '/ ' F ']'") : nat_scope.

Notation "\min_ ( i <- r ) F" :=
(*  (\big[minn/(\max_(i <- r) F)]_(i <- r) F%N)*)
  (\Sbig[minn/0]_(i <- r) F)
    (at level 41, F at level 41, i, r at level 50,
     format "\min_ ( i <- r ) F") : nat_scope.

Notation "\min_ ( i | P ) F" :=
(*  (\big[minn/(\max_(i | P) F)]_(i | P%B) F%N)*)
  (\Sbig[minn/0]_(i | P) F%N)
    (at level 41, F at level 41, i at level 50,
     format "\min_ ( i | P ) F") : nat_scope.
(*
Notation "\min_ i F" :=
  (\Sbig[minn/0]_i F%N)
    (at level 41, F at level 41, i at level 50,
     format "\min_ i F") : nat_scope.

Notation "\min_ ( i : I | P ) F" :=
  (\big[minn/(\max_(i : I | P) F)]_(i : I | P%B) F%N)
    (at level 41, F at level 41, i at level 50, only parsing) : nat_scope.

Notation "\min_ ( i : I ) F" :=
  (\big[minn/(\max_(i : I) F)]_(i : I) F%N)
    (at level 41, F at level 41, i at level 50, only parsing) : nat_scope.

Notation "\min_ ( m <= i < n | P ) F" :=
  (\big[minn/(\max_(m <= i < n | P) F)]_(m <= i < n | P%B) F%N)
    (at level 41, F at level 41, i, m, n at level 50,
     format "\min_ ( m <= i < n | P ) F") : nat_scope.

Notation "\min_ ( m <= i < n ) F" :=
  (\big[minn/(\max_(m <= i < n) F)]_(m <= i < n) F%N)
    (at level 41, F at level 41, i, m, n at level 50,
     format "\min_ ( m <= i < n ) F") : nat_scope.

Notation "\min_ ( i < n | P ) F" :=
  (\big[minn/(\max_(i < n | P) F)]_(i < n | P%B) F%N)
    (at level 41, F at level 41, i, n at level 50,
     format "\min_ ( i < n | P ) F") : nat_scope.

Notation "\min_ ( i < n ) F" :=
  (\big[minn/(\max_(i < n) F)]_(i < n) F%N)
    (at level 41, F at level 41, i, n at level 50,
     format "\min_ ( i < n ) F") : nat_scope.

Notation "\min_ ( i 'in' A | P ) F" :=
  (\big[minn/(\max_(i in A | P) F)]_(i in A | P%B) F%N)
    (at level 41, F at level 41, i, A at level 50,
     format "\min_ ( i 'in' A | P ) F") : nat_scope.

Notation "\min_ ( i 'in' A ) F" :=
  (\big[minn/(\max_(i in A) F)]_(i in A) F%N)
    (at level 41, F at level 41, i, A at level 50,
     format "\min_ ( i 'in' A ) F") : nat_scope.
*)
Section Sbignat.
  Variable (I:eqType).
  Implicit Types (P:pred I).

  Lemma bigmin_hasC r P F: ~~ has P r -> \min_(i <- r | P i) F i = 0.
  Proof. exact : Sbig_hasC. Qed.

  Lemma bigmin_sup r P F M:
    {in r, forall x, P x -> F x <= M -> \min_(i <- r | P i) F i <= M}.
  Proof. exact : (@CTT_Sbigl _ _ leq_CTTpred). Qed.

  Lemma bigmin_infP r P F m:
    has P r ->
    reflect {in r, forall x, P x -> m <= F x} (m <= \min_(i <- r | P i) F i).
  Proof. exact : (@CTT_SbigrP _ _ leq_CTTpred). Qed.

  Lemma Sbigmax_inf r P F m:
    {in r, forall x,
                P x -> m <= F x -> m <= \Sbig[maxn/0]_(i <- r | P i) F i}.
  Proof. exact : (@CTT_Sbigl _ _ geq_CTTpred). Qed.

  Lemma Sbigmax_supP r P F M:
    has P r ->
    reflect {in r, forall x, P x -> F x <= M}
            (\Sbig[maxn/0]_(i <- r | P i) F i <= M).
  Proof. exact : (@CTT_SbigrP _ _ geq_CTTpred). Qed.

  Lemma bigmax_inf r P F m:
    {in r, forall x, P x -> m <= F x -> m <= \max_(i <- r | P i) F i}.
  Proof.
    move => x. rewrite -(Sbig_big maxn0). exact : Sbigmax_inf.
  Qed.

  Lemma bigmax_supP r P F M:
    reflect {in r, forall x, P x -> F x <= M} (\max_(i <- r | P i) F i <= M).
  Proof.
    case Hhas : (has P r).
    - rewrite -(Sbig_big maxn0). exact : Sbigmax_supP.
    - rewrite big_hasC; last by rewrite Hhas.
      apply /(iffP idP) =>[_ x|]; last by rewrite leq0n.
        by move /hasPn : Hhas => H /H /negP.
  Qed.

End Sbignat.
(*
Section leq_bigmin.

  Variable (I:finType).
  Implicit Types (P:pred I).

  Lemma leq_bigmin_cond P F i0: P i0 -> \min_(i | P i) F i <= F i0.
  Proof.
    move => HPi0.
    elim : (index_enum I) (mem_index_enum i0) =>[|i r IHr];
      first by rewrite !big_nil. rewrite in_cons bigmin_cons.
    case /orP; first (move /eqP =><-; rewrite HPi0).
    - case : ifP =>//. by rewrite geq_minl.
    - move => Hin. have : has P r; first by (apply /hasP; exists i0).
      move =>->/=. by case : ifP; rewrite ?geq_min (IHr Hin) ?orbT.
  Qed.

  Lemma bigmin_eq_arg P F i0:
    P i0 -> \min_(i | P i) F i = F [arg min_(i < i0 | P i) F i].
  Proof.
    move => HPi0. case : arg_minP =>// x HPx Hleq.
    elim : (index_enum I) (mem_index_enum x) =>[|i r IHr];
      first by rewrite !big_nil. rewrite in_cons bigmin_cons.
    case /orP; first (move /eqP =><-; rewrite HPx).
    - case : ifP =>//={IHr} Hhas.
      apply : (big_ind (fun k => minn (F x) k = F x)).
      + apply : minn_idPl.
        elim : r Hhas =>[|j r IHr]//=. rewrite big_cons. case : ifP =>//Hj _.
        by rewrite leq_max (Hleq _ Hj).
      + move => j k. move /minn_idPl => Hj. move /minn_idPl => Hk.
        apply /minn_idPl. by rewrite leq_min Hj Hk.
      + move => k Hk. apply /minn_idPl. exact : Hleq.
      + case : ifP =>/=;
                   last by (move /negbT /hasPn => H; move /H; rewrite HPx).
        case : ifP =>// HPi _. move /IHr =>->. apply /minn_idPr. exact : Hleq.
  Qed.

End leq_bigmin.
*)