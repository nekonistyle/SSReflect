From mathcomp
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div fintype
     tuple finfun bigop.
From mathcomp
     Require Import ssralg.
Add LoadPath "../mylib".
Require Export mylib mybig myalg.
Require Export NNet_sub_def NNet NNet_alg MPsolvable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export GRing NNetDef NNet_algDef.

(* ***************************** *)
Section zmodCNNet_lemma.
  Variable (S:zmodCNNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let activation := @NNactivation S.
  Let additivel := @NNadditivel S.
  Let parameter := @MP1parameter S.
  Let MPparameter := @MPparameter S.

  Lemma MPsolvableN1 Idim l Odim P (f:I ^ Idim -> O ^ Odim) j:
    MPsolvable l P f ->
    MPsolvable l P (fun input =>
                    [ffun i => if i == j then (- f input i)%R else f input i]).
  Proof.
    elim : l =>[|Hdim l IHl] in Idim P f *; case =>[p H].
    - exists ([ffun i => if i == j then [ffun k => (- p.1 i k)%R] else p.1 i],
              [ffun i => if i == j then (- p.2 i)%R else p.2 i])
      => input /H ->. apply /ffunP => i. rewrite !ffunE. case : eqP =>//_.
      by rewrite neuron1Nl.
    - apply : MPsolvable_cons=>[|input _|input /H ->].
      + apply : (@IHl _ predT (MPfunction p.2)). exact : MPfunction_solvable.
      + by rewrite unfold_in.
      apply /ffunP => i. by rewrite !ffunE.
  Qed.

End zmodCNNet_lemma.

(* ***************************** *)
Section zmod3NNet_lemma.
  Variable (S:zmod3NNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let actf := @NNactf S.
  Let activation := @NNactivation S.
  Let parameter := @MP1parameter S.
  Let MPparameter := @MPparameter S.

  Lemma MPsolvable_pred1 Idim l Odim (x:I ^ Idim) (f:I ^ Idim -> O ^ Odim):
    MPsolvable l (pred1 x) f.
  Proof.
    apply : MPsolvable_constant => y /=. by rewrite unfold_in =>/eqP ->.
  Qed.

  Let MPsolvable Idim l Odim s := @MPsolvable S Idim l Odim (pred_of_seq s).

  Lemma MPsolvable_nil Idim l Odim (f:I ^ Idim -> O ^ Odim):
    MPsolvable l ([::] : seq (I ^Idim)) f.
  Proof.
    exact : (MPsolvable_eql _ (@MPsolvable_pred0 _ 0%R 0%R _ _ _ _)).
  Qed.

  Lemma MPsolvable_seq1 Idim l Odim (x:I ^ Idim) (f:I ^ Idim -> O ^ Odim):
    MPsolvable l [:: x] f.
  Proof.
    apply : (MPsolvable_eql _ (MPsolvable_pred1 _ x _)) => y.
      by rewrite mem_seq1 unfold_in.
  Qed.

  Definition expressive_number Idim l Odim n :=
    forall (s:seq (I ^ Idim)) (f:I ^ Idim -> O ^ Odim),
      size s = n -> MPsolvable l s f.

  Lemma expressive_number0 Idim l Odim : expressive_number Idim l Odim 0.
  Proof. move =>[]// f _. exact : MPsolvable_nil. Qed.

  Lemma expressive_number1 Idim l Odim : expressive_number Idim l Odim 1.
  Proof. move => [|x []]// f _/=. exact : MPsolvable_seq1. Qed.

  Lemma expressive_number_le Idim l Odim n m :
    n <= m -> expressive_number Idim l Odim m ->
    expressive_number Idim l Odim n.
  Proof.
    move => Hle Hm s f Hsize.
    apply : (MPsolvable_subset
               _ (Hm (s ++ (mkseq (fun => [ffun => 0%R]) (m - n))) f _));
      last by rewrite size_cat Hsize size_mkseq (subnKC Hle).
    exact : (mem_subseq (prefix_subseq _ _)).
  Qed.

  Lemma expressive_number_Idim0 l Odim n : expressive_number 0 l Odim n.
  Proof. move => s f _. exact : MPsolvable_Idim0. Qed.

  Lemma expressive_number_Idim_le Idim1 Idim2 l Odim n :
    Idim1 <= Idim2 -> expressive_number Idim2 l Odim n ->
    expressive_number Idim1 l Odim n.
  Proof.
    move /subnKC =><- H2 s f Hsize.
    case : {H2} (H2 (map (fun x => index_app x [ffun => 0%R]) s)    
                    (fun y => f (index_projl y)));
      first by rewrite size_map Hsize.
    case : l =>[|Hdim l]/= p Hp.
    - exists ([ffun i => index_projl (p.1 i)],p.2) => x Hx.
      move : (Hp _ (map_f _ Hx)). rewrite index_projl_app =>->.
        by rewrite MP1_appI index_projl_app index_projr_app MP1_input0.
    - exists (([ffun i => index_projl (p.1.1 i)],p.1.2),p.2) => x Hx.
      move : (Hp _ (map_f _ Hx)). rewrite index_projl_app =>->/=.
        by rewrite MP1_appI index_projl_app index_projr_app MP1_input0.
  Qed.

  Lemma expressive_number_Odim0 Idim l n : expressive_number Idim l 0 n.
  Proof. move => s f _. exact : (MPsolvable_Odim0 0%R 0%R). Qed.

  Lemma expressive_number_Odim_le Idim l Odim1 Odim2 n :
    Odim1 <= Odim2 -> expressive_number Idim l Odim2 n ->
    expressive_number Idim l Odim1 n.
  Proof.
    move /subnKC =><- H2 s f Hsize.
    case : {H2} (H2 _ (fun x => (index_app (f x) [ffun => 0%R])) Hsize).
    elim /last_ind : l =>[|l Hdim IHl] p Hp.
    - exists (index_projl p.1,index_projl p.2) => x /Hp /=.
      rewrite -{2}[f x](@index_projl_app _ _ (Odim2 - Odim1) _ [ffun=> 0%R])
      =>->. by rewrite MP1_appO index_projl_app.
    - exists (MPparameter_rcons (MPparameter_belast p)
                                (index_projl (MPparameter_last p).1,
                                 index_projl (MPparameter_last p).2))
      => x /Hp /=.
      rewrite -{2}[f x](@index_projl_app _ _ (Odim2 - Odim1) _ [ffun=> 0%R])
      =>->. rewrite !MPfunction_rcons /= !MP1_appO index_projl_app.
        by rewrite MPparameter_last_rcons MPparameter_belast_rcons.
  Qed.

  Definition maximum_expressive_number Idim l Odim n :=
    expressive_number Idim l Odim n /\ ~ expressive_number Idim l Odim n.+1.

  Lemma maximum_expressive_numberP Idim l Odim n:
    maximum_expressive_number Idim l Odim n <->
    (forall m, expressive_number Idim l Odim m <-> m <= n).
  Proof.
    split =>[[Hn Hn1] m|Hm]; split.
    - by case : ltnP =>// Hle /(expressive_number_le Hle) /Hn1.
    - move => Hle. exact : (expressive_number_le Hle).
    - exact /Hm.
    - move /Hm. by rewrite ltnn.
  Qed.

  Lemma maximum_expressive_number_not0 Idim l Odim:
    ~ maximum_expressive_number Idim l Odim 0.
  Proof. case =>_. apply. exact : expressive_number1. Qed.

  Lemma maximum_expressive_number_in0 (i0 i1:I) (o0 o1:O) Idim l Odim :
    0 < Idim -> 0 < Odim -> i0 <> i1 -> o0 <> o1 ->
    0 \in l -> maximum_expressive_number Idim l Odim 1.
  Proof.
    move => HIdim HOdim HI HO Hl.
    split =>[|H]; first exact : expressive_number1.
    move : (H [:: [ffun => i0]; [ffun => i1]]
              (fun x => if (x == [ffun => i0])
                        then [ffun => o0] else [ffun => o1]) erefl).
    case /(MPsolvable_in0 Hl) => y Hy. move : (erefl y) HI HO.
    rewrite -{1}(Hy [ffun => i0]) ?mem_head //.
    rewrite -(Hy [ffun => i1]) ?in_cons ?eq_refl ?orbT //.
    case : ifP =>[/eqP|_]/ffunP Heq.
    - move : (Heq (Ordinal HIdim)). by rewrite !ffunE =>->.
    - move : (Heq (Ordinal HOdim)). by rewrite !ffunE =>->.
      
  Qed.

  Lemma maximum_expressive_number_ex Idim l Odim n:
    ~ expressive_number Idim l Odim n ->
    classically (exists m, maximum_expressive_number Idim l Odim m).
  Proof.
    move => Hn. apply /classicP => Hm. move : Hn.
    elim : n =>[[]|n IHn]; first exact : expressive_number0.
    move => H. apply : IHn => Hn. apply : Hm. exists n. by split.
  Qed.

  Lemma maximum_expressive_number_ex' Idim l Odim n:
    ~ expressive_number Idim l Odim n ->
    ~ ~ exists m, maximum_expressive_number Idim l Odim m.
  Proof.
    move => Hn Hm. move : Hn.
    elim : n =>[[]|n IHn]; first exact : expressive_number0.
    move => H. apply : IHn => Hn. apply : Hm. exists n. by split.
  Qed.

  End zmod3NNet_lemma.
