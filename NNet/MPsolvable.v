From mathcomp
     Require Import ssreflect ssrnat ssrbool ssrfun eqtype seq div fintype
     tuple finfun bigop.
Add LoadPath "../mylib".
Require Export mylib.
Require Export NNet_sub_def NNet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export NNetDef.

(* ***************************** *)
Section NNet_lemma.

  Variable (S:NNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let actf := @NNactf S.
  Let parameter := MP1parameter S.
  Let MPparameter := MPparameter S.

  Definition MPsolvable Idim l Odim (P:pred (I ^ Idim))
             (f:I ^ Idim -> O ^ Odim) :=
    exists p:MPparameter Idim l Odim, {in P, f =1 MPfunction p}.

  Lemma MPsolvable_eqr Idim (l:seq nat) Odim P (f1 f2:I ^ Idim -> O ^ Odim):
    {in P, f1 =1 f2} -> MPsolvable l P f1 -> MPsolvable l P f2.
  Proof.
    move => Hf [p HMP]. exists p => input Hinput.
      by rewrite -(Hf _ Hinput) (HMP _ Hinput).
  Qed.

  Lemma MPsolvable_subset Idim l Odim P1 P2 (f:I ^ Idim -> O ^ Odim):
    {subset P2 <= P1} -> MPsolvable l P1 f -> MPsolvable l P2 f.
  Proof. move => HP [p H]. exists p => input /HP. exact : H. Qed.

  Lemma MPsolvable_eql Idim l Odim P1 P2 (f:I ^ Idim -> O ^ Odim):
    P1 =i P2 -> MPsolvable l P1 f -> MPsolvable l P2 f.
  Proof. move => HP. apply : MPsolvable_subset => x. by rewrite HP. Qed.

  Lemma MPsolvable_cons Idim Hdim l Odim P (f:I ^ Idim -> O ^ Odim)
        P' (f':I ^ Hdim -> O ^ Odim) (p:parameter Idim Hdim) :
    MPsolvable l P' f' ->
    {subset P <= P' \o @actf Hdim \o MP1 p} ->
    {in P, f =1 f' \o @actf Hdim \o MP1 p} ->
    MPsolvable (Hdim :: l) P f.
  Proof.
    case => p' HMP HP Hf. exists (p,p') => input Hinput. rewrite (Hf _ Hinput).
    exact : HMP (HP _ Hinput).
  Qed.

  Lemma MPsolvable_rcons Idim l Hdim Odim P (f:I ^ Idim -> O ^ Odim)
        (f':I ^ Idim -> O ^ Hdim) (p:parameter Hdim Odim):
    MPsolvable l P f' ->
    {in P, f =1 MP1 p \o @actf Hdim \o f'} ->
    MPsolvable (rcons l Hdim) P f.
  Proof.
    case => p' HMP Hf. exists (MPparameter_rcons p' p) => input Hinput.
    rewrite (Hf _ Hinput) MPfunction_rcons /= (HMP _ Hinput).
      by rewrite MPparameter_last_rcons MPparameter_belast_rcons.
  Qed.

  Lemma MPsolvable_in0 Idim l Odim P (f:I ^ Idim -> O ^ Odim):
   0 \in l -> MPsolvable l P f -> exists y, {in P, f =1 (fun => y)}.
  Proof.
    move => Hl [p Hp]. case : (MPfunction_in0 p Hl) =>[y Heq].
      by exists y => input /Hp ->.
  Qed.

  Lemma MPfunction_solvable Idim l Odim P (p:MPparameter Idim l Odim):
    MPsolvable l P (MPfunction p).
  Proof. by exists p => input. Qed.

  Lemma MPsolvable_trans Idim l1 Hdim l2 Odim P1 P2
        (f1:I ^ Idim -> O ^ Hdim) (f2:I ^ Hdim -> O ^ Odim):
    MPsolvable l1 P1 f1 -> MPsolvable l2 P2 f2 ->
    {subset P1 <= P2 \o @actf Hdim \o f1} ->
    MPsolvable (l1 ++ Hdim :: l2) P1 (f2 \o @actf Hdim \o f1).
  Proof.
    move => [p1 Hf1] [p2 Hf2].
    exists (MPparameter_app p1 p2) => input Hinput /=.
    rewrite MPfunction_app (Hf1 _ Hinput) Hf2 // unfold_in -(Hf1 _ Hinput).
    exact : H Hinput.
  Qed.
(*
  Lemma MPsolvable_trans_rev Idim l1 Hdim l2 Odim (f:I ^ Idim -> O ^ Odim):
    MPsolvable (l1 ++ Hdim :: l2) f ->
    exists (f1:I ^ Idim -> O ^ Hdim) (f2:I ^ Hdim -> O ^ Odim),
      [/\ f =1 f2 \o @actf Hdim \o f1, MPsolvable l1 f1 & MPsolvable l2 f2].
  Proof.
    elim : l1 => [|dim l1 IHl1]/= in Idim f *; case => p Hf.
    - exists (MP1 p.1), (MPfunction p.2).
      split=>//; exact : MPfunction_solvable.
    - case : (IHl1 _ (MPfunction p.2)); first exact : MPfunction_solvable.
      move => f1 [f2] [Hp2 HMP Hl2].
      exists (f1 \o @actf dim \o MP1 p.1), f2. split =>[input||]//=.
      + by rewrite Hf /= Hp2.
      + exact : MPsolvable_cons HMP _.
  Qed.
*)
  Lemma MPsolvable_ex (o0:O) (c0:C) Idim l Odim P:
    exists (f:I ^ Idim -> O ^ Odim), MPsolvable l P f.
  Proof.
    exists (MPfunction (@MPparameter_zero _ o0 c0 Idim l Odim)).
    exact : MPfunction_solvable.
  Qed.

  Lemma MPsolvable_Idim0_nil (c0:C) Odim P (f:I ^ 0 -> O ^ Odim):
    MPsolvable [::] P f.
  Proof.
    exists (coeff_zero c0 _ _,f (empty_index _)) => input /=.
    by rewrite MP1_Idim0 eq_empty_index.
  Qed.

  Lemma MPsolvable_Odim0 (o0:O) (c0:C) Idim l P (f:I ^ Idim -> O ^ 0):
    MPsolvable l P f.
  Proof.
    exists (MPparameter_zero o0 c0) => input. by rewrite !eq_empty_index.
  Qed.

  Lemma MPsolvable_O1 (o0:O) (c0:C) :
    all_equal_to o0 ->
    forall Idim l Odim P (f:I ^ Idim -> O ^ Odim), MPsolvable l P f.
  Proof.
    move => H Idim l Odim P f. exists (MPparameter_zero o0 c0) => input.
    by rewrite !(eq_index1 H).
  Qed.

  Lemma MPsolvable_pred0 (o0:O) (c0:C) Idim l Odim (f:I ^ Idim -> O ^ Odim):
    MPsolvable l pred0 f.
  Proof. by exists (MPparameter_zero o0 c0). Qed.

  Lemma MPsolvable_shift Idim l Odim P
        (f:I ^ Idim -> O ^ Odim) (bias:O ^ Odim):
    MPsolvable l P f ->
    MPsolvable l P (fun input => [ffun j : 'I_Odim => op (f input j) (bias j)]).
  Proof.
    case.
    elim : l =>[|Hdim l IHl] in Idim P f *=> p Hf.
    - exists (p.1,[ffun j => op (p.2 j) (bias j)]) => input /=.
        by rewrite MP1_op_bias =>/Hf ->.
    - apply : MPsolvable_cons =>[|input _|input /Hf ->];
        first exact : (@IHl _ predT (MPfunction p.2) p.2).
      + by rewrite unfold_in.
      + exact /ffunP.
  Qed.
(*
  Lemma MPsolvable_appW Idim1 Idim2 l Odim P
        P (f:I ^ (Idim1 + Idim2) -> O ^ Odim) input':
    MPsolvable l f ->
    MPsolvable l (fun input => f (index_app input input')).
  Proof.
    case : l =>[|Hdim l][p H].
    - exists ([ffun i => index_projl (p.1 i)],
              MP1 ([ffun i => index_projr (p.1 i)],p.2) input') => input.
        by rewrite H /= MP1_appI index_projl_app index_projr_app.
    - exists (([ffun i => index_projl (p.1.1 i)],
               MP1 ([ffun i => index_projr (p.1.1 i)],p.1.2) input'),p.2)
      => input.
        by rewrite H /= MP1_appI index_projl_app index_projr_app.
  Qed.
 *)
End NNet_lemma.

(* ***************************** *)
Section monoNNet_lemma.

  Variable (S:monoNNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let id := @NNid S.

End monoNNet_lemma.

(* ***************************** *)
Section idCNNet_lemma.

  Variable (S:idCNNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let id := @NNid S.
  Let idC := @NNidC S.
  Let parameter := @MP1parameter S.
  Let MPparameter := @MPparameter S.

  Lemma MPsolvable_bias Idim l Odim P (bias:O ^ Odim):
    MPsolvable l P (fun _ :I ^ Idim => bias).
  Proof.
    elim : l =>[|Hdim l IHl] in Idim P *.
    - exists (coeff0 _ _ _, bias) => input /= _. by rewrite MP1_coeff0.
    - exact : (MPsolvable_cons (P' := predT) (p:=MP1parameter0 S _ _)).
  Qed.

  Lemma MPsolvable_constant Idim l Odim P (f:I ^ Idim -> O ^ Odim) bias:
    {in P, forall x, f x = bias} -> MPsolvable l P f.
  Proof.
    move => H.
    by apply : MPsolvable_eqr (MPsolvable_bias _ _ bias) => input /H ->.
  Qed.

  Lemma MPsolvable_Idim0 l Odim P (f:I ^ 0 -> O ^ Odim): MPsolvable l P f.
  Proof.
    apply : MPsolvable_eqr (MPsolvable_bias _ _ _) => input.
    by rewrite eq_empty_index.
  Qed.

  Lemma MPsolvable_I1 (i0:I) :
    all_equal_to i0 ->
    forall Idim l Odim P (f:I ^ Idim -> O ^ Odim), MPsolvable l P f.
  Proof.
    move => HI Idim l Odim P f.
    apply : MPsolvable_eqr (MPsolvable_bias _ _ _) => input.
    by rewrite (eq_index1 HI).
  Qed.

End idCNNet_lemma.

(* ***************************** *)
Section comoNNet_lemma.
End comoNNet_lemma.

(* ***************************** *)
Section comidCNNet_lemma.

  Variable (S:comidCNNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let op := @NNop S.
  Let action := @NNaction S.
  Let id := @NNid S.
  Let idC := @NNidC S.
  Let actf := @NNactf S.
  Let parameter := @MP1parameter S.
  Let MPparameter := MPparameter S.

  Lemma MPsolvable_sum Idim1 l1 Odim1 Idim2 l2 Odim2
        P1 (f1:I ^ Idim1 -> O ^ Odim1) P2 (f2:I ^ Idim2 -> O ^ Odim2):
    size l1 = size l2 -> MPsolvable l1 P1 f1 -> MPsolvable l2 P2 f2 ->
    MPsolvable (l1 +l l2)
               (fun input => P1 (index_projl input) && P2 (index_projr input))
               (fun input =>
                  index_app (f1 (index_projl input)) (f2 (index_projr input))).
  Proof.
    move => Hsize [p1 Hf1] [p2 Hf2].
    exists (MPparameter_sum p1 p2) => input /andP [] /Hf1 -> /Hf2 ->.
    by rewrite MPfunction_sum.
  Qed.

  Lemma MPsolvable_sumO Idim l1 l2 Odim1 Odim2
        P1 (f1:I ^ Idim -> O ^ Odim1) P2 (f2:I ^ Idim -> O ^ Odim2):
    size l1 = size l2 -> MPsolvable l1 P1 f1 -> MPsolvable l2 P2 f2 ->
    MPsolvable (l1 +l l2) [predI P1 & P2]
               (fun input:I ^ Idim => index_app (f1 input) (f2 input)).
  Proof.
    case : l1 l2 =>[|Hdim1 l1][|Hdim2 l2]=>//.
    - move =>_ [p1 H1] [p2 H2].
      exists (index_app p1.1 p2.1,index_app p1.2 p2.2)
      => input /andP [] /H1 -> /H2 ->/=. by rewrite MP1_sumO.
    - case => Hsize [p1 H1] [p2 H2].
      exists ((index_app p1.1.1 p2.1.1,index_app p1.1.2 p2.1.2),
              MPparameter_sum p1.2 p2.2) => input /andP [] /H1 -> /H2 ->/=.
      by rewrite (MPfunction_sum _ _ _ Hsize) MP1_sumO actf_app
                 index_projl_app index_projr_app.
  Qed.
(*
  Lemma NNet_Psolvable_seq Idim Odim (prob:I ^ Idim -> O ^ Odim):
    forall n (L:(seq nat) ^ Odim),
      (forall (j:'I_Odim), size (L j) = n)
      -> (forall (j:'I_Odim),
             NNet_Psolvable (L j)
                           (fun input:I ^ Idim
                            => [ffun _:'I_1 => prob input j]))
      -> NNet_Psolvable (\big[(seqop addn)/[::]]_(j < Odim) (L j)) prob.
  Proof.
    move => n.
    elim : Odim => [|Odim IHOdim] in prob * => L Hsize HNNS.
    - exact : NNet_Psolvable_Odim0 idC.
    - move : addn1 prob L Hsize HNNS =><-.
      case : Odim addn1 IHOdim => [->| Odim addn1] IHOdim prob L Hsize HNNS.
      + rewrite big_ord_recl big_ord0 seqopidr.
        apply : NNet_Psolvable_eq_prob (HNNS ord0) => input.
        apply /ffunP => i. by rewrite !ffunE f_I_1_ord0.
      + have : (fun input => index_app (index_projl (prob input))
                                       (index_projr (prob input))) =1 prob.
        move => input /=. exact : index_app_proj.
        move => Hprob. apply : (NNet_Psolvable_eq_prob Hprob).
        rewrite big_split_ord. apply : NNet_Psolvable_appl.
        rewrite !size_big_seqop_ord. rewrite !(eq_bigmax (k:=n)) =>//.
        * rewrite (eq_bigr [ffun i=> L (lshift 1 i)]). apply : IHOdim => j.
          - by rewrite ffunE Hsize.
          - rewrite ffunE. apply : NNet_Psolvable_eq_prob (HNNS (lshift 1 j)).
            move => input /=. apply /ffunP => i. by rewrite !ffunE.
          - move => j Htrure. by rewrite ffunE.
        * rewrite big_ord_recl big_ord0 Monoid.mulm1.
          apply : NNet_Psolvable_eq_prob (HNNS (rshift Odim.+1 ord0)).
          move => input /=. apply /ffunP => i. by rewrite !ffunE f_I_1_ord0.
  Qed.
*)
End comidCNNet_lemma.

(* ***************************** *)
Section eqneuron1_lemma.
End eqneuron1_lemma.

(* ***************************** *)
Section eqcomoNNet_lemma.

  Variable (S:eqcomoNNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let id := @NNid S.
  Let actf := @NNactf S.

  Lemma MPnil_ex_not_solvable (i0 i1:I) (o0 o1:O) Idim Odim:
    i0 <> i1 -> o0 <> o1 -> 1 < Idim -> 0 < Odim ->
    exists f:I ^ Idim -> O ^ Odim, ~ MPsolvable [::] predT f.
  Proof.
    move /eqP /negbTE. rewrite eq_sym => HI HO HIdim HOdim.
    rewrite -(ltn_predK HIdim) -(ltn_predK HOdim).
    have HIdim1: 1 < Idim.-1.+1 by rewrite (ltn_predK HIdim).
    pose ord1 := Ordinal HIdim1.
    exists (fun input
            => [ffun j => if j == ord0
                          then if ((input ord0) == i0)
                               then if ((input ord1) == i0) then o0 else id
                               else if ((input ord1) == i0) then o1 else id
                          else id]).
    case =>/= p H.
    move /ffunP : (MP1_linear p [ffun i => i0] [ffun i => i1] ord0) => contra.
    move : (contra ord0).
      by rewrite -!(H _ (erefl _)) !ffunE !eq_refl HI !NNopo0.
  Qed.

End eqcomoNNet_lemma.