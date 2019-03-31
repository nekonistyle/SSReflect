From mathcomp
     Require Import all_ssreflect all_algebra.
Add LoadPath "../mylib".
Require Export mylib mybig myalg.
Require Export NNet_sub_def NNet NNet_alg NNet_num.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export GRing Num NNetDef NNet_algDef NNet_numDef.

Module Import ReLUNNetDef.
(* ***************************** *)
Module numDomain.
  Section Packing.
    Variable (R:numDomainType).

    Definition NNet_mixin :=
      @NNet.Mixin (neuron1.Pack (numDomainNNet.neuron1_class R)) (max^~ 0%R).
    Definition numDomainNNet_class := numDomainNNet.Class NNet_mixin.
    Definition numDomainNNet := numDomainNNet.Pack numDomainNNet_class.
    Let type := numDomainNNet.
    Definition neuron1 := numDomainNNet.neuron1 type.
    Definition mononeuron1 := numDomainNNet.mononeuron1 type.
    Definition idCneuron1 := numDomainNNet.idCneuron1 type.
    Definition comoneuron1 := numDomainNNet.comoneuron1 type.
    Definition comidCneuron1 := numDomainNNet.comidCneuron1 type.
    Definition NNet := numDomainNNet.NNet type.
    Definition monoNNet := numDomainNNet.monoNNet type.
    Definition idCNNet := numDomainNNet.idCNNet type.
    Definition comoNNet := numDomainNNet.comoNNet type.
    Definition comidCNNet := numDomainNNet.comidCNNet type.
    Definition zmodneuron1 := numDomainNNet.zmodneuron1 type.
    Definition zmodNNet := numDomainNNet.zmodNNet type.
    Definition zmodCNNet := numDomainNNet.zmodCNNet type.
    Definition zmodINNet := numDomainNNet.zmodINNet type.
    Definition zmod3NNet := numDomainNNet.zmod3NNet type.
    Definition lmodNNet := numDomainNNet.lmodNNet type.
    Definition lalgNNet := numDomainNNet.lalgNNet type.
    Definition algNNet := numDomainNNet.algNNet type.
    Definition ringNNet := numDomainNNet.ringNNet type.
    Definition comRingNNet := numDomainNNet.comRingNNet type.
    Definition unitRingNNet := numDomainNNet.unitRingNNet type.
    Definition comUnitRingNNet := numDomainNNet.comUnitRingNNet type.
    Definition idomainNNet := numDomainNNet.idomainNNet type.
  End Packing.

  Module Exports.
    Coercion neuron1 : numDomainType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : numDomainType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : numDomainType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : numDomainType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : numDomainType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : numDomainType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : numDomainType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : numDomainType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : numDomainType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : numDomainType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : numDomainType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : numDomainType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : numDomainType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : numDomainType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : numDomainType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : numDomainType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : numDomainType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion algNNet : numDomainType >-> algNNetType.
    Canonical algNNet.
    Coercion ringNNet : numDomainType >-> ringNNetType.
    Canonical ringNNet.
    Coercion comRingNNet : numDomainType >-> comRingNNetType.
    Canonical ringNNet.
    Coercion unitRingNNet : numDomainType >-> unitRingNNetType.
    Canonical unitRingNNet.
    Coercion comUnitRingNNet : numDomainType >-> comUnitRingNNetType.
    Canonical comUnitRingNNet.
    Coercion idomainNNet : numDomainType >-> idomainNNetType.
    Canonical idomainNNet.
    Coercion numDomainNNet : numDomainType >-> numDomainNNetType.
    Canonical numDomainNNet.
  End Exports.
End numDomain.
Export numDomain.Exports.

Section numDomain_lemma.
  Variable (R:numDomainType).
(*
  Lemma ReLU_def : @NNactivation R = (@max R)^~ 0%R.
  Proof. by []. Qed.

  Let ReLU_def : @NNactivation R = (@max R)^~ 0%R := (erefl _).
*)
  Definition ReLU_def : @NNactivation R = (@max R)^~ 0%R := (erefl _).

  Definition ReLUMP Idim l Odim (p:MPparameter R Idim l Odim):
    R ^ Idim -> R ^ Odim := MPfunction p.

End numDomain_lemma.

(* ***************************** *)
Module numField.
  Section Packing.
    Variable (F:numFieldType).

    Definition NNet_mixin :=
      @NNet.Mixin (neuron1.Pack (numDomainNNet.neuron1_class F)) (max^~ 0%R).
    Definition numFieldNNet_class := numFieldNNet.Class NNet_mixin.
    Definition numFieldNNet := numFieldNNet.Pack numFieldNNet_class.
    Let type := numFieldNNet.
    Definition neuron1 := numFieldNNet.neuron1 type.
    Definition mononeuron1 := numFieldNNet.mononeuron1 type.
    Definition idCneuron1 := numFieldNNet.idCneuron1 type.
    Definition comoneuron1 := numFieldNNet.comoneuron1 type.
    Definition comidCneuron1 := numFieldNNet.comidCneuron1 type.
    Definition NNet := numFieldNNet.NNet type.
    Definition monoNNet := numFieldNNet.monoNNet type.
    Definition idCNNet := numFieldNNet.idCNNet type.
    Definition comoNNet := numFieldNNet.comoNNet type.
    Definition comidCNNet := numFieldNNet.comidCNNet type.
    Definition zmodneuron1 := numFieldNNet.zmodneuron1 type.
    Definition zmodNNet := numFieldNNet.zmodNNet type.
    Definition zmodCNNet := numFieldNNet.zmodCNNet type.
    Definition zmodINNet := numFieldNNet.zmodINNet type.
    Definition zmod3NNet := numFieldNNet.zmod3NNet type.
    Definition lmodNNet := numFieldNNet.lmodNNet type.
    Definition lalgNNet := numFieldNNet.lalgNNet type.
    Definition algNNet := numFieldNNet.algNNet type.
    Definition ringNNet := numFieldNNet.ringNNet type.
    Definition comRingNNet := numFieldNNet.comRingNNet type.
    Definition unitRingNNet := numFieldNNet.unitRingNNet type.
    Definition comUnitRingNNet := numFieldNNet.comUnitRingNNet type.
    Definition idomainNNet := numFieldNNet.idomainNNet type.
    Definition fieldNNet := numFieldNNet.fieldNNet type.
    Definition numDomainNNet := numFieldNNet.numDomainNNet type.
  End Packing.

  Module Exports.
    Coercion neuron1 : numFieldType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : numFieldType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : numFieldType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : numFieldType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : numFieldType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : numFieldType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : numFieldType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : numFieldType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : numFieldType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : numFieldType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : numFieldType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : numFieldType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : numFieldType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : numFieldType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : numFieldType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : numFieldType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : numFieldType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion algNNet : numFieldType >-> algNNetType.
    Canonical algNNet.
    Coercion ringNNet : numFieldType >-> ringNNetType.
    Canonical ringNNet.
    Coercion comRingNNet : numFieldType >-> comRingNNetType.
    Canonical ringNNet.
    Coercion unitRingNNet : numFieldType >-> unitRingNNetType.
    Canonical unitRingNNet.
    Coercion comUnitRingNNet : numFieldType >-> comUnitRingNNetType.
    Canonical comUnitRingNNet.
    Coercion idomainNNet : numFieldType >-> idomainNNetType.
    Canonical idomainNNet.
    Coercion fieldNNet : numFieldType >-> fieldNNetType.
    Canonical fieldNNet.
    Coercion numDomainNNet : numFieldType >-> numDomainNNetType.
    Canonical numDomainNNet.
    Coercion numFieldNNet : numFieldType >-> numFieldNNetType.
    Canonical numFieldNNet.
  End Exports.
End numField.
Export numField.Exports.

Section numField_lemma.
End numField_lemma.

(* ***************************** *)
Module realDomain.
  Section Packing.
    Variable (R:realDomainType).

    Definition NNet_mixin :=
      @NNet.Mixin (neuron1.Pack (realDomainNNet.neuron1_class R)) (max^~ 0%R).
    Definition realDomainNNet_class := realDomainNNet.Class NNet_mixin.
    Definition realDomainNNet := realDomainNNet.Pack realDomainNNet_class.
    Let type := realDomainNNet.
    Definition neuron1 := realDomainNNet.neuron1 type.
    Definition mononeuron1 := realDomainNNet.mononeuron1 type.
    Definition idCneuron1 := realDomainNNet.idCneuron1 type.
    Definition comoneuron1 := realDomainNNet.comoneuron1 type.
    Definition comidCneuron1 := realDomainNNet.comidCneuron1 type.
    Definition NNet := realDomainNNet.NNet type.
    Definition monoNNet := realDomainNNet.monoNNet type.
    Definition idCNNet := realDomainNNet.idCNNet type.
    Definition comoNNet := realDomainNNet.comoNNet type.
    Definition comidCNNet := realDomainNNet.comidCNNet type.
    Definition zmodneuron1 := realDomainNNet.zmodneuron1 type.
    Definition zmodNNet := realDomainNNet.zmodNNet type.
    Definition zmodCNNet := realDomainNNet.zmodCNNet type.
    Definition zmodINNet := realDomainNNet.zmodINNet type.
    Definition zmod3NNet := realDomainNNet.zmod3NNet type.
    Definition lmodNNet := realDomainNNet.lmodNNet type.
    Definition lalgNNet := realDomainNNet.lalgNNet type.
    Definition algNNet := realDomainNNet.algNNet type.
    Definition ringNNet := realDomainNNet.ringNNet type.
    Definition comRingNNet := realDomainNNet.comRingNNet type.
    Definition unitRingNNet := realDomainNNet.unitRingNNet type.
    Definition comUnitRingNNet := realDomainNNet.comUnitRingNNet type.
    Definition idomainNNet := realDomainNNet.idomainNNet type.
    Definition numDomainNNet := realDomainNNet.numDomainNNet type.
  End Packing.

  Module Exports.
    Coercion neuron1 : realDomainType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : realDomainType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : realDomainType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : realDomainType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : realDomainType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : realDomainType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : realDomainType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : realDomainType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : realDomainType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : realDomainType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : realDomainType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : realDomainType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : realDomainType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : realDomainType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : realDomainType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : realDomainType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : realDomainType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion algNNet : realDomainType >-> algNNetType.
    Canonical algNNet.
    Coercion ringNNet : realDomainType >-> ringNNetType.
    Canonical ringNNet.
    Coercion comRingNNet : realDomainType >-> comRingNNetType.
    Canonical ringNNet.
    Coercion unitRingNNet : realDomainType >-> unitRingNNetType.
    Canonical unitRingNNet.
    Coercion comUnitRingNNet : realDomainType >-> comUnitRingNNetType.
    Canonical comUnitRingNNet.
    Coercion idomainNNet : realDomainType >-> idomainNNetType.
    Canonical idomainNNet.
    Coercion numDomainNNet : realDomainType >-> numDomainNNetType.
    Canonical numDomainNNet.
    Coercion realDomainNNet : realDomainType >-> realDomainNNetType.
    Canonical realDomainNNet.
  End Exports.
End realDomain.
Export realDomain.Exports.

Section realDomain_lemma.
  Variable (R:realDomainType).
  Let parameter := @MP1parameter R.
  Let MPparameter := @MPparameter R.

  Section lRegion.

(*    Variable (Idim:nat).*)
    Let Idim := 1.
(*    Variable (p:MPparameter Idim [:: Hdim] Odim).*)
(*    Variable (k:'I_Idim).*)
    Let k := ord0 : 'I_Idim.
(*    Let leParameter := leParameter p.1.
    Let leParameterInput := leParameterInput p.1.
    Let leInputParameter := leInputParameter p.1.
    Let inputRegion1 := inputRegion1 p.1.
    Let parameterRegion1 := parameterRegion1 p.1.*)

    Definition lRegion1Parameter1 Hdim Odim
               (p:MPparameter Idim [:: Hdim] Odim) n i : parameter Idim Odim :=
      if (parameterRegion1 p.1 i <= n) == (le 0%R (p.1.1 i k))
      then ([ffun j => [ffun k => (p.2.1 j i) * (p.1.1 i k)]],
            if p.1.1 i k == 0%R then [ffun j => p.2.1 j i * max (p.1.2 i) 0]
            else [ffun j => p.2.1 j i * p.1.2 i])%R
      else MP1parameter0 R _ _.

    Definition lRegion1Parameter Hdim Odim
               (p:MPparameter Idim [:: Hdim] Odim) n :=
      ((\sum_i (lRegion1Parameter1 p n i)) + (coeff0 R _ _,p.2.2))%R.

    Lemma MPfunction_lRegion1 Hdim Odim
          (p:MPparameter Idim [:: Hdim] Odim) input :
      MPfunction p input =
      MP1 (lRegion1Parameter p (inputRegion1 p.1 input)) input.
    Proof.
      apply /ffunP => j. rewrite !ffunE /=.
      rewrite neuron1_bias /neuron1 !big_ord_recl !big_ord0 !ffunE /=.
      rewrite !NNop_add !NNaction_mul !addr0 !addrA. congr(_ + _)%R.
      rewrite big_pair_add /= !sum_ffunE mulr_suml -big_split.
      apply : eq_bigr => i _. rewrite NNaction_mul ffunE /= ReLU_def ffunE /=.
      rewrite /neuron1 big_ord_recl big_ord0 NNop_add NNaction_mul.
      rewrite /lRegion1Parameter1.
      case : ltrgt0P; (case : leqP; last rewrite ltnNge =>/negP);
      move /leParameterInputP =>/=; rewrite /leParameterInput !ffunE /=;
           rewrite ?NNidC0 ?NNid0 ?mul0r ?add0r -?mulrA -?mulrDr;
      rewrite -1?sgr_gt0 -1?sgr_lt0 normrEsg -mulrN -mulrA => Hi Hp.
      - rewrite maxr_l =>//.
          by rewrite -ler_subl_addr sub0r -(ler_pmul2l Hp).
      - rewrite maxr_r; first exact : mulr0.
        rewrite -ler_subr_addr sub0r -(ler_pmul2l Hp). by case : ltrgtP Hi.
      - rewrite maxr_r; first exact : mulr0.
          by rewrite -ler_subr_addr sub0r -(ler_nmul2l Hp).
      - rewrite maxr_l =>//.
        rewrite -ler_subl_addr sub0r -(ler_nmul2l Hp). by case : ltrgtP Hi.
      - by rewrite Hp mul0r !add0r.
      - move : Hp Hi =>->. by rewrite /sg eqxx !mul0r lerr.
    Qed.

    Lemma lRegion1Parameter_max
          Hdim Odim (p:MPparameter Idim [:: Hdim] Odim) n :
      Hdim <= n -> lRegion1Parameter p n = lRegion1Parameter p Hdim.
    Proof.
      rewrite /lRegion1Parameter => Hn. congr(_ + _)%R. apply : eq_bigr => i _.
        by rewrite /lRegion1Parameter1 parameterRegion1_max
                   (leq_trans (parameterRegion1_max _ _) Hn).
    Qed.

    Definition lRegionBoundaryOutput
               Hdim Odim (p:MPparameter Idim [:: Hdim] Odim) n i : R ^ Odim :=
      let wi := p.1.1 i k in
      let p' := lRegion1Parameter p n in
      (MP1 p' [ffun => - sg wi * p.1.2 i] + (- 1 + norm wi) *: p'.2)%R.

    Lemma lRegionBoundaryOutput_continuous
          Hdim Odim (p:MPparameter Idim [:: Hdim.+1] Odim) n :
      lRegionBoundaryOutput p n (lRegionUboundary p.1 n) =
      lRegionBoundaryOutput p n.+1 (lRegionUboundary p.1 n).
    Proof.
      apply /ffunP => j. rewrite !ffunE /=.
      rewrite /neuron1 ![\big[_ / _]_(i < 1) _]big_ord_recl !big_ord0.
      rewrite !NNop_add !NNaction_mul !ffunE /= !addr0 !scalerDr !addrA.
      congr(_ + _)%R. rewrite ![(_ + p.2.2 j)%R]addrC -!addrA. congr(_ + _)%R.
      rewrite !scalerDl !scaleN1r !addNKr.
      rewrite !big_pair_add /= !sum_ffunE !mulr_suml !scaler_mul !mulr_sumr.
      rewrite -!big_split. apply : eq_bigr => i _. rewrite /lRegion1Parameter1.
      case : leqP =>[/leqW->|]//.
      case : (ltngtP n.+1) =>// /eq_lRegionUboundary_parameterRegion1.
      move /leParameter_equivP =>/=.
      by case : ltrgt0P =>[/gtr0_sg->|/ltr0_sg->|];
         rewrite !ffunE /= ?mulr0 ?mul0r addr0
                 ?mulN1r ?mul1r ?mulNr ?mulrN ?eqr_opp;
         [move /andP =>[_/eqP Heq];
                       rewrite [(_ * (p.2.1 _ _ * _))%R]mulrCA -Heq !mulrA addNr
                                                                    ..
         |move =>->/eqP->;
               rewrite /sg eq_refl normr0 !mul0r mulr0 addr0 oppr0].
    Qed.

    Let Odim := 1.
    Let k' := ord0 : 'I_Odim.

    Definition boundaryOutput Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) n :=
      lRegionBoundaryOutput p n (lRegionUboundary p.1 n).

    Definition leBoundary
               Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) : rel nat :=
      fun n m =>
        let wn := p.1.1 (lRegionUboundary p.1 n) k in
        let wm := p.1.1 (lRegionUboundary p.1 m) k in
        (le ((if wm == 0 then 1 else norm wm) * boundaryOutput p n k')
            ((if wn == 0 then 1 else norm wn) * boundaryOutput p m k'))%R.

    Definition leBoundaryOutput
               Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) n x :=
      let wn := p.1.1 (lRegionUboundary p.1 n) k in
      le (boundaryOutput p n k')
         ((if wn == 0 then 1 else norm wn) * MPfunction p x k')%R.

    Definition leOutputBoundary
               Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) x n :=
      let wn := p.1.1 (lRegionUboundary p.1 n) k in
      le ((if wn == 0 then 1 else norm wn) * MPfunction p x k')%R
         (boundaryOutput p n k').

    Lemma le0if1normr (w:R) : le 0%R (if w == 0%R then 1%R else norm w).
    Proof. case : ifP; by rewrite ?ler01 ?normr_ge0. Qed.

    Lemma leBoundary_refl Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) :
      reflexive (leBoundary p).
    Proof. by rewrite /leBoundary => x. Qed.

    Lemma leBoundary_trans Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) :
      transitive (leBoundary p).
    Proof.
      rewrite /leBoundary => y x z.
      pose w n := p.1.1 (lRegionUboundary p.1 n) k.
      case : ifPn=>[_|]; last rewrite -normr_gt0 => Hy;
      rewrite ?mul1r =>/(ler_wpmul2l (le0if1normr (w z)));
      rewrite ![((if _ then _ else norm (w z)) * (_ * _))%R]mulrCA
      => Hxy /(ler_wpmul2l (le0if1normr (w x))); first exact : ler_trans Hxy.
      rewrite [(_ * (norm (w y) * _))%R]mulrCA => Hyz.
      rewrite -(ler_pmul2l Hy). exact : ler_trans Hxy Hyz.
    Qed.

    Lemma leBoundary_transOPP Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) n x m:
      leOutputBoundary p x n -> leBoundary p n m -> leOutputBoundary p x m.
    Proof.
      rewrite /leOutputBoundary /leBoundary.
      pose w n := p.1.1 (lRegionUboundary p.1 n) k.
      case : ifPn =>[_|]; last rewrite -normr_gt0 => Hn;
      rewrite ?normr1 ?mul1r =>/(ler_wpmul2l (le0if1normr (w m)));
      first exact : ler_trans.
      move => Hxn Hnm. by rewrite -(ler_pmul2l Hn) mulrCA (ler_trans Hxn Hnm).
    Qed.

    Lemma leBoundary_transPPO Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) m n x:
      leBoundary p n m -> leBoundaryOutput p m x -> leBoundaryOutput p n x.
    Proof.
      rewrite /leBoundary /leBoundaryOutput.
      pose w n := p.1.1 (lRegionUboundary p.1 n) k.
      case : ifPn =>[_|]; last rewrite -normr_gt0 => Hm;
      rewrite ?normr1 ?mul1r => Hnm /(ler_wpmul2l (le0if1normr (w n)));
      first exact : (ler_trans Hnm).
      move => Hmx. by rewrite -(ler_pmul2l Hm) mulrCA (ler_trans Hnm Hmx).
    Qed.

    Definition leOutput Hdim (p:MPparameter Idim [:: Hdim] Odim)
      : rel (R ^ Idim) := fun x y => le (MPfunction p x k') (MPfunction p y k').

    Lemma leBoundary_transOPO Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) n x y:
      leOutputBoundary p x n -> leBoundaryOutput p n y -> leOutput p x y.
    Proof.
      rewrite /leOutputBoundary /leBoundaryOutput /leOutput.
      case : ifPn =>[_|]; last rewrite -normr_gt0 => Hy Hxn Hny;
        rewrite ?normr1 ?mul1r; first exact : ler_trans.
        by rewrite -(ler_pmul2l Hy) (ler_trans Hxn Hny).
    Qed.

    Lemma posslope_leOutputBoundary_inputRegion1
          Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) x:
      let n := inputRegion1 p.1 x in
      n <= Hdim ->
      le 0%R ((lRegion1Parameter p n).1 k' k) ->
      leOutputBoundary p x n.
    Proof.
      move => n /lRegionUboundary_inputRegion1.
      rewrite /leOutputBoundary /boundaryOutput /lRegionBoundaryOutput.
      rewrite MPfunction_lRegion1 -/n !ffunE /= /neuron1.
      rewrite ![\big[_/_]_(_ < 1) _]big_ord_recl !big_ord0 scaler_mul.
      rewrite mulrDl !NNop_add mulN1r addrA addrK !ffunE addr0 NNaction_mul.
      rewrite /leInputParameter =>/andP [/negPf ->].
        by rewrite !mulrDr !addrA !ler_add2r mulrCA mulNr => H /ler_wpmul2l ->.
    Qed.

    Lemma posslope_leBoundaryOutput_inputRegion1
          Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) x:
      let n := inputRegion1 p.1 x in
      (exists i, leParameterInput p.1 i x && (p.1.1 i k != 0%R)) ->
      le 0%R ((lRegion1Parameter p n).1 k' k) ->
      leBoundaryOutput p n.-1 x.
    Proof.
      move => n [j /andP [Hjx /negbTE HjN0]].
      rewrite /leBoundaryOutput /boundaryOutput
              lRegionBoundaryOutput_continuous.
      case : ifP =>[|_].
      - move : Hjx => /leParameterInputP /pred_leq /(leq_lRegionUboundary p.1).
        move /andP : (eq_lRegionUboundary_NparameterRegion1 p.1 j) =>[Hj _].
        move /(leParameter_trans Hj). rewrite /leParameter.
        case : ifP =>//. by rewrite HjN0.
      - have : exists i, leParameterInput p.1 i x by exists j.
        move /le_lRegionUboundary_NinputRegion1 => H.
        move : Hjx => /leParameterInputP /(leq_trans (lt0parameterRegion1 _ _)).
        move /prednK =>->. rewrite /lRegionBoundaryOutput -/n /leParameterInput.
        rewrite MPfunction_lRegion1 -/n !ffunE /= /neuron1.
        rewrite ![\big[_/_]_(_ < 1) _]big_ord_recl !big_ord0 scaler_mul.
        rewrite !NNop_add !NNaction_mul !ffunE !addr0 mulrDl mulN1r addrA addrK.
        rewrite [(_ * (_ + (_ + _)))%R]mulrDr ler_add2r [(norm _ * _)%R]mulrCA.
        rewrite mulNr =>/ler_wpmul2l. exact.
    Qed.

    Lemma posslope_leBoundary
          Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) n m:
      p.1.1 (lRegionUboundary p.1 n) k != 0%R -> 
      n <= m ->
      (forall t, n <= t <= m -> le 0%R ((lRegion1Parameter p t).1 k' k)) ->
      leBoundary p n m.
    Proof.
      move => Hn.
      elim : m =>[|m IHm];
                   first (rewrite leqn0 =>/eqP->_; exact : leBoundary_refl).
      rewrite leq_eqVlt =>/orP [/eqP->_|]; first exact : leBoundary_refl.
      rewrite ltnS => Hleq Ht.
      apply : (leBoundary_trans (IHm Hleq _)) =>[t /andP [Hnt /leqW Htm]|].
      - apply : Ht. exact /andP.
      - move : (Ht m.+1).
        rewrite (leqW Hleq) leqnn /leBoundary /boundaryOutput.
        rewrite lRegionBoundaryOutput_continuous /lRegionBoundaryOutput.
        rewrite !ffunE /= /neuron1.
        rewrite ![\big[_/_]_(_ < 1) _]big_ord_recl !big_ord0 !scaler_mul.
        rewrite !NNop_add !NNaction_mul !ffunE !addr0 !mulrDl !mulN1r.
        rewrite addrA addrK addrA addrK !mulrDr.
        move : (leq_lRegionUboundary p.1 Hleq) Hn
               (leq_lRegionUboundary p.1 (leqnSn m)). rewrite /leParameter.
        case : ifP =>[/eqP->/eqP->/eqP|_ _ _]//. case : ifP =>[|_]//.
        rewrite ![(norm (p.1.1 (lRegionUboundary _ m.+1) _) * (_ * _))%R]mulrCA.
        rewrite ler_add2r [(norm _ *(_ * (_ * _)))%R]mulrCA => H /(_ isT).
        move /ler_wpmul2l. apply. by rewrite !mulNr mulrN ler_opp2.
    Qed.

    Lemma posslope_leOutput
          Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) x y:
      let nx := inputRegion1 p.1 x in
      let ny := inputRegion1 p.1 y in
      leInput x y ->
      (forall t, nx <= t <= ny -> le 0%R ((lRegion1Parameter p t).1 k' k)) ->
      leOutput p x y.
    Proof.
      move => nx ny Hxy Hslope. move : (Hxy) =>/(leInputW p.1).
      rewrite leq_eqVlt. case /orP =>[/eqP Heq|Hlt].
      - move : (Hslope ny). rewrite /leOutput !MPfunction_lRegion1 /nx /ny Heq.
        rewrite leqnn !ffunE /= /neuron1.
        rewrite ![\big[_/_]_(_ < 1) _]big_ord_recl !big_ord0.
        rewrite !NNop_add !NNaction_mul !addr0 ler_add2r => H.
        exact : (ler_wpmul2l (H _)).
      - have Hnx : nx <= Hdim. rewrite -ltnS.
          exact : (leq_trans Hlt (inputRegion1_max _ _)).
        have HxNb : p.1.1 (lRegionUboundary p.1 nx) k != 0%R.
          apply /negP => /(leInputParameter_bottom x).
          by rewrite (lRegionUboundary_inputRegion1 Hnx).
        apply : (leBoundary_transOPO
                   (posslope_leOutputBoundary_inputRegion1 _ _)) =>//.
        + apply : Hslope. rewrite leqnn /=. exact : ltnW.
        + apply : (leBoundary_transPPO
                     (posslope_leBoundary _ _ _)
                     (posslope_leBoundaryOutput_inputRegion1 _ _)) =>//.
          * by rewrite -ltnS (ltn_predK Hlt).
          * move => t /andP [Hxt Hty]. apply : Hslope. rewrite Hxt /=.
            exact : leq_trans (leq_pred _).
          * case : (ltInput_exParameter Hlt) => i /andP [Hxi Hiy].
            exists i. rewrite Hiy /=.
            apply /negP => /(leInputParameter_bottom x). by rewrite Hxi.
          * apply : Hslope. by rewrite (ltnW Hlt) leqnn.
    Qed.

    Lemma negslope_leBoundaryOutput_inputRegion1
          Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) x:
      let n := inputRegion1 p.1 x in
      n <= Hdim ->
      le ((lRegion1Parameter p n).1 k' k) 0%R ->
      leBoundaryOutput p n x.
    Proof.
      move => n /lRegionUboundary_inputRegion1.
      rewrite /leBoundaryOutput /boundaryOutput /lRegionBoundaryOutput.
      rewrite MPfunction_lRegion1 -/n !ffunE /= /neuron1.
      rewrite ![\big[_/_]_(_ < 1) _]big_ord_recl !big_ord0 scaler_mul.
      rewrite mulrDl !NNop_add mulN1r addrA addrK !ffunE addr0 NNaction_mul.
      rewrite /leInputParameter =>/andP [/negPf ->].
      rewrite !mulrDr !addrA !ler_add2r [(norm _ * (_ * _))%R]mulrCA mulNr => H.
      by move /ler_wnmul2l ->.
    Qed.

    Lemma negslope_leOutputBoundary_inputRegion1
          Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) x:
      let n := inputRegion1 p.1 x in
      (exists i, leParameterInput p.1 i x && (p.1.1 i k != 0%R)) ->
      le ((lRegion1Parameter p n).1 k' k) 0%R ->
      leOutputBoundary p x n.-1.
    Proof.
      move => n [j /andP [Hjx /negbTE HjN0]].
      rewrite /leOutputBoundary /boundaryOutput
              lRegionBoundaryOutput_continuous.
      case : ifP =>[|_].
      - move : Hjx => /leParameterInputP /pred_leq /(leq_lRegionUboundary p.1).
        move /andP : (eq_lRegionUboundary_NparameterRegion1 p.1 j) =>[Hj _].
        move /(leParameter_trans Hj). rewrite /leParameter.
        case : ifP =>//. by rewrite HjN0.
      - have : exists i, leParameterInput p.1 i x by exists j.
        move /le_lRegionUboundary_NinputRegion1 => H.
        move : Hjx => /leParameterInputP /(leq_trans (lt0parameterRegion1 _ _)).
        move /prednK =>->. rewrite /lRegionBoundaryOutput -/n /leParameterInput.
        rewrite MPfunction_lRegion1 -/n !ffunE /= /neuron1.
        rewrite ![\big[_/_]_(_ < 1) _]big_ord_recl !big_ord0 scaler_mul.
        rewrite !NNop_add !NNaction_mul !ffunE !addr0 mulrDl mulN1r addrA addrK.
        rewrite [(_ * (_ + (_ + _)))%R]mulrDr ler_add2r [(norm _ * _)%R]mulrCA.
        rewrite mulNr =>/ler_wnmul2l. exact.
    Qed.

    Lemma negslope_leBoundary
          Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) n m:
      p.1.1 (lRegionUboundary p.1 n) k != 0%R -> 
      n <= m ->
      (forall t, n <= t <= m -> le ((lRegion1Parameter p t).1 k' k) 0%R) ->
      leBoundary p m n.
    Proof.
      move => Hn.
      elim : m =>[|m IHm];
                   first (rewrite leqn0 =>/eqP->_; exact : leBoundary_refl).
      rewrite leq_eqVlt =>/orP [/eqP->_|]; first exact : leBoundary_refl.
      rewrite ltnS => Hleq Ht.
      apply : leBoundary_trans (IHm Hleq _)
      =>[|t /andP [Hnt /leqW Htm]]; last first.
      - apply : Ht. exact /andP.
      - move : (Ht m.+1).
        rewrite (leqW Hleq) leqnn /leBoundary /boundaryOutput.
        rewrite [lRegionBoundaryOutput _ m _]lRegionBoundaryOutput_continuous.
        rewrite /lRegionBoundaryOutput !ffunE /= /neuron1.
        rewrite ![\big[_/_]_(_ < 1) _]big_ord_recl !big_ord0 !scaler_mul.
        rewrite !NNop_add !NNaction_mul !ffunE !addr0 !mulrDl !mulN1r.
        rewrite addrA addrK addrA addrK !mulrDr.
        move : (leq_lRegionUboundary p.1 Hleq) Hn
               (leq_lRegionUboundary p.1 (leqnSn m)). rewrite /leParameter.
        case : ifP =>[/eqP->/eqP->/eqP|_ _ _]//. case : ifP =>[|_]//.
        rewrite ![(norm (p.1.1 (lRegionUboundary _ m.+1) _) * (_ * _))%R]mulrCA.
        rewrite ler_add2r [(norm _ *(_ * (_ * _)))%R]mulrCA => H /(_ isT).
        move /ler_wnmul2l. apply. by rewrite !mulNr mulrN ler_opp2.
    Qed.

    Lemma negslope_leOutput
          Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) x y:
      let nx := inputRegion1 p.1 x in
      let ny := inputRegion1 p.1 y in
      leInput x y ->
      (forall t, nx <= t <= ny -> le ((lRegion1Parameter p t).1 k' k) 0%R) ->
      leOutput p y x.
    Proof.
      move => nx ny Hxy Hslope. move : (Hxy) =>/(leInputW p.1).
      rewrite leq_eqVlt. case /orP =>[/eqP Heq|Hlt].
      - move : (Hslope ny). rewrite /leOutput !MPfunction_lRegion1 /nx /ny Heq.
        rewrite leqnn !ffunE /= /neuron1.
        rewrite ![\big[_/_]_(_ < 1) _]big_ord_recl !big_ord0.
        rewrite !NNop_add !NNaction_mul !addr0 ler_add2r => H.
        exact : (ler_wnmul2l (H _)).
      - have Hnx : nx <= Hdim. rewrite -ltnS.
          exact : (leq_trans Hlt (inputRegion1_max _ _)).
        have HxNb : p.1.1 (lRegionUboundary p.1 nx) k != 0%R.
          apply /negP => /(leInputParameter_bottom x).
          by rewrite (lRegionUboundary_inputRegion1 Hnx).
        apply : (leBoundary_transOPO
                   (negslope_leOutputBoundary_inputRegion1 _ _)) =>//.
        + case : (ltInput_exParameter Hlt) => i /andP [Hxi Hiy].
          exists i. rewrite Hiy /=.
          apply /negP => /(leInputParameter_bottom x). by rewrite Hxi.
        + apply : Hslope. by rewrite (ltnW Hlt) leqnn.
        + apply : (leBoundary_transPPO
                     (negslope_leBoundary _ _ _)
                     (negslope_leBoundaryOutput_inputRegion1 _ _)) =>//.
          * by rewrite -ltnS (ltn_predK Hlt).
          * move => t /andP [Hxt Hty]. apply : Hslope. rewrite Hxt /=.
            exact : leq_trans (leq_pred _).
          * apply : Hslope. rewrite leqnn /=. exact : ltnW.
    Qed.

    Lemma ltOutput_ex_negslope
          Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) x y:
      let nx := inputRegion1 p.1 x in
      let ny := inputRegion1 p.1 y in
      leInput x y ->
      ~~ leOutput p x y ->
      exists t, (nx <= t <= ny) && lt ((lRegion1Parameter p t).1 k' k) 0%R.
    Proof.
      move => nx ny Hinput /negPf Houtput.
      suff : exists t : 'I_ny.+1,
          (nx <= t) && lt ((lRegion1Parameter p t).1 k' k) 0%R.
      case => t /andP [Hleq Hlt]. exists t. by rewrite Hleq Hlt -ltnS ltn_ord.
      apply : existsP. apply : contraT.
      rewrite negb_exists -Houtput => /forallP H.
      apply : (posslope_leOutput Hinput) => t /andP [Hxt].
      rewrite -ltnS =>/inordK Ht. move : Ht Hxt (H (inord t)) =>->->/=.
        by case : lerP.
    Qed.

    Lemma ltOutput_ex_posslope
          Hdim (p:MPparameter Idim [:: Hdim.+1] Odim) x y:
      let nx := inputRegion1 p.1 x in
      let ny := inputRegion1 p.1 y in
      leInput x y ->
      ~~ leOutput p y x ->
      exists t, (nx <= t <= ny) && lt 0%R ((lRegion1Parameter p t).1 k' k).
    Proof.
      move => nx ny Hinput /negPf Houtput.
      suff : exists t : 'I_ny.+1,
          (nx <= t) && lt 0%R ((lRegion1Parameter p t).1 k' k).
      case => t /andP [Hleq Hlt]. exists t. by rewrite Hleq Hlt -ltnS ltn_ord.
      apply : existsP. apply : contraT.
      rewrite negb_exists -Houtput => /forallP H.
      apply : (negslope_leOutput Hinput) => t /andP [Hxt].
      rewrite -ltnS =>/inordK Ht. move : Ht Hxt (H (inord t)) =>->->/=.
        by case : lerP.
    Qed.

  End lRegion.
End realDomain_lemma.

(* ***************************** *)
Module realField.
  Section Packing.
    Variable (F:realFieldType).

    Definition NNet_mixin :=
      @NNet.Mixin (neuron1.Pack (realFieldNNet.neuron1_class F)) (max^~ 0%R).
    Definition realFieldNNet_class := realFieldNNet.Class NNet_mixin.
    Definition realFieldNNet := realFieldNNet.Pack realFieldNNet_class.
    Let type := realFieldNNet.
    Definition neuron1 := realFieldNNet.neuron1 type.
    Definition mononeuron1 := realFieldNNet.mononeuron1 type.
    Definition idCneuron1 := realFieldNNet.idCneuron1 type.
    Definition comoneuron1 := realFieldNNet.comoneuron1 type.
    Definition comidCneuron1 := realFieldNNet.comidCneuron1 type.
    Definition NNet := realFieldNNet.NNet type.
    Definition monoNNet := realFieldNNet.monoNNet type.
    Definition idCNNet := realFieldNNet.idCNNet type.
    Definition comoNNet := realFieldNNet.comoNNet type.
    Definition comidCNNet := realFieldNNet.comidCNNet type.
    Definition zmodneuron1 := realFieldNNet.zmodneuron1 type.
    Definition zmodNNet := realFieldNNet.zmodNNet type.
    Definition zmodCNNet := realFieldNNet.zmodCNNet type.
    Definition zmodINNet := realFieldNNet.zmodINNet type.
    Definition zmod3NNet := realFieldNNet.zmod3NNet type.
    Definition lmodNNet := realFieldNNet.lmodNNet type.
    Definition lalgNNet := realFieldNNet.lalgNNet type.
    Definition algNNet := realFieldNNet.algNNet type.
    Definition ringNNet := realFieldNNet.ringNNet type.
    Definition comRingNNet := realFieldNNet.comRingNNet type.
    Definition unitRingNNet := realFieldNNet.unitRingNNet type.
    Definition comUnitRingNNet := realFieldNNet.comUnitRingNNet type.
    Definition idomainNNet := realFieldNNet.idomainNNet type.
    Definition fieldNNet := realFieldNNet.fieldNNet type.
    Definition numDomainNNet := realFieldNNet.numDomainNNet type.
    Definition numFieldNNet := realFieldNNet.numFieldNNet type.
    Definition realDomainNNet := realFieldNNet.realDomainNNet type.
  End Packing.

  Module Exports.
    Coercion neuron1 : realFieldType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : realFieldType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : realFieldType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : realFieldType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : realFieldType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : realFieldType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : realFieldType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : realFieldType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : realFieldType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : realFieldType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : realFieldType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : realFieldType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : realFieldType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : realFieldType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : realFieldType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : realFieldType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : realFieldType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion algNNet : realFieldType >-> algNNetType.
    Canonical algNNet.
    Coercion ringNNet : realFieldType >-> ringNNetType.
    Canonical ringNNet.
    Coercion comRingNNet : realFieldType >-> comRingNNetType.
    Canonical ringNNet.
    Coercion unitRingNNet : realFieldType >-> unitRingNNetType.
    Canonical unitRingNNet.
    Coercion comUnitRingNNet : realFieldType >-> comUnitRingNNetType.
    Canonical comUnitRingNNet.
    Coercion idomainNNet : realFieldType >-> idomainNNetType.
    Canonical idomainNNet.
    Coercion fieldNNet : realFieldType >-> fieldNNetType.
    Canonical fieldNNet.
    Coercion numDomainNNet : realFieldType >-> numDomainNNetType.
    Canonical numDomainNNet.
    Coercion numFieldNNet : realFieldType >-> numFieldNNetType.
    Canonical numFieldNNet.
    Coercion realDomainNNet : realFieldType >-> realDomainNNetType.
    Canonical realDomainNNet.
    Coercion realFieldNNet : realFieldType >-> realFieldNNetType.
    Canonical realFieldNNet.
  End Exports.
End realField.
Export realField.Exports.

Section realField_lemma.
End realField_lemma.

(* ***************************** *)
End ReLUNNetDef.
Export numDomain.Exports numField.Exports realDomain.Exports realField.Exports.