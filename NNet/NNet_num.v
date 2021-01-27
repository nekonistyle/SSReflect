From mathcomp
     Require Import all_ssreflect.
From mathcomp
     Require Import all_algebra.
Add LoadPath "../mylib".
Require Export mylib mybig myalg.
Require Export NNet_sub_def NNet NNet_alg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export GRing NNetDef NNet_algDef.

Module Import NNet_numDef.

(* ***************************** *)
Module numDomainNNet.

  Record class_of (R:numDomainType) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class *%R (@addrA R)))
      }.

  Section class.
    Variable (R:numDomainType).
    Variable (m:class_of R).
    Definition neuron1_class := neuron1.Class *%R (@addrA R).
    Definition mono_mixin :=
      @mononeuron1.Mixin (neuron1.Pack neuron1_class) _ (@add0r _) (@addr0 _).
    Definition mono_class := mononeuron1.Class mono_mixin.
    Definition idC_mixin :=
      @idCneuron1.Mixin (mononeuron1.Pack mono_class) _ (@mul0r _).
    Definition idC_class := idCneuron1.Class idC_mixin.
    Definition como_mixin :=
      @comoneuron1.Mixin (mononeuron1.Pack mono_class) (@addrC _).
    Definition como_class := comoneuron1.Class como_mixin.
    Definition comidC_class := comidCneuron1.Class como_mixin idC_mixin.
    Definition NNet_class := NNet.Class (NNet_mixin m).
    Definition monoNNet_class := monoNNet.Class mono_mixin NNet_class.
    Definition idCNNet_class := idCNNet.Class idC_mixin NNet_class.
    Definition comoNNet_class := comoNNet.Class como_mixin NNet_class.
    Definition comidCNNet_class :=
      comidCNNet.Class como_mixin idC_mixin NNet_class.
    Definition zmod_class := zmodneuron1.Class (@mul R).
    Definition zmodNNet_class := @zmodNNet.Class _ _ _ zmod_class NNet_class.
    Definition zmodCNNet_class :=
      @zmodCNNet.Class _ _ _ zmod_class NNet_class (@mulrBl _).
    Definition zmodINNet_class :=
      @zmodINNet.Class _ _ _ zmod_class NNet_class (@mulrBr _).
    Definition zmod3NNet_class :=
      @zmod3NNet.Class _ _ _ zmod_class NNet_class (@mulrBl _) (@mulrBr _).
    Definition lmodNNet_class :=
      @lmodNNet.Class _ (regular_lmodType _) NNet_class.
    Definition lalgNNet_class :=
      @lalgNNet.Class _ (regular_lalgType _) NNet_class.
    Definition algNNet_class :=
      @algNNet.Class _ (regular_algType _) NNet_class.
    Definition ringNNet_class := ringNNet.Class NNet_class.
    Definition comRingNNet_class := comRingNNet.Class NNet_class.
    Definition unitRingNNet_class := unitRingNNet.Class NNet_class.
    Definition comUnitRingNNet_class := comUnitRingNNet.Class NNet_class.
    Definition idomainNNet_class := idomainNNet.Class NNet_class.
  End class.

  Section Packing.
    Structure type := Pack {NNetR; _:@class_of NNetR}.
    Variable (cT:type).
    Definition class := let: Pack _ c := cT return class_of (NNetR cT) in c.

    Definition neuron1 := neuron1.Pack (neuron1_class (NNetR cT)).
    Definition mononeuron1 := mononeuron1.Pack (mono_class (NNetR cT)).
    Definition idCneuron1 := idCneuron1.Pack (idC_class (NNetR cT)).
    Definition comoneuron1 := comoneuron1.Pack (como_class (NNetR cT)).
    Definition comidCneuron1 := comidCneuron1.Pack (comidC_class (NNetR cT)).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).
    Definition idCNNet := idCNNet.Pack (idCNNet_class class).
    Definition comoNNet := comoNNet.Pack (comoNNet_class class).
    Definition comidCNNet := comidCNNet.Pack (comidCNNet_class class).
    Definition zmodneuron1 := zmodneuron1.Pack (zmod_class (NNetR cT)).
    Definition zmodNNet := zmodNNet.Pack (zmodNNet_class class).
    Definition zmodCNNet := zmodCNNet.Pack (zmodCNNet_class class).
    Definition zmodINNet := zmodINNet.Pack (zmodINNet_class class).
    Definition zmod3NNet := zmod3NNet.Pack (zmod3NNet_class class).
    Definition lmodNNet := lmodNNet.Pack (lmodNNet_class class).
    Definition lalgNNet := lalgNNet.Pack (lalgNNet_class class).
    Definition algNNet := algNNet.Pack (algNNet_class class).
    Definition ringNNet := ringNNet.Pack (ringNNet_class class).
    Definition comRingNNet := comRingNNet.Pack (comRingNNet_class class).
    Definition unitRingNNet := unitRingNNet.Pack (unitRingNNet_class class).
    Definition comUnitRingNNet :=
      comUnitRingNNet.Pack (comUnitRingNNet_class class).
    Definition idomainNNet := idomainNNet.Pack (idomainNNet_class class).
  End Packing.

  Module Exports.
    Notation numDomainNNetType := type.
    Coercion mono_mixin : numDomainType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : numDomainType >-> idCneuron1.mixin_of.
    Coercion como_mixin : numDomainType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : numDomainType >-> neuron1.class_of.
    Coercion mono_class : numDomainType >-> mononeuron1.class_of.
    Coercion idC_class : numDomainType >-> idCneuron1.class_of.
    Coercion como_class : numDomainType >-> comoneuron1.class_of.
    Coercion comidC_class : numDomainType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : numDomainType >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion zmodCNNet_class : class_of >-> zmodCNNet.class_of.
    Coercion zmodINNet_class : class_of >-> zmodINNet.class_of.
    Coercion zmod3NNet_class : class_of >-> zmod3NNet.class_of.
    Coercion lmodNNet_class : class_of >-> lmodNNet.class_of.
    Coercion lalgNNet_class : class_of >-> lalgNNet.class_of.
    Coercion algNNet_class : class_of >-> algNNet.class_of.
    Coercion ringNNet_class : class_of >-> ringNNet.class_of.
    Coercion comRingNNet_class : class_of >-> comRingNNet.class_of.
    Coercion unitRingNNet_class : class_of >-> unitRingNNet.class_of.
    Coercion comUnitRingNNet_class : class_of >-> comUnitRingNNet.class_of.
    Coercion idomainNNet_class : class_of >-> idomainNNet.class_of.
    Coercion NNetR : numDomainNNetType >-> numDomainType.
    Coercion neuron1 : numDomainNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : numDomainNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : numDomainNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : numDomainNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : numDomainNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : numDomainNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : numDomainNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : numDomainNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : numDomainNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : numDomainNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : numDomainNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : numDomainNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : numDomainNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : numDomainNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : numDomainNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : numDomainNNetType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : numDomainNNetType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion algNNet : numDomainNNetType >-> algNNetType.
    Canonical algNNet.
    Coercion ringNNet : numDomainNNetType >-> ringNNetType.
    Canonical ringNNet.
    Coercion comRingNNet : numDomainNNetType >-> comRingNNetType.
    Canonical comRingNNet.
    Coercion unitRingNNet : numDomainNNetType >-> unitRingNNetType.
    Canonical unitRingNNet.
    Coercion comUnitRingNNet : numDomainNNetType >-> comUnitRingNNetType.
    Canonical comUnitRingNNet.
    Coercion idomainNNet : numDomainNNetType >-> idomainNNetType.
    Canonical idomainNNet.
  End Exports.
End numDomainNNet.
Export numDomainNNet.Exports.

Section numDomainNNet_lemma.
  Variable (R:numDomainNNetType).
  Let actf := @NNactf R.
  Let activation := @NNactivation R.
  Let parameter := @MP1parameter R.
  Let MPparameter := @MPparameter R.

  Section leParameter.
(*    Variable (Idim:nat).*)
    Let Idim := 1.
    Variable (Odim:nat).
    Variable (p:parameter Idim Odim).
(*    Variable (k:'I_Idim).*)
    Let k := ord0 : 'I_Idim.

    Definition leParameter : rel 'I_Odim :=
    fun i j =>
      let wi := p.1 i k in
      let wj := p.1 j k in
      if wj == 0%R then wi == 0%R else
      (le (norm wi * (sg wj * p.2 j)) (norm wj * (sg wi * p.2 i)))%R.

    Lemma leParameter_refl : reflexive leParameter.
    Proof. rewrite /leParameter => x. by case : ifP. Qed.

    Lemma leParameter_trans : transitive leParameter.
    Proof.
      rewrite /leParameter => y x z.
      case : ifPn =>[_/eqP->|]; case : ifP =>[|_]//;
        first by rewrite /sg eqxx normr0 !mul0r mulr0.
      rewrite -normr_gt0 => Hy.
      move /(ler_wpmul2l (normr_ge0 (p.1 z k))).
      rewrite ![(norm (p.1 z _) * (norm _ * _))%R]mulrCA => Hyx.
      move /(ler_wpmul2l (normr_ge0 (p.1 x k))) => Hzy.
      rewrite -(ler_pmul2l Hy) mulrCA. exact : ler_trans Hzy Hyx.
    Qed.

    Lemma leParameter_bottom i j : p.1 i k == 0%R -> leParameter i j.
    Proof.
      rewrite /leParameter => /eqP ->. rewrite /sg eqxx normr0 !mul0r mulr0.
        by case : ifP.
    Qed.

    Lemma leParameter_equivP i j :
      reflect
        (let wi := p.1 i k in
         let wj := p.1 j k in
         if wi == 0%R then wj == 0%R else (wj != 0%R) &&
         (norm wi * (sg wj * p.2 j) == norm wj * (sg wi * p.2 i)))%R
        (equiv leParameter i j).
    Proof.
      rewrite /leParameter. apply : (iffP idP) =>[/andP []|].
      - case : ifP =>[/eqP->/eqP->|_]; first by rewrite eq_refl.
        case : ifP =>[/eqP->|_ Hji Hij]//=. by rewrite eqr_le Hji Hij.
      - rewrite /equiv. case : ifP =>[/eqP->/eqP->|_]; first by rewrite eq_refl.
        case : ifP =>//=_/eqP->. by rewrite lerr.
    Qed.

    Definition leParameterInput i (x:R ^ Idim) :=
      let wi := p.1 i k in le (- (sg wi * p.2 i))%R (norm wi * x k)%R.

    Definition leInputParameter (x:R ^ Idim) i :=
      let wi := p.1 i k in
      (wi != 0%R) && le (norm wi * x k)%R (- (sg wi * p.2 i))%R.

    Lemma leParameter_transPPI j i x:
      leParameter i j -> leParameterInput j x -> leParameterInput i x.
    Proof.
      rewrite /leParameter /leParameterInput.
      case : ifPn =>[_/eqP->|];
        first by rewrite /sg eqxx normr0 !mul0r oppr0.
      rewrite -normr_gt0 ler_oppl
      => Hj H /(ler_wpmul2l (normr_ge0 (p.1 i k))) H'.
      rewrite ler_oppl -(ler_pmul2l Hj) mulrN mulrCA -mulrN.
      exact : ler_trans H' H.
    Qed.

    Lemma leParameter_transIPP j x i:
      leInputParameter x j -> leParameter j i -> leInputParameter x i.
    Proof.
      rewrite /leParameter /leInputParameter =>/andP [].
      case : ifPn =>[_/negbTE->|]//=. rewrite -!normr_gt0 => Hi Hj.
      rewrite ler_oppr =>/(ler_wpmul2l (normr_ge0 (p.1 i k))) H H'.
      rewrite ler_oppr -(ler_pmul2l Hj) mulrN [(_ * (_ * x _))%R]mulrCA -mulrN.
      exact : ler_trans H' H.
    Qed.

    Lemma leParameter_transPIP x i j:
      leParameterInput i x -> leInputParameter x j -> leParameter i j.
    Proof.
      rewrite /leParameterInput /leInputParameter /leParameter.
      case : ifP =>//=_. move /(ler_wpmul2l (normr_ge0 (p.1 j k))).
      rewrite [(_ * (_ * x _))%R]mulrCA => H.
      move /(ler_wpmul2l (normr_ge0 (p.1 i k))) /(ler_trans H).
        by rewrite !mulrN ler_opp2.
    Qed.

    Definition leInput : rel (R ^ Idim) := fun x y => le (x k) (y k).

    Lemma leParameter_transIIP y x i:
      leInput x y -> leInputParameter y i -> leInputParameter x i.
    Proof.
      rewrite /leInput /leInputParameter.
      move /(ler_wpmul2l (normr_ge0 (p.1 i k))) => H /andP []->/=.
      exact : ler_trans H.
    Qed.

    Lemma leParameter_transPII x i y:
      leParameterInput i x -> leInput x y -> leParameterInput i y.
    Proof.
      rewrite /leParameterInput /leInput => H.
      move /(ler_wpmul2l (normr_ge0 (p.1 i k))). exact : ler_trans H.
    Qed.

    Lemma leParameter_transIPI i x y:
      leInputParameter x i -> leParameterInput i y -> leInput x y.
    Proof.
      rewrite /leInputParameter /leParameterInput /leInput =>/andP [].
      rewrite -normr_gt0 => Hi H. move /(ler_trans H).
        by rewrite (ler_pmul2l Hi).
    Qed.

    Lemma leParameterInput_bottom i x:
      p.1 i k == 0%R -> leParameterInput i x.
    Proof.
      rewrite /leParameterInput =>/eqP->.
        by rewrite /sg eqxx normr0 !mul0r oppr0.
    Qed.

    Lemma leInputParameter_bottom x i:
      p.1 i k == 0%R -> ~~ leInputParameter x i.
    Proof. by rewrite /leInputParameter =>/eqP ->; rewrite eqxx. Qed.

    Lemma leParameterInput_comparableParameter x i j:
      leParameterInput i x -> leParameterInput j x ->
      comparable leParameter i j.
    Proof.
      rewrite /leParameterInput /leParameter /comparable.
      move /(ler_wpmul2l (normr_ge0 (p.1 j k))).
      rewrite mulrN [(_ * (norm _ * _))%R]mulrCA ler_oppl => Hix.
      move /(ler_wpmul2l (normr_ge0 (p.1 i k))).
      rewrite mulrN ler_oppl => Hjx.
      case : ifP =>[/eqP->|_].
      - case : ifP =>//=. by rewrite /sg eq_refl normr0 !mul0r mulr0.
      - case : ifP =>[/eqP->|_].
        + by rewrite /sg eq_refl normr0 !mul0r mulr0 lerr.
        + rewrite orbC. exact : (ler_comparable Hix Hjx).
    Qed.

    Definition inputRegion1 x := count (leParameterInput^~ x) (enum 'I_Odim).
    Definition parameterRegion1 i := count (leParameter^~ i) (enum 'I_Odim).

    Lemma lt0parameterRegion1 i : 0 < parameterRegion1 i.
    Proof.
      rewrite /parameterRegion1. rewrite -has_count. apply /hasP.
      exists i. exact : in_enum. exact : leParameter_refl.
    Qed.

    Lemma inputRegion1_max x : inputRegion1 x <= Odim.
    Proof. apply : (leq_trans (count_size _ _)). by rewrite size_enum_ord. Qed.

    Lemma parameterRegion1_max x : parameterRegion1 x <= Odim.
    Proof. apply : (leq_trans (count_size _ _)). by rewrite size_enum_ord. Qed.

    Lemma leInputW x y:
      leInput x y -> inputRegion1 x <= inputRegion1 y.
    Proof.
      rewrite /inputRegion1 => Hxy.
      rewrite sub_count =>// i Hix. exact : leParameter_transPII Hix Hxy.
    Qed.

    Lemma leParameterW i j:
      leParameter i j -> parameterRegion1 i <= parameterRegion1 j.
    Proof.
      rewrite /parameterRegion1 => Hij.
      rewrite sub_count =>// t Hti. exact : leParameter_trans Hti Hij.
    Qed.

    Lemma leInputParameterW x i:
      leInputParameter x i -> inputRegion1 x <= parameterRegion1 i.
    Proof.
      rewrite /parameterRegion1 /inputRegion1 => Hxi.
      rewrite sub_count =>// j Hjx. exact : leParameter_transPIP Hjx Hxi.
    Qed.

    Lemma leParameterInputW i x:
      leParameterInput i x -> parameterRegion1 i <= inputRegion1 x.
    Proof.
      rewrite /inputRegion1 /parameterRegion1 => Hix.
      rewrite sub_count =>// j Hji. exact : leParameter_transPPI Hji Hix.
    Qed.

    Lemma inputRegion1_ex_parameterRegion1 x:
      (exists i, leParameterInput i x) ->
      exists i, leParameterInput i x /\ parameterRegion1 i = inputRegion1 x.
    Proof.
      rewrite /inputRegion1 /parameterRegion1 =>[[i0 Hi0]].
      elim : (enum 'I_Odim) =>[|i s [j [IHj IHeq]]]/=; first by exists i0.
      case Hix : (leParameterInput i x).
      - case Hij : (leParameter i j).
        + exists j. by rewrite Hij IHj IHeq.
        + exists i. move : (leParameterInput_comparableParameter IHj Hix).
          rewrite /comparable Hix Hij leParameter_refl orbF => Hji.
          split =>//=. congr(_ + _). apply /eqP. rewrite eqn_leq.
          apply /andP. split; last rewrite -IHeq; rewrite sub_count =>// t Ht.
          * exact : leParameter_transPPI Ht Hix.
          * exact : leParameter_trans Ht Hji.
      - exists j. rewrite IHj IHeq.
        case Hij : (leParameter i j)=>//.
          by move : (leParameter_transPPI Hij IHj) Hix ->.
    Qed.

  End leParameter.

End numDomainNNet_lemma.

(* ***************************** *)
Module numFieldNNet.

  Record class_of (F:numFieldType) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class *%R (@addrA F)))
      }.

  Section class.
    Variable (F:numFieldType).
    Variable (m:class_of F).
    Definition neuron1_class := neuron1.Class *%R (@addrA F).
    Definition mono_mixin :=
      @mononeuron1.Mixin (neuron1.Pack neuron1_class) _ (@add0r _) (@addr0 _).
    Definition mono_class := mononeuron1.Class mono_mixin.
    Definition idC_mixin :=
      @idCneuron1.Mixin (mononeuron1.Pack mono_class) _ (@mul0r _).
    Definition idC_class := idCneuron1.Class idC_mixin.
    Definition como_mixin :=
      @comoneuron1.Mixin (mononeuron1.Pack mono_class) (@addrC _).
    Definition como_class := comoneuron1.Class como_mixin.
    Definition comidC_class := comidCneuron1.Class como_mixin idC_mixin.
    Definition NNet_class := NNet.Class (NNet_mixin m).
    Definition monoNNet_class := monoNNet.Class mono_mixin NNet_class.
    Definition idCNNet_class := idCNNet.Class idC_mixin NNet_class.
    Definition comoNNet_class := comoNNet.Class como_mixin NNet_class.
    Definition comidCNNet_class :=
      comidCNNet.Class como_mixin idC_mixin NNet_class.
    Definition zmod_class := zmodneuron1.Class (@mul F).
    Definition zmodNNet_class := @zmodNNet.Class _ _ _ zmod_class NNet_class.
    Definition zmodCNNet_class :=
      @zmodCNNet.Class _ _ _ zmod_class NNet_class (@mulrBl _).
    Definition zmodINNet_class :=
      @zmodINNet.Class _ _ _ zmod_class NNet_class (@mulrBr _).
    Definition zmod3NNet_class :=
      @zmod3NNet.Class _ _ _ zmod_class NNet_class (@mulrBl _) (@mulrBr _).
    Definition lmodNNet_class :=
      @lmodNNet.Class _ (regular_lmodType _) NNet_class.
    Definition lalgNNet_class :=
      @lalgNNet.Class _ (regular_lalgType _) NNet_class.
    Definition algNNet_class :=
      @algNNet.Class _ (regular_algType _) NNet_class.
    Definition ringNNet_class := ringNNet.Class NNet_class.
    Definition comRingNNet_class := comRingNNet.Class NNet_class.
    Definition unitRingNNet_class := unitRingNNet.Class NNet_class.
    Definition comUnitRingNNet_class := comUnitRingNNet.Class NNet_class.
    Definition idomainNNet_class := idomainNNet.Class NNet_class.
    Definition fieldNNet_class := fieldNNet.Class NNet_class.
    Definition numDomainNNet_class := numDomainNNet.Class NNet_class.
  End class.

  Section Packing.
    Structure type := Pack {NNetF; _:@class_of NNetF}.
    Variable (cT:type).
    Definition class := let: Pack _ c := cT return class_of (NNetF cT) in c.

    Definition neuron1 := neuron1.Pack (neuron1_class (NNetF cT)).
    Definition mononeuron1 := mononeuron1.Pack (mono_class (NNetF cT)).
    Definition idCneuron1 := idCneuron1.Pack (idC_class (NNetF cT)).
    Definition comoneuron1 := comoneuron1.Pack (como_class (NNetF cT)).
    Definition comidCneuron1 := comidCneuron1.Pack (comidC_class (NNetF cT)).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).
    Definition idCNNet := idCNNet.Pack (idCNNet_class class).
    Definition comoNNet := comoNNet.Pack (comoNNet_class class).
    Definition comidCNNet := comidCNNet.Pack (comidCNNet_class class).
    Definition zmodneuron1 := zmodneuron1.Pack (zmod_class (NNetF cT)).
    Definition zmodNNet := zmodNNet.Pack (zmodNNet_class class).
    Definition zmodCNNet := zmodCNNet.Pack (zmodCNNet_class class).
    Definition zmodINNet := zmodINNet.Pack (zmodINNet_class class).
    Definition zmod3NNet := zmod3NNet.Pack (zmod3NNet_class class).
    Definition lmodNNet := lmodNNet.Pack (lmodNNet_class class).
    Definition lalgNNet := lalgNNet.Pack (lalgNNet_class class).
    Definition algNNet := algNNet.Pack (algNNet_class class).
    Definition ringNNet := ringNNet.Pack (ringNNet_class class).
    Definition comRingNNet := comRingNNet.Pack (comRingNNet_class class).
    Definition unitRingNNet := unitRingNNet.Pack (unitRingNNet_class class).
    Definition comUnitRingNNet :=
      comUnitRingNNet.Pack (comUnitRingNNet_class class).
    Definition idomainNNet := idomainNNet.Pack (idomainNNet_class class).
    Definition fieldNNet := fieldNNet.Pack (fieldNNet_class class).
    Definition numDomainNNet := numDomainNNet.Pack (numDomainNNet_class class).
  End Packing.

  Module Exports.
    Notation numFieldNNetType := type.
    Coercion mono_mixin : numFieldType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : numFieldType >-> idCneuron1.mixin_of.
    Coercion como_mixin : numFieldType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : numFieldType >-> neuron1.class_of.
    Coercion mono_class : numFieldType >-> mononeuron1.class_of.
    Coercion idC_class : numFieldType >-> idCneuron1.class_of.
    Coercion como_class : numFieldType >-> comoneuron1.class_of.
    Coercion comidC_class : numFieldType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : numFieldType >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion zmodCNNet_class : class_of >-> zmodCNNet.class_of.
    Coercion zmodINNet_class : class_of >-> zmodINNet.class_of.
    Coercion zmod3NNet_class : class_of >-> zmod3NNet.class_of.
    Coercion lmodNNet_class : class_of >-> lmodNNet.class_of.
    Coercion lalgNNet_class : class_of >-> lalgNNet.class_of.
    Coercion algNNet_class : class_of >-> algNNet.class_of.
    Coercion ringNNet_class : class_of >-> ringNNet.class_of.
    Coercion comRingNNet_class : class_of >-> comRingNNet.class_of.
    Coercion unitRingNNet_class : class_of >-> unitRingNNet.class_of.
    Coercion comUnitRingNNet_class : class_of >-> comUnitRingNNet.class_of.
    Coercion idomainNNet_class : class_of >-> idomainNNet.class_of.
    Coercion fieldNNet_class : class_of >-> fieldNNet.class_of.
    Coercion numDomainNNet_class : class_of >-> numDomainNNet.class_of.
    Coercion NNetF : numFieldNNetType >-> numFieldType.
    Coercion neuron1 : numFieldNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : numFieldNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : numFieldNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : numFieldNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : numFieldNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : numFieldNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : numFieldNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : numFieldNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : numFieldNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : numFieldNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : numFieldNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : numFieldNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : numFieldNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : numFieldNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : numFieldNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : numFieldNNetType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : numFieldNNetType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion algNNet : numFieldNNetType >-> algNNetType.
    Canonical algNNet.
    Coercion ringNNet : numFieldNNetType >-> ringNNetType.
    Canonical ringNNet.
    Coercion comRingNNet : numFieldNNetType >-> comRingNNetType.
    Canonical comRingNNet.
    Coercion unitRingNNet : numFieldNNetType >-> unitRingNNetType.
    Canonical unitRingNNet.
    Coercion comUnitRingNNet : numFieldNNetType >-> comUnitRingNNetType.
    Canonical comUnitRingNNet.
    Coercion idomainNNet : numFieldNNetType >-> idomainNNetType.
    Canonical idomainNNet.
    Coercion fieldNNet : numFieldNNetType >-> fieldNNetType.
    Canonical fieldNNet.
    Coercion numDomainNNet : numFieldNNetType >-> numDomainNNetType.
    Canonical numDomainNNet.
  End Exports.
End numFieldNNet.
Export numFieldNNet.Exports.

(* ***************************** *)
Module realDomainNNet.

  Record class_of (R:realDomainType) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class *%R (@addrA R)))
      }.

  Section class.
    Variable (R:realDomainType).
    Variable (m:class_of R).
    Definition neuron1_class := neuron1.Class *%R (@addrA R).
    Definition mono_mixin :=
      @mononeuron1.Mixin (neuron1.Pack neuron1_class) _ (@add0r _) (@addr0 _).
    Definition mono_class := mononeuron1.Class mono_mixin.
    Definition idC_mixin :=
      @idCneuron1.Mixin (mononeuron1.Pack mono_class) _ (@mul0r _).
    Definition idC_class := idCneuron1.Class idC_mixin.
    Definition como_mixin :=
      @comoneuron1.Mixin (mononeuron1.Pack mono_class) (@addrC _).
    Definition como_class := comoneuron1.Class como_mixin.
    Definition comidC_class := comidCneuron1.Class como_mixin idC_mixin.
    Definition NNet_class := NNet.Class (NNet_mixin m).
    Definition monoNNet_class := monoNNet.Class mono_mixin NNet_class.
    Definition idCNNet_class := idCNNet.Class idC_mixin NNet_class.
    Definition comoNNet_class := comoNNet.Class como_mixin NNet_class.
    Definition comidCNNet_class :=
      comidCNNet.Class como_mixin idC_mixin NNet_class.
    Definition zmod_class := zmodneuron1.Class (@mul R).
    Definition zmodNNet_class := @zmodNNet.Class _ _ _ zmod_class NNet_class.
    Definition zmodCNNet_class :=
      @zmodCNNet.Class _ _ _ zmod_class NNet_class (@mulrBl _).
    Definition zmodINNet_class :=
      @zmodINNet.Class _ _ _ zmod_class NNet_class (@mulrBr _).
    Definition zmod3NNet_class :=
      @zmod3NNet.Class _ _ _ zmod_class NNet_class (@mulrBl _) (@mulrBr _).
    Definition lmodNNet_class :=
      @lmodNNet.Class _ (regular_lmodType _) NNet_class.
    Definition lalgNNet_class :=
      @lalgNNet.Class _ (regular_lalgType _) NNet_class.
    Definition algNNet_class :=
      @algNNet.Class _ (regular_algType _) NNet_class.
    Definition ringNNet_class := ringNNet.Class NNet_class.
    Definition comRingNNet_class := comRingNNet.Class NNet_class.
    Definition unitRingNNet_class := unitRingNNet.Class NNet_class.
    Definition comUnitRingNNet_class := comUnitRingNNet.Class NNet_class.
    Definition idomainNNet_class := idomainNNet.Class NNet_class.
    Definition numDomainNNet_class := numDomainNNet.Class NNet_class.
  End class.

  Section Packing.
    Structure type := Pack {NNetR; _:@class_of NNetR}.
    Variable (cT:type).
    Definition class := let: Pack _ c := cT return class_of (NNetR cT) in c.

    Definition neuron1 := neuron1.Pack (neuron1_class (NNetR cT)).
    Definition mononeuron1 := mononeuron1.Pack (mono_class (NNetR cT)).
    Definition idCneuron1 := idCneuron1.Pack (idC_class (NNetR cT)).
    Definition comoneuron1 := comoneuron1.Pack (como_class (NNetR cT)).
    Definition comidCneuron1 := comidCneuron1.Pack (comidC_class (NNetR cT)).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).
    Definition idCNNet := idCNNet.Pack (idCNNet_class class).
    Definition comoNNet := comoNNet.Pack (comoNNet_class class).
    Definition comidCNNet := comidCNNet.Pack (comidCNNet_class class).
    Definition zmodneuron1 := zmodneuron1.Pack (zmod_class (NNetR cT)).
    Definition zmodNNet := zmodNNet.Pack (zmodNNet_class class).
    Definition zmodCNNet := zmodCNNet.Pack (zmodCNNet_class class).
    Definition zmodINNet := zmodINNet.Pack (zmodINNet_class class).
    Definition zmod3NNet := zmod3NNet.Pack (zmod3NNet_class class).
    Definition lmodNNet := lmodNNet.Pack (lmodNNet_class class).
    Definition lalgNNet := lalgNNet.Pack (lalgNNet_class class).
    Definition algNNet := algNNet.Pack (algNNet_class class).
    Definition ringNNet := ringNNet.Pack (ringNNet_class class).
    Definition comRingNNet := comRingNNet.Pack (comRingNNet_class class).
    Definition unitRingNNet := unitRingNNet.Pack (unitRingNNet_class class).
    Definition comUnitRingNNet :=
      comUnitRingNNet.Pack (comUnitRingNNet_class class).
    Definition idomainNNet := idomainNNet.Pack (idomainNNet_class class).
    Definition numDomainNNet := numDomainNNet.Pack (numDomainNNet_class class).
  End Packing.

  Module Exports.
    Notation realDomainNNetType := type.
    Coercion mono_mixin : realDomainType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : realDomainType >-> idCneuron1.mixin_of.
    Coercion como_mixin : realDomainType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : realDomainType >-> neuron1.class_of.
    Coercion mono_class : realDomainType >-> mononeuron1.class_of.
    Coercion idC_class : realDomainType >-> idCneuron1.class_of.
    Coercion como_class : realDomainType >-> comoneuron1.class_of.
    Coercion comidC_class : realDomainType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : realDomainType >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion zmodCNNet_class : class_of >-> zmodCNNet.class_of.
    Coercion zmodINNet_class : class_of >-> zmodINNet.class_of.
    Coercion zmod3NNet_class : class_of >-> zmod3NNet.class_of.
    Coercion lmodNNet_class : class_of >-> lmodNNet.class_of.
    Coercion lalgNNet_class : class_of >-> lalgNNet.class_of.
    Coercion algNNet_class : class_of >-> algNNet.class_of.
    Coercion ringNNet_class : class_of >-> ringNNet.class_of.
    Coercion comRingNNet_class : class_of >-> comRingNNet.class_of.
    Coercion unitRingNNet_class : class_of >-> unitRingNNet.class_of.
    Coercion comUnitRingNNet_class : class_of >-> comUnitRingNNet.class_of.
    Coercion idomainNNet_class : class_of >-> idomainNNet.class_of.
    Coercion numDomainNNet_class : class_of >-> numDomainNNet.class_of.
    Coercion NNetR : realDomainNNetType >-> realDomainType.
    Coercion neuron1 : realDomainNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : realDomainNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : realDomainNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : realDomainNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : realDomainNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : realDomainNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : realDomainNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : realDomainNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : realDomainNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : realDomainNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : realDomainNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : realDomainNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : realDomainNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : realDomainNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : realDomainNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : realDomainNNetType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : realDomainNNetType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion algNNet : realDomainNNetType >-> algNNetType.
    Canonical algNNet.
    Coercion ringNNet : realDomainNNetType >-> ringNNetType.
    Canonical ringNNet.
    Coercion comRingNNet : realDomainNNetType >-> comRingNNetType.
    Canonical comRingNNet.
    Coercion unitRingNNet : realDomainNNetType >-> unitRingNNetType.
    Canonical unitRingNNet.
    Coercion comUnitRingNNet : realDomainNNetType >-> comUnitRingNNetType.
    Canonical comUnitRingNNet.
    Coercion idomainNNet : realDomainNNetType >-> idomainNNetType.
    Canonical idomainNNet.
    Coercion numDomainNNet : realDomainNNetType >-> numDomainNNetType.
    Canonical numDomainNNet.
  End Exports.
End realDomainNNet.
Export realDomainNNet.Exports.

Section realDomainNNet_lemma.
  Variable (R:realDomainNNetType).
  Let actf := @NNactf R.
  Let activation := @NNactivation R.
  Let parameter := @MP1parameter R.
  Let MPparameter := @MPparameter R.

  Section leParameter.
(*    Variable (Idim:nat).*)
    Let Idim := 1.
    Let k := ord0 : 'I_Idim.
    Variable (Odim:nat).
    Variable (p:parameter Idim Odim).
    (*    Variable (k:'I_Idim).*)
    Let leParameter := leParameter p.
    Let leParameterInput := leParameterInput p.
    Let leInputParameter := leInputParameter p.
    Let inputRegion1 := inputRegion1 p.
    Let parameterRegion1 := parameterRegion1 p.

    Lemma leInput_total : total (@leInput R).
    Proof.
      rewrite /leInput => x y.
        by case /orP : (ler_total (x k) (y k)) =>->; rewrite ?orbT.
    Qed.

    Lemma leParameter_total : total leParameter.
    Proof.
      rewrite /leParameter /NNet_numDef.leParameter => i j.
      case : ifP =>[/eqP->|_]; case : ifP =>[// /eqP->|_];
        rewrite /sg ?eqxx ?normr0 ?mul0r ?mulr0 ?lerr //.
      exact : ler_total.
    Qed.

    Lemma leParameterInput_total i x :
      leParameterInput i x || leInputParameter x i.
    Proof.
      rewrite /leParameterInput /NNet_numDef.leParameterInput.
      rewrite /leInputParameter /NNet_numDef.leInputParameter.
      case : (p.1 i ord0 =P 0%R) =>[->|_]/=; last exact : ler_total.
        by rewrite /sg eqxx normr0 !mul0r oppr0 lerr.
    Qed.

    Lemma leParameterP i j:
      reflect (parameterRegion1 i <= parameterRegion1 j) (leParameter i j).
    Proof.
      rewrite /parameterRegion1 /NNet_numDef.parameterRegion1.
      rewrite -/leParameter.
      apply /(iffP idP) =>[Hij|]; first exact : leParameterW.
      case Hij : (leParameter i j) (leParameter_total i j) =>//= Hji.
      have Hsub : subpred (leParameter^~ j) (leParameter^~ i)
        by move => t Htj; exact : leParameter_trans Htj Hji.
      move : (in_enum i). elim : (enum 'I_Odim) =>[|t s IHs]//=.
      rewrite inE =>/predU1P [<-|].
      - rewrite {1}/leParameter leParameter_refl Hij /= add1n add0n.
          by case : ltnP (sub_count Hsub s).
      - case Hti : (leParameter t i) =>/=.
        + case : (leParameter t j);
            by rewrite /= !add1n ?add0n ?ltnS =>/IHs // Hs /ltnW.
        + case Htj : (leParameter t j); rewrite /= !add0n //.
          move : (leParameter_trans Htj Hji) Hti.
            by rewrite -/leParameter =>->.
    Qed.

    Lemma leParameterInputP i x:
      reflect (parameterRegion1 i <= inputRegion1 x) (leParameterInput i x).
    Proof.
      rewrite /parameterRegion1 /NNet_numDef.parameterRegion1.
      rewrite /inputRegion1 /NNet_numDef.inputRegion1 -/leParameterInput.
      apply /(iffP idP) =>[Hix|];
        first (rewrite sub_count =>// j Hji;
                exact : leParameter_transPPI Hji Hix).
      case Hix : (leParameterInput i x) (leParameterInput_total i x) =>//= Hxi.
      have Hsub : subpred (leParameterInput^~ x) (leParameter^~ i)
        by move => j Hjx; exact : leParameter_transPIP Hjx Hxi.
      move : (in_enum i). elim : (enum 'I_Odim) =>[|j s IHs]//=.
      rewrite inE =>/predU1P [<-|].
      - rewrite leParameter_refl Hix /= add1n add0n.
          by case : ltnP (sub_count Hsub s).
      - rewrite -/leParameter. case Hji : (leParameter j i) =>/=.
        + case : (leParameterInput j x);
            by rewrite /= !add1n ?add0n ?ltnS =>/IHs // Hs /ltnW.
        + case Hjx : (leParameterInput j x); rewrite /= !add0n //.
          move : (leParameter_transPIP Hjx Hxi) Hji.
            by rewrite -/leParameter =>->.
    Qed.

    Lemma leParameterInput_Region i x:
      parameterRegion1 i <= inputRegion1 x = leParameterInput i x.
    Proof. exact : (sameP idP (leParameterInputP i x)). Qed.

    Lemma ltInputParameter_Region x i:
      inputRegion1 x < parameterRegion1 i -> leInputParameter x i.
    Proof.
      rewrite ltnNge =>/negP /leParameterInputP.
        by case /orP : (leParameterInput_total i x) =>->.
    Qed.

    Lemma ltInput_exParameter x y:
      inputRegion1 x < inputRegion1 y ->
      exists i, leInputParameter x i && leParameterInput i y.
    Proof.
      move => Hxy. move : (Hxy).
      rewrite /inputRegion1 /NNet_numDef.inputRegion1 -/leParameterInput.
      elim : (enum 'I_Odim) =>[|i s IHs]//=.
      case Hix : (leParameterInput i x) (leParameterInput_total i x).
      - case : (leParameterInput i y) (leParameterInput_total i y).
        + move =>_ _/IHs [i0 Hi0]. by exists i0.
        + move => Hyi _. move /(leInputW p) : (leParameter_transIPI Hyi Hix).
          by case : leqP Hxy.
      - case Hiy : (leParameterInput i y) =>/=.
        + move => Hxi _. exists i. by rewrite Hxi Hiy.
        + move =>_ /IHs [i0 Hi0]. by exists i0.
    Qed.

  End leParameter.

  Section lRegionUboundary.
    Let Idim := 1.
    Let k := ord0 : 'I_Idim.

    Lemma max_parameterRegion1 Odim (p:parameter Idim Odim) :
      \max_i (parameterRegion1 p i) = Odim.
    Proof.
      case : Odim =>[|Odim] in p *; first by rewrite big_ord0.
      rewrite (bigmax_eq_arg ord0 (erefl _)). case : arg_maxP =>// i _ H.
      rewrite /parameterRegion1.
      suff : all ((leParameter p)^~ i) (enum 'I_Odim.+1).
      rewrite all_count =>/eqP->. exact : size_enum_ord.
      apply /allP => j _. apply /leParameterP. exact : H _.
    Qed.

    Definition lRegionUboundary Odim (p:parameter Idim Odim.+1) n :=
      let i0 := [arg max_(i > ord0) parameterRegion1 p i] in
      [arg min_(i < i0 | n < parameterRegion1 p i) parameterRegion1 p i].

    Lemma lRegionUboundary_max Odim (p:parameter Idim Odim.+1) n :
      Odim < n ->
      lRegionUboundary p n = [arg max_(i > ord0) parameterRegion1 p i].
    Proof.
      move => Hn. apply : arg_min_pred0 => i. apply : negbTE.
        by rewrite -leqNgt (leq_trans (parameterRegion1_max _ _) Hn).
    Qed.

    Lemma parameterRegion1_lRegionUboundary1
          Odim (p:parameter Idim Odim.+1) n :
      n <= Odim.+1 -> n <= parameterRegion1 p (lRegionUboundary p n).
    Proof.
      rewrite leq_eqVlt =>/orP [/eqP->|].
      - by rewrite (lRegionUboundary_max _ (ltnSn _))
           -(bigmax_eq_arg _ (erefl _)) max_parameterRegion1 ltnSn.
      - rewrite/lRegionUboundary ltnS => Hn. case : arg_minP =>[|i /leqW]//.
          by rewrite -(bigmax_eq_arg _ (erefl _)) max_parameterRegion1 ltnS.
    Qed.

    Lemma parameterRegion1_lRegionUboundary
          Odim (p:parameter Idim Odim.+1) n :
      (n <= Odim.+1) = (n <= parameterRegion1 p (lRegionUboundary p n)).
    Proof.
      case : leqP =>[/parameterRegion1_lRegionUboundary1->|Hn]//.
      rewrite (lRegionUboundary_max _ (ltnW Hn)) -(bigmax_eq_arg _ (erefl _)).
      rewrite max_parameterRegion1. by case : leqP Hn.
    Qed.

    Lemma leq_lRegionUboundary Odim (p:parameter Idim Odim.+1) :
      {homo lRegionUboundary p : n m / n <= m >-> leParameter p n m}.
    Proof.
      move => n m Hnm. apply /leParameterP. case HOdim : (m <= Odim).
      - rewrite /lRegionUboundary. case : arg_minP =>[|i Hn]; last apply.
        + by rewrite -(bigmax_eq_arg _ (erefl _)) max_parameterRegion1 ltnS
                                               (leq_trans Hnm HOdim).
        + case : arg_minP =>[|j Hm _]; last exact : leq_ltn_trans Hnm Hm.
            by rewrite -(bigmax_eq_arg _ (erefl _)) max_parameterRegion1 ltnS.
      - case : leqP HOdim =>// /lRegionUboundary_max->_.
        case : arg_maxP =>[|i _]//; exact.
    Qed.

    Lemma lRegionUboundary_parameterRegion1
          Odim (p:parameter Idim Odim.+1) i :
      leParameter p i (lRegionUboundary p (parameterRegion1 p i)).
    Proof.
      apply /leParameterP.
        by rewrite -parameterRegion1_lRegionUboundary parameterRegion1_max.
    Qed.

    Lemma eq_lRegionUboundary_parameterRegion1
          Odim (p:parameter Idim Odim.+1) n i :
      n.+1 = parameterRegion1 p i ->
      equiv (leParameter p) i (lRegionUboundary p n).
    Proof.
      move => Hn. apply /andP.
      split; apply /leParameterP; rewrite /lRegionUboundary Hn.
      - case : arg_minP =>[|j ->]//. by case : arg_maxP =>[|j _]//; apply.
      - case : arg_minP =>[|j _]. by case : arg_maxP =>[|j _]//; apply.
          by apply.
    Qed.

    Definition eq_lRegionUboundary_NparameterRegion1
          Odim (p:parameter Idim Odim.+1) i :
      equiv (leParameter p) i
            (lRegionUboundary p (parameterRegion1 p i).-1) :=
      eq_lRegionUboundary_parameterRegion1 (prednK (lt0parameterRegion1 _ _)).

    Lemma lRegionUboundary_inputRegion1
          Odim (p:parameter Idim Odim.+1) x :
      inputRegion1 p x <= Odim ->
      leInputParameter p x (lRegionUboundary p (inputRegion1 p x)).
    Proof.
      move => Hx. apply : ltInputParameter_Region.
      rewrite /lRegionUboundary. case : arg_minP =>[|i]//.
        by rewrite -(bigmax_eq_arg _ (erefl _)) max_parameterRegion1 ltnS.
    Qed.

    Lemma le_lRegionUboundary_inputRegion1
          Odim (p:parameter Idim Odim.+1) n x :
      n.+1 = inputRegion1 p x ->
      (exists i, leParameterInput p i x) ->
      leParameterInput p (lRegionUboundary p n) x.
    Proof.
      move => Hn /inputRegion1_ex_parameterRegion1 [i [_ Hi]].
      apply /leParameterInputP. rewrite /lRegionUboundary.
      case : arg_minP =>[|j Hj H].
      - rewrite -(bigmax_eq_arg _ (erefl _)) max_parameterRegion1 Hn.
        exact : inputRegion1_max.
      - move : Hn Hi (H i) =><-->. by apply.
    Qed.

    Lemma le_lRegionUboundary_NinputRegion1
          Odim (p:parameter Idim Odim.+1) x :
      (exists i, leParameterInput p i x) ->
      leParameterInput p (lRegionUboundary p (inputRegion1 p x).-1) x.
    Proof.
      move => H. apply : le_lRegionUboundary_inputRegion1 (prednK _) (H).
      case : H => i /leParameterInputP.
      exact : leq_trans (lt0parameterRegion1 _ i).
    Qed.

  End lRegionUboundary.
End realDomainNNet_lemma.

(* ***************************** *)
Module realFieldNNet.

  Record class_of (F:realFieldType) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class *%R (@addrA F)))
      }.

  Section class.
    Variable (F:realFieldType).
    Variable (m:class_of F).
    Definition neuron1_class := neuron1.Class *%R (@addrA F).
    Definition mono_mixin :=
      @mononeuron1.Mixin (neuron1.Pack neuron1_class) _ (@add0r _) (@addr0 _).
    Definition mono_class := mononeuron1.Class mono_mixin.
    Definition idC_mixin :=
      @idCneuron1.Mixin (mononeuron1.Pack mono_class) _ (@mul0r _).
    Definition idC_class := idCneuron1.Class idC_mixin.
    Definition como_mixin :=
      @comoneuron1.Mixin (mononeuron1.Pack mono_class) (@addrC _).
    Definition como_class := comoneuron1.Class como_mixin.
    Definition comidC_class := comidCneuron1.Class como_mixin idC_mixin.
    Definition NNet_class := NNet.Class (NNet_mixin m).
    Definition monoNNet_class := monoNNet.Class mono_mixin NNet_class.
    Definition idCNNet_class := idCNNet.Class idC_mixin NNet_class.
    Definition comoNNet_class := comoNNet.Class como_mixin NNet_class.
    Definition comidCNNet_class :=
      comidCNNet.Class como_mixin idC_mixin NNet_class.
    Definition zmod_class := zmodneuron1.Class (@mul F).
    Definition zmodNNet_class := @zmodNNet.Class _ _ _ zmod_class NNet_class.
    Definition zmodCNNet_class :=
      @zmodCNNet.Class _ _ _ zmod_class NNet_class (@mulrBl _).
    Definition zmodINNet_class :=
      @zmodINNet.Class _ _ _ zmod_class NNet_class (@mulrBr _).
    Definition zmod3NNet_class :=
      @zmod3NNet.Class _ _ _ zmod_class NNet_class (@mulrBl _) (@mulrBr _).
    Definition lmodNNet_class :=
      @lmodNNet.Class _ (regular_lmodType _) NNet_class.
    Definition lalgNNet_class :=
      @lalgNNet.Class _ (regular_lalgType _) NNet_class.
    Definition algNNet_class :=
      @algNNet.Class _ (regular_algType _) NNet_class.
    Definition ringNNet_class := ringNNet.Class NNet_class.
    Definition comRingNNet_class := comRingNNet.Class NNet_class.
    Definition unitRingNNet_class := unitRingNNet.Class NNet_class.
    Definition comUnitRingNNet_class := comUnitRingNNet.Class NNet_class.
    Definition idomainNNet_class := idomainNNet.Class NNet_class.
    Definition fieldNNet_class := fieldNNet.Class NNet_class.
    Definition numDomainNNet_class := numDomainNNet.Class NNet_class.
    Definition numFieldNNet_class := numFieldNNet.Class NNet_class.
    Definition realDomainNNet_class := realDomainNNet.Class NNet_class.
  End class.

  Section Packing.
    Structure type := Pack {NNetF; _:@class_of NNetF}.
    Variable (cT:type).
    Definition class := let: Pack _ c := cT return class_of (NNetF cT) in c.

    Definition neuron1 := neuron1.Pack (neuron1_class (NNetF cT)).
    Definition mononeuron1 := mononeuron1.Pack (mono_class (NNetF cT)).
    Definition idCneuron1 := idCneuron1.Pack (idC_class (NNetF cT)).
    Definition comoneuron1 := comoneuron1.Pack (como_class (NNetF cT)).
    Definition comidCneuron1 := comidCneuron1.Pack (comidC_class (NNetF cT)).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).
    Definition idCNNet := idCNNet.Pack (idCNNet_class class).
    Definition comoNNet := comoNNet.Pack (comoNNet_class class).
    Definition comidCNNet := comidCNNet.Pack (comidCNNet_class class).
    Definition zmodneuron1 := zmodneuron1.Pack (zmod_class (NNetF cT)).
    Definition zmodNNet := zmodNNet.Pack (zmodNNet_class class).
    Definition zmodCNNet := zmodCNNet.Pack (zmodCNNet_class class).
    Definition zmodINNet := zmodINNet.Pack (zmodINNet_class class).
    Definition zmod3NNet := zmod3NNet.Pack (zmod3NNet_class class).
    Definition lmodNNet := lmodNNet.Pack (lmodNNet_class class).
    Definition lalgNNet := lalgNNet.Pack (lalgNNet_class class).
    Definition algNNet := algNNet.Pack (algNNet_class class).
    Definition ringNNet := ringNNet.Pack (ringNNet_class class).
    Definition comRingNNet := comRingNNet.Pack (comRingNNet_class class).
    Definition unitRingNNet := unitRingNNet.Pack (unitRingNNet_class class).
    Definition comUnitRingNNet :=
      comUnitRingNNet.Pack (comUnitRingNNet_class class).
    Definition idomainNNet := idomainNNet.Pack (idomainNNet_class class).
    Definition fieldNNet := fieldNNet.Pack (fieldNNet_class class).
    Definition numDomainNNet := numDomainNNet.Pack (numDomainNNet_class class).
    Definition numFieldNNet := numFieldNNet.Pack (numFieldNNet_class class).
    Definition realDomainNNet :=
      realDomainNNet.Pack (realDomainNNet_class class).
  End Packing.

  Module Exports.
    Notation realFieldNNetType := type.
    Coercion mono_mixin : realFieldType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : realFieldType >-> idCneuron1.mixin_of.
    Coercion como_mixin : realFieldType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : realFieldType >-> neuron1.class_of.
    Coercion mono_class : realFieldType >-> mononeuron1.class_of.
    Coercion idC_class : realFieldType >-> idCneuron1.class_of.
    Coercion como_class : realFieldType >-> comoneuron1.class_of.
    Coercion comidC_class : realFieldType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : realFieldType >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion zmodCNNet_class : class_of >-> zmodCNNet.class_of.
    Coercion zmodINNet_class : class_of >-> zmodINNet.class_of.
    Coercion zmod3NNet_class : class_of >-> zmod3NNet.class_of.
    Coercion lmodNNet_class : class_of >-> lmodNNet.class_of.
    Coercion lalgNNet_class : class_of >-> lalgNNet.class_of.
    Coercion algNNet_class : class_of >-> algNNet.class_of.
    Coercion ringNNet_class : class_of >-> ringNNet.class_of.
    Coercion comRingNNet_class : class_of >-> comRingNNet.class_of.
    Coercion unitRingNNet_class : class_of >-> unitRingNNet.class_of.
    Coercion comUnitRingNNet_class : class_of >-> comUnitRingNNet.class_of.
    Coercion idomainNNet_class : class_of >-> idomainNNet.class_of.
    Coercion fieldNNet_class : class_of >-> fieldNNet.class_of.
    Coercion numDomainNNet_class : class_of >-> numDomainNNet.class_of.
    Coercion numFieldNNet_class : class_of >-> numFieldNNet.class_of.
    Coercion realDomainNNet_class : class_of >-> realDomainNNet.class_of.
    Coercion NNetF : realFieldNNetType >-> realFieldType.
    Coercion neuron1 : realFieldNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : realFieldNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : realFieldNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : realFieldNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : realFieldNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : realFieldNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : realFieldNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : realFieldNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : realFieldNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : realFieldNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : realFieldNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : realFieldNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : realFieldNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : realFieldNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : realFieldNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : realFieldNNetType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : realFieldNNetType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion algNNet : realFieldNNetType >-> algNNetType.
    Canonical algNNet.
    Coercion ringNNet : realFieldNNetType >-> ringNNetType.
    Canonical ringNNet.
    Coercion comRingNNet : realFieldNNetType >-> comRingNNetType.
    Canonical comRingNNet.
    Coercion unitRingNNet : realFieldNNetType >-> unitRingNNetType.
    Canonical unitRingNNet.
    Coercion comUnitRingNNet : realFieldNNetType >-> comUnitRingNNetType.
    Canonical comUnitRingNNet.
    Coercion idomainNNet : realFieldNNetType >-> idomainNNetType.
    Canonical idomainNNet.
    Coercion fieldNNet : realFieldNNetType >-> fieldNNetType.
    Canonical fieldNNet.
    Coercion numDomainNNet : realFieldNNetType >-> numDomainNNetType.
    Canonical numDomainNNet.
    Coercion numFieldNNet : realFieldNNetType >-> numFieldNNetType.
    Canonical idomainNNet.
    Coercion realDomainNNet : realFieldNNetType >-> realDomainNNetType.
    Canonical realDomainNNet.
  End Exports.
End realFieldNNet.
Export realFieldNNet.Exports.

(* ***************************** *)
End NNet_numDef.
Export numDomainNNet.Exports numFieldNNet.Exports realDomainNNet.Exports
       realFieldNNet.
