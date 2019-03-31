From mathcomp
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div fintype
     tuple finfun bigop.
From mathcomp
     Require Import ssralg.
Add LoadPath "../mylib".
Require Export mylib mybig myalg.
Require Export NNet_sub_def NNet.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export GRing NNetDef.

Module Import NNet_algDef.

(* ***************************** *)
Module zmodneuron1.

  Record class_of (I:Type) (O:zmodType) (C:Type) := Class {action:C -> I -> O}.

  Section class.
    Variable (I:Type) (O:zmodType) (C:Type).
    Variable (m:class_of I O C).
    Definition neuron1_class := neuron1.Class (action m) (@addrA _).
    Definition mono_mixin :=
      @mononeuron1.Mixin (neuron1.Pack neuron1_class) _ (@add0r _) (@addr0 _).
    Definition mono_class := mononeuron1.Class mono_mixin.
    Definition como_mixin :=
      @comoneuron1.Mixin (mononeuron1.Pack mono_class) (@addrC _).
    Definition como_class := comoneuron1.Class como_mixin.
  End class.

  Section Packing.
    Structure type := Pack {NNetI; NNetO:zmodType; NNetC;
                            zmod_class : class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT return
                           class_of (NNetI cT) (NNetO cT) (NNetC cT) in c.
    Definition neuron1 := neuron1.Pack (neuron1_class class).
    Definition mononeuron1 := mononeuron1.Pack (mono_class class).
    Definition comoneuron1 := comoneuron1.Pack (como_class class).
  End Packing.

  Module Exports.
    Notation zmodneuron1Type := type.
    Coercion mono_mixin : class_of >-> mononeuron1.mixin_of.
    Coercion como_mixin : class_of >-> comoneuron1.mixin_of.
    Coercion neuron1_class : class_of >-> neuron1.class_of.
    Coercion mono_class : class_of >-> mononeuron1.class_of.
    Coercion como_class : class_of >-> comoneuron1.class_of.
    Coercion NNetO : zmodneuron1Type >-> zmodType.
    Coercion neuron1 : zmodneuron1Type >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : zmodneuron1Type >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion comoneuron1 : zmodneuron1Type >-> comoneuron1Type.
    Canonical comoneuron1.
  End Exports.
End zmodneuron1.
Export zmodneuron1.Exports.

(* ***************************** *)
Module zmodNNet.

  Record class_of (I:Type) (O:zmodType) (C:Type) :=
    Class {
        zmod_class : zmodneuron1.class_of I O C;
        NNet_mixin : NNet.mixin_of (neuron1.Pack zmod_class)
      }.

  Section class.
    Variable (I:Type) (O:zmodType) (C:Type).
    Variable (m:class_of I O C).
    Definition neuron1_class := zmodneuron1.neuron1_class (zmod_class m).
    Definition mono_class := zmodneuron1.mono_class (zmod_class m).
    Definition como_class := zmodneuron1.como_class (zmod_class m).
    Definition NNet_class := NNet.Class (NNet_mixin m).
    Definition monoNNet_class := monoNNet.Class mono_class NNet_class.
    Definition comoNNet_class := comoNNet.Class como_class NNet_class.
  End class.

  Section Packing.

    Structure type := Pack {NNetI; NNetO; NNetC; _:class_of NNetI NNetO NNetC}.

    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT return
                           class_of (NNetI cT) (NNetO cT) (NNetC cT) in c.
    Definition neuron1 := neuron1.Pack (neuron1_class class).
    Definition mononeuron1 := mononeuron1.Pack (mono_class class).
    Definition comoneuron1 := comoneuron1.Pack (como_class class).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).
    Definition comoNNet := comoNNet.Pack (comoNNet_class class).
    Definition zmodneuron1 := zmodneuron1.Pack (zmod_class class).
  End Packing.

  Module Exports.
    Notation zmodNNetType := type.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : class_of >-> neuron1.class_of.
    Coercion mono_class : class_of >-> mononeuron1.class_of.
    Coercion como_class : class_of >-> comoneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion zmod_class : class_of >-> zmodneuron1.class_of.
    Coercion NNetO : zmodNNetType >-> zmodType.
    Coercion neuron1 : zmodNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : zmodNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion comoneuron1 : zmodNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion NNet : zmodNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : zmodNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion comoNNet : zmodNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion zmodneuron1 : zmodNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
  End Exports.
End zmodNNet.
Export zmodNNet.Exports.

Section zmodNNet_lemma.
  Variable (S:zmodNNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let activation := @NNactivation S.
  Let parameter := @MP1parameter S.
  Let MPparameter := @MPparameter S.

  Definition NNop_add (a:O) : NNop a = (add a)%R := (erefl _).
  Definition NNid0 : @NNid S = 0%R := (erefl _).

End zmodNNet_lemma.

(* ***************************** *)
Module zmodCNNet.

  Record class_of (I:Type) (O C:zmodType) :=
    Class {
        zmod_class : zmodneuron1.class_of I O C;
        NNet_mixin : NNet.mixin_of (neuron1.Pack zmod_class);
        action_additivel:
          forall i, additive ((@NNaction (neuron1.Pack zmod_class))^~ i)
      }.

  Section class.
    Variable (I:Type) (O C:zmodType).
    Variable (m:class_of I O C).
    Let class := zmod_class m.
    Definition neuron1_class := zmodneuron1.neuron1_class class.
    Definition mono_class := zmodneuron1.mono_class class.
    Definition idC_mixin :=
      @idCneuron1.Mixin (mononeuron1.Pack mono_class) _
                        (fun x => raddf0 (Additive (action_additivel x))).
    Definition idC_class := idCneuron1.Class idC_mixin.
    Definition como_class := zmodneuron1.como_class class.
    Definition comidC_class := comidCneuron1.Class como_class idC_class.
    Definition NNet_class := NNet.Class (NNet_mixin m).
    Definition monoNNet_class := monoNNet.Class mono_class NNet_class.
    Definition idCNNet_class := idCNNet.Class idC_class NNet_class.
    Definition comoNNet_class := comoNNet.Class como_class NNet_class.
    Definition comidCNNet_class :=
      comidCNNet.Class como_class idC_class NNet_class.
    Definition zmodNNet_class := zmodNNet.Class NNet_class.
  End class.

  Section Packing.
    Structure type := Pack {NNetI; NNetO; NNetC; _:class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT return
                           class_of (NNetI cT) (NNetO cT) (NNetC cT) in c.

    Definition neuron1 := neuron1.Pack (neuron1_class class).
    Definition mononeuron1 := mononeuron1.Pack (mono_class class).
    Definition idCneuron1 := idCneuron1.Pack (idC_class class).
    Definition comoneuron1 := comoneuron1.Pack (como_class class).
    Definition comidCneuron1 := comidCneuron1.Pack (comidC_class class).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).
    Definition idCNNet := idCNNet.Pack (idCNNet_class class).
    Definition comoNNet := comoNNet.Pack (comoNNet_class class).
    Definition comidCNNet := comidCNNet.Pack (comidCNNet_class class).
    Definition zmodneuron1 := zmodneuron1.Pack (zmod_class class).
    Definition zmodNNet := zmodNNet.Pack (zmodNNet_class class).
  End Packing.

  Module Exports.
    Notation zmodCNNetType := type.
    Coercion idC_mixin : class_of >-> idCneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : class_of >-> neuron1.class_of.
    Coercion mono_class : class_of >-> mononeuron1.class_of.
    Coercion idC_class : class_of >-> idCneuron1.class_of.
    Coercion como_class : class_of >-> comoneuron1.class_of.
    Coercion comidC_class : class_of >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : class_of >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion NNetO : zmodCNNetType >-> zmodType.
    Coercion NNetC : zmodCNNetType >-> zmodType.
    Coercion neuron1 : zmodCNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : zmodCNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : zmodCNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : zmodCNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : zmodCNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : zmodCNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : zmodCNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : zmodCNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : zmodCNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : zmodCNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : zmodCNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : zmodCNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Definition NNadditivel S x :=
      Additive (@action_additivel _ _ _ (class S) x).
    Canonical NNadditivel.
  End Exports.
End zmodCNNet.
Export zmodCNNet.Exports.

Section zmodCNNet_lemma.

  Variable (S:zmodCNNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let activation := @NNactivation S.
  Let additivel := @NNadditivel S.
  Let parameter := @MP1parameter S.
  Let MPparameter := @MPparameter S.

  Definition NNidC0 : @NNidC S = 0%R := (erefl _).

  Lemma action_addl i : {morph (action^~ i) : x y / (x + y)%R}.
  Proof. exact : (raddfD (additivel i)). Qed.

  Lemma action0x i : action 0%R i = 0%R.
  Proof. exact : (raddf0 (additivel i)). Qed.

  Lemma actionNx i : {morph (action^~ i) : x / (- x)%R}.
  Proof. exact : (raddfN (additivel i)). Qed.

  Lemma action_mulrl i n : {morph (action^~ i) : x / (x *+ n)%R}.
  Proof. exact : (raddfMn (additivel i)). Qed.

  Lemma action_suml i K r (P:pred K) F:
    action (\sum_(k <- r | P k) F k)%R i =
    (\sum_(k <- r | P k) action (F k) i)%R.
  Proof. exact : (raddf_sum (additivel i)). Qed.

  Lemma neuron1Nl Idim (coeff:C ^ Idim) y input:
    (- neuron1 coeff y input)%R =
    neuron1 (- coeff)%R (- y)%R input.
  Proof.
    rewrite /neuron1 (big_morph _ (@opprD _) refl_equal).
    apply : eq_bigr => i _. by rewrite ffunE -actionNx.
  Qed.

  Lemma MP1Nl Idim Odim (p:parameter Idim Odim) input:
    (- MP1 p input)%R = MP1 (- p.1,- p.2)%R input.
  Proof. apply /ffunP => j. by rewrite !ffunE neuron1Nl. Qed.

  Lemma neuron1_coeff_add Idim (coeff coeff':C ^ Idim) y input:
    neuron1 (coeff + coeff')%R y input =
    (neuron1 coeff 0%R input + neuron1 coeff' y input)%R.
  Proof.
    rewrite ![neuron1 _ y _]neuron1_bias [(_ + (NNop _ _))%R]NNopA.
    rewrite -big_split. congr(NNop _ _).
    apply : big_ind2 =>[|x x' z z'->->|i _]//.
      by rewrite ffunE -/action action_addl.
  Qed.

  Lemma neuron1_parameter_add Idim (coeff coeff':C ^ Idim) y y' input:
    neuron1 (coeff + coeff')%R (y + y')%R input =
    (neuron1 coeff y input + neuron1 coeff' y' input)%R.
  Proof.
    rewrite [neuron1 _ y _]neuron1_bias [neuron1 _ y' _]neuron1_bias.
    rewrite [neuron1 _ (y + _)%R _]neuron1_bias neuron1_coeff_add.
      by rewrite [((NNop _ _) + _)%R]NNopACA.
  Qed.

  Lemma MP1_parameter_add Idim Odim (p p':parameter Idim Odim) input:
    MP1 (p + p')%R input = (MP1 p input + MP1 p' input)%R.
  Proof. apply /ffunP => j. by rewrite !ffunE neuron1_parameter_add. Qed.

End zmodCNNet_lemma.

(* ***************************** *)
Module zmodINNet.

  Record class_of (I O:zmodType) (C:Type) :=
    Class {
        zmod_class : zmodneuron1.class_of I O C;
        NNet_mixin : NNet.mixin_of (neuron1.Pack zmod_class);
        action_additiver: forall c,
            additive (@NNaction (neuron1.Pack zmod_class) c);
      }.

  Section class.
    Variable (I O:zmodType) (C:Type).
    Variable (m:class_of I O C).
    Let class := zmod_class m.
    Definition neuron1_class := zmodneuron1.neuron1_class class.
    Definition mono_class := zmodneuron1.mono_class class.
    Definition como_class := zmodneuron1.como_class class.
    Definition NNet_class := NNet.Class (NNet_mixin m).
    Definition monoNNet_class := monoNNet.Class class NNet_class.
    Definition comoNNet_class := comoNNet.Class class NNet_class.
    Definition zmodNNet_class := zmodNNet.Class NNet_class.
  End class.

  Section Packing.
    Structure type := Pack {NNetI; NNetO; NNetC; _:class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT return
                           class_of (NNetI cT) (NNetO cT) (NNetC cT) in c.

    Definition neuron1 := neuron1.Pack (neuron1_class class).
    Definition mononeuron1 := mononeuron1.Pack (mono_class class).
    Definition comoneuron1 := comoneuron1.Pack (como_class class).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).
    Definition comoNNet := comoNNet.Pack (comoNNet_class class).
    Definition zmodneuron1 := zmodneuron1.Pack (zmod_class class).
    Definition zmodNNet := zmodNNet.Pack (zmodNNet_class class).
  End Packing.

  Module Exports.
    Notation zmodINNetType := type.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : class_of >-> neuron1.class_of.
    Coercion mono_class : class_of >-> mononeuron1.class_of.
    Coercion como_class : class_of >-> comoneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion zmod_class : class_of >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion NNetI : zmodINNetType >-> zmodType.
    Coercion NNetO : zmodINNetType >-> zmodType.
    Coercion neuron1 : zmodINNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : zmodINNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion comoneuron1 : zmodINNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion NNet : zmodINNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : zmodINNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion comoNNet : zmodINNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion zmodneuron1 : zmodINNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : zmodINNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Definition NNadditiver S c :=
      Additive (@action_additiver _ _ _ (class S) c).
    Canonical NNadditiver.
  End Exports.
End zmodINNet.
Export zmodINNet.Exports.

Section zmodINNet_lemma.

  Variable (S:zmodINNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let activation := @NNactivation S.
  Let additiver := @NNadditiver S.
  Let parameter := @MP1parameter S.
  Let MPparameter := @MPparameter S.

  Lemma action_addr c : {morph (action c) : x y / (x + y)%R}.
  Proof. exact : (raddfD (additiver c)). Qed.

  Lemma actionx0 c : action c 0%R = 0%R.
  Proof. exact : (raddf0 (additiver c)). Qed.

  Lemma actionxN c : {morph (action c) : x / (- x)%R}.
  Proof. exact : (raddfN (additiver c)). Qed.

  Lemma action_mulrr c n : {morph (action c) : x / (x *+ n)%R}.
  Proof. exact : (raddfMn (additiver c)). Qed.

  Lemma action_sumr c K r (P:pred K) F:
    action c (\sum_(k <- r | P k) F k)%R =
    (\sum_(k <- r | P k) action c (F k))%R.
  Proof. exact : (raddf_sum (additiver c)). Qed.

  Lemma neuron1_input0 Idim (coeff:C ^ Idim) y:
    neuron1 coeff y [ffun => 0%R] = y.
  Proof.
    rewrite neuron1_bias /neuron1 big1 =>[|i _]; first exact : add0r.
    rewrite ffunE. exact : (raddf0 (additiver _)).
  Qed.

  Lemma neuron1Nr Idim (coeff:C ^ Idim) y input:
    (- neuron1 coeff y input)%R = neuron1 coeff (- y)%R (- input)%R.
  Proof.
    rewrite /neuron1 (big_morph _ (@opprD _) refl_equal).
    apply : eq_bigr => i _. by rewrite ffunE -actionxN.
  Qed.

  Lemma MP1_input0 Idim Odim (p:parameter Idim Odim):
    MP1 p [ffun => 0%R] = p.2.
  Proof. apply /ffunP => j. by rewrite !ffunE neuron1_input0. Qed.

  Lemma MP1Nr Idim Odim (p:parameter Idim Odim) input:
    (- MP1 p input)%R = MP1 (p.1,- p.2)%R (- input)%R.
  Proof. apply /ffunP => j. by rewrite !ffunE neuron1Nr. Qed.

End zmodINNet_lemma.

(* ***************************** *)
Module zmod3NNet.

  Record class_of (I O C:zmodType) :=
    Class {
        zmod_class : zmodneuron1.class_of I O C;
        NNet_mixin : NNet.mixin_of (neuron1.Pack zmod_class);
        action_additivel: forall x,
            additive ((@NNaction (zmodneuron1.Pack zmod_class))^~ x);
        action_additiver: forall c,
            additive (@NNaction (zmodneuron1.Pack zmod_class) c);
      }.

  Section class.
    Variable (I O C:zmodType).
    Variable (m:class_of I O C).
    Let class := zmod_class m.
    Definition neuron1_class := zmodneuron1.neuron1_class class.
    Definition mono_class := zmodneuron1.mono_class class.
    Definition idC_mixin :=
      @idCneuron1.Mixin (mononeuron1.Pack mono_class) _
                        (fun x => raddf0 (Additive (action_additivel x))).
    Definition idC_class := idCneuron1.Class idC_mixin.
    Definition como_class := zmodneuron1.como_class class.
    Definition comidC_class := comidCneuron1.Class como_class idC_class.
    Definition NNet_class := NNet.Class (NNet_mixin m).
    Definition monoNNet_class := monoNNet.Class mono_class NNet_class.
    Definition idCNNet_class := idCNNet.Class idC_class NNet_class.
    Definition comoNNet_class := comoNNet.Class como_class NNet_class.
    Definition comidCNNet_class :=
      comidCNNet.Class como_class idC_class NNet_class.
    Definition zmodNNet_class := zmodNNet.Class NNet_class.
    Definition zmodCNNet_class :=
      zmodCNNet.Class NNet_class (@action_additivel _ _ _ _).
    Definition zmodINNet_class :=
      zmodINNet.Class NNet_class (@action_additiver _ _ _ _).
  End class.

  Section Packing.
    Structure type := Pack {NNetI; NNetO; NNetC; _:class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT return
                           class_of (NNetI cT) (NNetO cT) (NNetC cT) in c.

    Definition neuron1 := neuron1.Pack (neuron1_class class).
    Definition mononeuron1 := mononeuron1.Pack (mono_class class).
    Definition idCneuron1 := idCneuron1.Pack (idC_class class).
    Definition comoneuron1 := comoneuron1.Pack (como_class class).
    Definition comidCneuron1 := comidCneuron1.Pack (comidC_class class).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).
    Definition idCNNet := idCNNet.Pack (idCNNet_class class).
    Definition comoNNet := comoNNet.Pack (comoNNet_class class).
    Definition comidCNNet := comidCNNet.Pack (comidCNNet_class class).
    Definition zmodneuron1 := zmodneuron1.Pack (zmod_class class).
    Definition zmodNNet := zmodNNet.Pack (zmodNNet_class class).
    Definition zmodCNNet := zmodCNNet.Pack (zmodCNNet_class class).
    Definition zmodINNet := zmodINNet.Pack (zmodINNet_class class).
  End Packing.

  Module Exports.
    Notation zmod3NNetType := type.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : class_of >-> neuron1.class_of.
    Coercion mono_class : class_of >-> mononeuron1.class_of.
    Coercion idC_class : class_of >-> idCneuron1.class_of.
    Coercion como_class : class_of >-> comoneuron1.class_of.
    Coercion comidC_class : class_of >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : class_of >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion zmodCNNet_class : class_of >-> zmodCNNet.class_of.
    Coercion zmodINNet_class : class_of >-> zmodINNet.class_of.
    Coercion NNetI : zmod3NNetType >-> zmodType.
    Coercion NNetO : zmod3NNetType >-> zmodType.
    Coercion NNetC : zmod3NNetType >-> zmodType.
    Coercion neuron1 : zmod3NNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : zmod3NNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : zmod3NNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : zmod3NNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : zmod3NNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : zmod3NNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : zmod3NNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : zmod3NNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : zmod3NNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : zmod3NNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : zmod3NNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : zmod3NNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : zmod3NNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : zmod3NNetType >-> zmodINNetType.
    Canonical zmodINNet.
  End Exports.
End zmod3NNet.
Export zmod3NNet.Exports.

(* ***************************** *)
Module lmodNNet.

  Record class_of (C:ringType) (O:lmodType C) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class (@scale _ O) (@addrA _)))
      }.

  Section class.
    Variable (C:ringType) (O:lmodType C).
    Variable (m:class_of O).
    Definition neuron1_class := neuron1.Class (@scale _ O) (@addrA _).
    Definition mono_mixin :=
      @mononeuron1.Mixin (neuron1.Pack neuron1_class) _ (@add0r _) (@addr0 _).
    Definition mono_class := mononeuron1.Class mono_mixin.
    Definition idC_mixin :=
      @idCneuron1.Mixin (mononeuron1.Pack mono_class) _ (@scale0r _ _).
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
    Definition zmod_class := zmodneuron1.Class (@scale _ O).
    Definition zmodNNet_class := @zmodNNet.Class _ _ _ zmod_class NNet_class.
    Definition zmodCNNet_class :=
      @zmodCNNet.Class _ _ _ zmod_class NNet_class
                       (fun x a b => scalerBl a b x).
    Definition zmodINNet_class :=
      @zmodINNet.Class _ _ _ zmod_class NNet_class (@scalerBr _ _).
    Definition zmod3NNet_class :=
      @zmod3NNet.Class _ _ _ zmod_class NNet_class
                       (fun x a b => scalerBl a b x) (@scalerBr _ _).
  End class.

  Section Packing.
    Structure type := Pack {NNetC; NNetO; _:@class_of NNetC NNetO}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ c := cT return class_of (NNetO cT) in c.

    Definition neuron1 := neuron1.Pack (neuron1_class (NNetO cT)).
    Definition mononeuron1 := mononeuron1.Pack (mono_class (NNetO cT)).
    Definition idCneuron1 := idCneuron1.Pack (idC_class (NNetO cT)).
    Definition comoneuron1 := comoneuron1.Pack (como_class (NNetO cT)).
    Definition comidCneuron1 := comidCneuron1.Pack (comidC_class (NNetO cT)).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).
    Definition idCNNet := idCNNet.Pack (idCNNet_class class).
    Definition comoNNet := comoNNet.Pack (comoNNet_class class).
    Definition comidCNNet := comidCNNet.Pack (comidCNNet_class class).
    Definition zmodneuron1 := zmodneuron1.Pack (zmod_class (NNetO cT)).
    Definition zmodNNet := zmodNNet.Pack (zmodNNet_class class).
    Definition zmodCNNet := zmodCNNet.Pack (zmodCNNet_class class).
    Definition zmodINNet := zmodINNet.Pack (zmodINNet_class class).
    Definition zmod3NNet := zmod3NNet.Pack (zmod3NNet_class class).
  End Packing.

  Module Exports.
    Notation lmodNNetType := type.
    Coercion mono_mixin : lmodType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : lmodType >-> idCneuron1.mixin_of.
    Coercion como_mixin : lmodType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : lmodType >-> neuron1.class_of.
    Coercion mono_class : lmodType >-> mononeuron1.class_of.
    Coercion idC_class : lmodType >-> idCneuron1.class_of.
    Coercion como_class : lmodType >-> comoneuron1.class_of.
    Coercion comidC_class : lmodType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : lmodType >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion zmodCNNet_class : class_of >-> zmodCNNet.class_of.
    Coercion zmodINNet_class : class_of >-> zmodINNet.class_of.
    Coercion zmod3NNet_class : class_of >-> zmod3NNet.class_of.
    Coercion NNetC : lmodNNetType >-> ringType.
    Coercion NNetO : lmodNNetType >-> lmodType.
    Coercion neuron1 : lmodNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : lmodNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : lmodNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : lmodNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : lmodNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : lmodNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : lmodNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : lmodNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : lmodNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : lmodNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : lmodNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : lmodNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : lmodNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : lmodNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : lmodNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
  End Exports.
End lmodNNet.
Export lmodNNet.Exports.

Section lmodNNet_lemma.

  Variable (S:lmodNNetType).
  Let O := NNetO S.
  Let C := NNetC S.
  Let activation := @NNactivation S.
  Let parameter := @MP1parameter S.
  Let MPparameter := @MPparameter S.

  Definition NNaction_scale (a:C): NNaction a = scale a := (erefl _).

  Lemma neuron1A Idim (a:C) (coeff:C ^ Idim) (b:O) input:
    (a *: (neuron1 coeff b input))%R =
    neuron1 [ffun i => a * (coeff i)]%R (a *: b)%R input.
  Proof.
    rewrite /neuron1 (big_morph _ (scalerDr _) refl_equal).
    apply /eq_bigr => i _. by rewrite ffunE scalerA.
  Qed.

  Lemma MP1A Idim Odim (a:C) (p:parameter Idim Odim) input:
    (a *: (MP1 p input))%R =
    MP1 ([ffun i => [ffun j => a * (p.1 i j)]], a *: p.2)%R input.
  Proof. apply /ffunP => j. by rewrite !ffunE neuron1A. Qed.

  Lemma neuron1_inner_prod Idim (coeff:C ^ Idim) (b:O) input:
    neuron1 coeff b input = (inner_prod coeff input + b)%R.
  Proof. by rewrite neuron1_bias. Qed.

  Lemma MP1_inner_prod Idim Odim (p:parameter Idim Odim) input:
    MP1 p input = [ffun j => (inner_prod (p.1 j) input + (p.2 j))%R].
  Proof. apply /ffunP => j. by rewrite !ffunE neuron1_inner_prod. Qed.

End lmodNNet_lemma.

(* ***************************** *)
Module lalgNNet.

  Record class_of (C:ringType) (O:lalgType C) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class (@scale _ O) (@addrA _)))
      }.

  Section class.
    Variable (C:ringType) (O:lalgType C).
    Variable (m:class_of O).
    Definition neuron1_class := neuron1.Class (@scale _ O) (@addrA _).
    Definition mono_mixin :=
      @mononeuron1.Mixin (neuron1.Pack neuron1_class) _ (@add0r _) (@addr0 _).
    Definition mono_class := mononeuron1.Class mono_mixin.
    Definition idC_mixin :=
      @idCneuron1.Mixin (mononeuron1.Pack mono_class) _ (@scale0r _ _).
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
    Definition zmod_class := zmodneuron1.Class (@scale _ O).
    Definition zmodNNet_class := @zmodNNet.Class _ _ _ zmod_class NNet_class.
    Definition zmodCNNet_class :=
      @zmodCNNet.Class _ _ _ zmod_class NNet_class
                       (fun x a b => scalerBl a b x).
    Definition zmodINNet_class :=
      @zmodINNet.Class _ _ _ zmod_class NNet_class (@scalerBr _ _).
    Definition zmod3NNet_class :=
      @zmod3NNet.Class _ _ _ zmod_class NNet_class
                       (fun x a b => scalerBl a b x) (@scalerBr _ _).
    Definition lmodNNet_class := lmodNNet.Class NNet_class.
  End class.

  Section Packing.
    Structure type := Pack {NNetC; NNetO; _:@class_of NNetC NNetO}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ c := cT return class_of (NNetO cT) in c.

    Definition neuron1 := neuron1.Pack (neuron1_class (NNetO cT)).
    Definition mononeuron1 := mononeuron1.Pack (mono_class (NNetO cT)).
    Definition idCneuron1 := idCneuron1.Pack (idC_class (NNetO cT)).
    Definition comoneuron1 := comoneuron1.Pack (como_class (NNetO cT)).
    Definition comidCneuron1 := comidCneuron1.Pack (comidC_class (NNetO cT)).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).
    Definition idCNNet := idCNNet.Pack (idCNNet_class class).
    Definition comoNNet := comoNNet.Pack (comoNNet_class class).
    Definition comidCNNet := comidCNNet.Pack (comidCNNet_class class).
    Definition zmodneuron1 := zmodneuron1.Pack (zmod_class (NNetO cT)).
    Definition zmodNNet := zmodNNet.Pack (zmodNNet_class class).
    Definition zmodCNNet := zmodCNNet.Pack (zmodCNNet_class class).
    Definition zmodINNet := zmodINNet.Pack (zmodINNet_class class).
    Definition zmod3NNet := zmod3NNet.Pack (zmod3NNet_class class).
    Definition lmodNNet := lmodNNet.Pack (lmodNNet_class class).
  End Packing.

  Module Exports.
    Notation lalgNNetType := type.
    Coercion mono_mixin : lalgType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : lalgType >-> idCneuron1.mixin_of.
    Coercion como_mixin : lalgType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : lalgType >-> neuron1.class_of.
    Coercion mono_class : lalgType >-> mononeuron1.class_of.
    Coercion idC_class : lalgType >-> idCneuron1.class_of.
    Coercion como_class : lalgType >-> comoneuron1.class_of.
    Coercion comidC_class : lalgType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : lalgType >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion zmodCNNet_class : class_of >-> zmodCNNet.class_of.
    Coercion zmodINNet_class : class_of >-> zmodINNet.class_of.
    Coercion zmod3NNet_class : class_of >-> zmod3NNet.class_of.
    Coercion lmodNNet_class : class_of >-> lmodNNet.class_of.
    Coercion NNetC : lalgNNetType >-> ringType.
    Coercion NNetO : lalgNNetType >-> lalgType.
    Coercion neuron1 : lalgNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : lalgNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : lalgNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : lalgNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : lalgNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : lalgNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : lalgNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : lalgNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : lalgNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : lalgNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : lalgNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : lalgNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : lalgNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : lalgNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : lalgNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : lalgNNetType >-> lmodNNetType.
    Canonical lmodNNet.
  End Exports.
End lalgNNet.
Export lalgNNet.Exports.

(* ***************************** *)
Module algNNet.

  Record class_of (C:ringType) (O:algType C) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class (@scale _ O) (@addrA _)))
      }.

  Section class.
    Variable (C:ringType) (O:algType C).
    Variable (m:class_of O).
    Definition neuron1_class := neuron1.Class (@scale _ O) (@addrA _).
    Definition mono_mixin :=
      @mononeuron1.Mixin (neuron1.Pack neuron1_class) _ (@add0r _) (@addr0 _).
    Definition mono_class := mononeuron1.Class mono_mixin.
    Definition idC_mixin :=
      @idCneuron1.Mixin (mononeuron1.Pack mono_class) _ (@scale0r _ _).
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
    Definition zmod_class := zmodneuron1.Class (@scale _ O).
    Definition zmodNNet_class := @zmodNNet.Class _ _ _ zmod_class NNet_class.
    Definition zmodCNNet_class :=
      @zmodCNNet.Class _ _ _ zmod_class NNet_class
                       (fun x a b => scalerBl a b x).
    Definition zmodINNet_class :=
      @zmodINNet.Class _ _ _ zmod_class NNet_class (@scalerBr _ _).
    Definition zmod3NNet_class :=
      @zmod3NNet.Class _ _ _ zmod_class NNet_class
                       (fun x a b => scalerBl a b x) (@scalerBr _ _).
    Definition lmodNNet_class := lmodNNet.Class NNet_class.
    Definition lalgNNet_class := lalgNNet.Class NNet_class.
  End class.

  Section Packing.
    Structure type := Pack {NNetC; NNetO; _:@class_of NNetC NNetO}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ c := cT return class_of (NNetO cT) in c.

    Definition neuron1 := neuron1.Pack (neuron1_class (NNetO cT)).
    Definition mononeuron1 := mononeuron1.Pack (mono_class (NNetO cT)).
    Definition idCneuron1 := idCneuron1.Pack (idC_class (NNetO cT)).
    Definition comoneuron1 := comoneuron1.Pack (como_class (NNetO cT)).
    Definition comidCneuron1 := comidCneuron1.Pack (comidC_class (NNetO cT)).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).
    Definition idCNNet := idCNNet.Pack (idCNNet_class class).
    Definition comoNNet := comoNNet.Pack (comoNNet_class class).
    Definition comidCNNet := comidCNNet.Pack (comidCNNet_class class).
    Definition zmodneuron1 := zmodneuron1.Pack (zmod_class (NNetO cT)).
    Definition zmodNNet := zmodNNet.Pack (zmodNNet_class class).
    Definition zmodCNNet := zmodCNNet.Pack (zmodCNNet_class class).
    Definition zmodINNet := zmodINNet.Pack (zmodINNet_class class).
    Definition zmod3NNet := zmod3NNet.Pack (zmod3NNet_class class).
    Definition lmodNNet := lmodNNet.Pack (lmodNNet_class class).
    Definition lalgNNet := lalgNNet.Pack (lalgNNet_class class).
  End Packing.

  Module Exports.
    Notation algNNetType := type.
    Coercion mono_mixin : algType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : algType >-> idCneuron1.mixin_of.
    Coercion como_mixin : algType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : algType >-> neuron1.class_of.
    Coercion mono_class : algType >-> mononeuron1.class_of.
    Coercion idC_class : algType >-> idCneuron1.class_of.
    Coercion como_class : algType >-> comoneuron1.class_of.
    Coercion comidC_class : algType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : algType >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion zmodCNNet_class : class_of >-> zmodCNNet.class_of.
    Coercion zmodINNet_class : class_of >-> zmodINNet.class_of.
    Coercion zmod3NNet_class : class_of >-> zmod3NNet.class_of.
    Coercion lmodNNet_class : class_of >-> lmodNNet.class_of.
    Coercion lalgNNet_class : class_of >-> lalgNNet.class_of.
    Coercion NNetC : algNNetType >-> ringType.
    Coercion NNetO : algNNetType >-> algType.
    Coercion neuron1 : algNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : algNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : algNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : algNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : algNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : algNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : algNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : algNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : algNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : algNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : algNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : algNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : algNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : algNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : algNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : algNNetType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : algNNetType >-> lalgNNetType.
    Canonical lalgNNet.
  End Exports.
End algNNet.
Export algNNet.Exports.

(* ***************************** *)
Module ringNNet.

  Record class_of (R:ringType) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class *%R (@addrA R)))
      }.

  Section class.
    Variable (R:ringType).
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
  End Packing.

  Module Exports.
    Notation ringNNetType := type.
    Coercion mono_mixin : ringType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : ringType >-> idCneuron1.mixin_of.
    Coercion como_mixin : ringType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : ringType >-> neuron1.class_of.
    Coercion mono_class : ringType >-> mononeuron1.class_of.
    Coercion idC_class : ringType >-> idCneuron1.class_of.
    Coercion como_class : ringType >-> comoneuron1.class_of.
    Coercion comidC_class : ringType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : ringType >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion zmodCNNet_class : class_of >-> zmodCNNet.class_of.
    Coercion zmodINNet_class : class_of >-> zmodINNet.class_of.
    Coercion zmod3NNet_class : class_of >-> zmod3NNet.class_of.
    Coercion lmodNNet_class : class_of >-> lmodNNet.class_of.
    Coercion lalgNNet_class : class_of >-> lalgNNet.class_of.
    Coercion NNetR : ringNNetType >-> ringType.
    Coercion neuron1 : ringNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : ringNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : ringNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : ringNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : ringNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : ringNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : ringNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : ringNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : ringNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : ringNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : ringNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : ringNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : ringNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : ringNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : ringNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : ringNNetType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : ringNNetType >-> lalgNNetType.
    Canonical lalgNNet.
  End Exports.
End ringNNet.
Export ringNNet.Exports.

Section ringNNet_lemma.
  Variable (S:ringNNetType).

  Definition NNaction_mul (a:S) : NNaction a  = mul a := (erefl _).

End ringNNet_lemma.
(* ***************************** *)
Module comRingNNet.

  Record class_of (R:comRingType) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class *%R (@addrA R)))
      }.

  Section class.
    Variable (R:comRingType).
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
  End Packing.

  Module Exports.
    Notation comRingNNetType := type.
    Coercion mono_mixin : comRingType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : comRingType >-> idCneuron1.mixin_of.
    Coercion como_mixin : comRingType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : comRingType >-> neuron1.class_of.
    Coercion mono_class : comRingType >-> mononeuron1.class_of.
    Coercion idC_class : comRingType >-> idCneuron1.class_of.
    Coercion como_class : comRingType >-> comoneuron1.class_of.
    Coercion comidC_class : comRingType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : comRingType >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion zmodCNNet_class : class_of >-> zmodCNNet.class_of.
    Coercion zmodINNet_class : class_of >-> zmodINNet.class_of.
    Coercion zmod3NNet_class : class_of >-> zmod3NNet.class_of.
    Coercion lmodNNet_class : class_of >-> lmodNNet.class_of.
    Coercion lalgNNet_class : class_of >-> lalgNNet.class_of.
    Coercion algNNet_class : class_of >-> algNNet.class_of.
    Coercion ringNNet_class : class_of >-> ringNNet.class_of.
    Coercion NNetR : comRingNNetType >-> comRingType.
    Coercion neuron1 : comRingNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : comRingNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : comRingNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : comRingNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : comRingNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : comRingNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : comRingNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : comRingNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : comRingNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : comRingNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : comRingNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : comRingNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : comRingNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : comRingNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : comRingNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : comRingNNetType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : comRingNNetType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion algNNet : comRingNNetType >-> algNNetType.
    Canonical algNNet.
    Coercion ringNNet : comRingNNetType >-> ringNNetType.
    Canonical ringNNet.
  End Exports.
End comRingNNet.
Export comRingNNet.Exports.

(* ***************************** *)
Module unitRingNNet.

  Record class_of (R:unitRingType) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class *%R (@addrA R)))
      }.

  Section class.
    Variable (R:unitRingType).
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
    Definition ringNNet_class := ringNNet.Class NNet_class.
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
    Definition ringNNet := ringNNet.Pack (ringNNet_class class).
  End Packing.

  Module Exports.
    Notation unitRingNNetType := type.
    Coercion mono_mixin : unitRingType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : unitRingType >-> idCneuron1.mixin_of.
    Coercion como_mixin : unitRingType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : unitRingType >-> neuron1.class_of.
    Coercion mono_class : unitRingType >-> mononeuron1.class_of.
    Coercion idC_class : unitRingType >-> idCneuron1.class_of.
    Coercion como_class : unitRingType >-> comoneuron1.class_of.
    Coercion comidC_class : unitRingType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : unitRingType >-> zmodneuron1.class_of.
    Coercion zmodNNet_class : class_of >-> zmodNNet.class_of.
    Coercion zmodCNNet_class : class_of >-> zmodCNNet.class_of.
    Coercion zmodINNet_class : class_of >-> zmodINNet.class_of.
    Coercion zmod3NNet_class : class_of >-> zmod3NNet.class_of.
    Coercion lmodNNet_class : class_of >-> lmodNNet.class_of.
    Coercion lalgNNet_class : class_of >-> lalgNNet.class_of.
    Coercion ringNNet_class : class_of >-> ringNNet.class_of.
    Coercion NNetR : unitRingNNetType >-> unitRingType.
    Coercion neuron1 : unitRingNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : unitRingNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : unitRingNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : unitRingNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : unitRingNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : unitRingNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : unitRingNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : unitRingNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : unitRingNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : unitRingNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : unitRingNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : unitRingNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : unitRingNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : unitRingNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : unitRingNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : unitRingNNetType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : unitRingNNetType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion ringNNet : unitRingNNetType >-> ringNNetType.
    Canonical ringNNet.
  End Exports.
End unitRingNNet.
Export unitRingNNet.Exports.

(* ***************************** *)
Module comUnitRingNNet.

  Record class_of (R:comUnitRingType) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class *%R (@addrA R)))
      }.

  Section class.
    Variable (R:comUnitRingType).
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
  End Packing.

  Module Exports.
    Notation comUnitRingNNetType := type.
    Coercion mono_mixin : comUnitRingType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : comUnitRingType >-> idCneuron1.mixin_of.
    Coercion como_mixin : comUnitRingType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : comUnitRingType >-> neuron1.class_of.
    Coercion mono_class : comUnitRingType >-> mononeuron1.class_of.
    Coercion idC_class : comUnitRingType >-> idCneuron1.class_of.
    Coercion como_class : comUnitRingType >-> comoneuron1.class_of.
    Coercion comidC_class : comUnitRingType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : comUnitRingType >-> zmodneuron1.class_of.
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
    Coercion NNetR : comUnitRingNNetType >-> comUnitRingType.
    Coercion neuron1 : comUnitRingNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : comUnitRingNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : comUnitRingNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : comUnitRingNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : comUnitRingNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : comUnitRingNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : comUnitRingNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : comUnitRingNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : comUnitRingNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : comUnitRingNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : comUnitRingNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : comUnitRingNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : comUnitRingNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : comUnitRingNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : comUnitRingNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : comUnitRingNNetType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : comUnitRingNNetType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion algNNet : comUnitRingNNetType >-> algNNetType.
    Canonical algNNet.
    Coercion ringNNet : comUnitRingNNetType >-> ringNNetType.
    Canonical ringNNet.
    Coercion comRingNNet : comUnitRingNNetType >-> comRingNNetType.
    Canonical comRingNNet.
    Coercion unitRingNNet : comUnitRingNNetType >-> unitRingNNetType.
    Canonical unitRingNNet.
  End Exports.
End comUnitRingNNet.
Export comUnitRingNNet.Exports.

(* ***************************** *)
Module idomainNNet.

  Record class_of (R:idomainType) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class *%R (@addrA R)))
      }.

  Section class.
    Variable (R:idomainType).
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
  End Packing.

  Module Exports.
    Notation idomainNNetType := type.
    Coercion mono_mixin : idomainType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : idomainType >-> idCneuron1.mixin_of.
    Coercion como_mixin : idomainType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : idomainType >-> neuron1.class_of.
    Coercion mono_class : idomainType >-> mononeuron1.class_of.
    Coercion idC_class : idomainType >-> idCneuron1.class_of.
    Coercion como_class : idomainType >-> comoneuron1.class_of.
    Coercion comidC_class : idomainType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : idomainType >-> zmodneuron1.class_of.
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
    Coercion NNetR : idomainNNetType >-> idomainType.
    Coercion neuron1 : idomainNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : idomainNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : idomainNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : idomainNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : idomainNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : idomainNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : idomainNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : idomainNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : idomainNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : idomainNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : idomainNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : idomainNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : idomainNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : idomainNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : idomainNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : idomainNNetType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : idomainNNetType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion algNNet : idomainNNetType >-> algNNetType.
    Canonical algNNet.
    Coercion ringNNet : idomainNNetType >-> ringNNetType.
    Canonical ringNNet.
    Coercion comRingNNet : idomainNNetType >-> comRingNNetType.
    Canonical comRingNNet.
    Coercion unitRingNNet : idomainNNetType >-> unitRingNNetType.
    Canonical unitRingNNet.
    Coercion comUnitRingNNet : idomainNNetType >-> comUnitRingNNetType.
    Canonical comUnitRingNNet.
  End Exports.
End idomainNNet.
Export idomainNNet.Exports.

(* ***************************** *)
Module fieldNNet.

  Record class_of (F:fieldType) :=
    Class {
        NNet_mixin : NNet.mixin_of
                       (neuron1.Pack (neuron1.Class *%R (@addrA F)))
      }.

  Section class.
    Variable (F:fieldType).
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
  End Packing.

  Module Exports.
    Notation fieldNNetType := type.
    Coercion mono_mixin : fieldType >-> mononeuron1.mixin_of.
    Coercion idC_mixin : fieldType >-> idCneuron1.mixin_of.
    Coercion como_mixin : fieldType >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : fieldType >-> neuron1.class_of.
    Coercion mono_class : fieldType >-> mononeuron1.class_of.
    Coercion idC_class : fieldType >-> idCneuron1.class_of.
    Coercion como_class : fieldType >-> comoneuron1.class_of.
    Coercion comidC_class : fieldType >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion comidCNNet_class : class_of >-> comidCNNet.class_of.
    Coercion zmod_class : fieldType >-> zmodneuron1.class_of.
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
    Coercion NNetF : fieldNNetType >-> fieldType.
    Coercion neuron1 : fieldNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : fieldNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : fieldNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : fieldNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : fieldNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : fieldNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : fieldNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : fieldNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : fieldNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : fieldNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion zmodneuron1 : fieldNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : fieldNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : fieldNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
    Coercion zmodINNet : fieldNNetType >-> zmodINNetType.
    Canonical zmodINNet.
    Coercion zmod3NNet : fieldNNetType >-> zmod3NNetType.
    Canonical zmod3NNet.
    Coercion lmodNNet : fieldNNetType >-> lmodNNetType.
    Canonical lmodNNet.
    Coercion lalgNNet : fieldNNetType >-> lalgNNetType.
    Canonical lalgNNet.
    Coercion algNNet : fieldNNetType >-> algNNetType.
    Canonical algNNet.
    Coercion ringNNet : fieldNNetType >-> ringNNetType.
    Canonical ringNNet.
    Coercion comRingNNet : fieldNNetType >-> comRingNNetType.
    Canonical comRingNNet.
    Coercion unitRingNNet : fieldNNetType >-> unitRingNNetType.
    Canonical unitRingNNet.
    Coercion comUnitRingNNet : fieldNNetType >-> comUnitRingNNetType.
    Canonical comUnitRingNNet.
    Coercion idomainNNet : fieldNNetType >-> idomainNNetType.
    Canonical idomainNNet.
  End Exports.
End fieldNNet.
Export fieldNNet.Exports.

(* ***************************** *)
Module eqzmodCNNet.

  Section Packing.
    Structure type := Pack {NNetI:eqType; NNetO; NNetC;
                            _:zmodCNNet.class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT return
                           zmodCNNet.class_of (NNetI cT) (NNetO cT) (NNetC cT)
      in c.
    Definition neuron1 := neuron1.Pack class.
    Definition mononeuron1 := mononeuron1.Pack class.
    Definition idCneuron1 := idCneuron1.Pack class.
    Definition comoneuron1 := comoneuron1.Pack class.
    Definition comidCneuron1 := comidCneuron1.Pack class.
    Definition NNet := NNet.Pack class.
    Definition monoNNet := monoNNet.Pack class.
    Definition idCNNet := idCNNet.Pack class.
    Definition comoNNet := comoNNet.Pack class.
    Definition comidCNNet := comidCNNet.Pack class.
    Definition eqneuron1 := eqneuron1.Pack class.
    Definition eqcomoNNet := eqcomoNNet.Pack class.
    Definition zmodneuron1 := zmodneuron1.Pack class.
    Definition zmodNNet := zmodNNet.Pack class.
    Definition zmodCNNet := zmodCNNet.Pack class.
  End Packing.

  Module Exports.
    Notation eqzmodCNNetType := type.
    Coercion NNetI : eqzmodCNNetType >-> eqType.
    Coercion NNetO : eqzmodCNNetType >-> zmodType.
    Coercion NNetC : eqzmodCNNetType >-> zmodType.
    Coercion neuron1 : eqzmodCNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : eqzmodCNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : eqzmodCNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comoneuron1 : eqzmodCNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion comidCneuron1 : eqzmodCNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : eqzmodCNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : eqzmodCNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion idCNNet : eqzmodCNNetType >-> idCNNetType.
    Canonical idCNNet.
    Coercion comoNNet : eqzmodCNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion comidCNNet : eqzmodCNNetType >-> comidCNNetType.
    Canonical comidCNNet.
    Coercion eqneuron1 : eqzmodCNNetType >-> eqneuron1Type.
    Canonical eqneuron1.
    Coercion eqcomoNNet : eqzmodCNNetType >-> eqcomoNNetType.
    Canonical eqcomoNNet.
    Coercion zmodneuron1 : eqzmodCNNetType >-> zmodneuron1Type.
    Canonical zmodneuron1.
    Coercion zmodNNet : eqzmodCNNetType >-> zmodNNetType.
    Canonical zmodNNet.
    Coercion zmodCNNet : eqzmodCNNetType >-> zmodCNNetType.
    Canonical zmodCNNet.
  End Exports.
End eqzmodCNNet.
Export eqzmodCNNet.Exports.

(* ***************************** *)
End NNet_algDef.
Export zmodneuron1.Exports zmodNNet.Exports zmodCNNet.Exports zmodINNet.Exports
       zmod3NNet.Exports lmodNNet.Exports lalgNNet.Exports algNNet.Exports
       ringNNet.Exports comRingNNet.Exports unitRingNNet.Exports
       comUnitRingNNet.Exports idomainNNet.Exports fieldNNet.Exports
       eqzmodCNNet.Exports.