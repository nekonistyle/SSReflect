From mathcomp
     Require Import ssreflect ssrnat ssrbool ssrfun eqtype seq div fintype
     tuple finfun bigop.
Add LoadPath "../mylib".
Require Export mylib.
Require Export NNet_sub_def.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Import NNetDef.
(* ***************************** *)
Module neuron1.

   Record class_of (I O C:Type) :=
    Class {
        action : C -> I -> O;
        op : O -> O -> O;
        _ : associative op
      }.

  Section Packing.

    Structure type :=
      Pack {NNetI; NNetO; NNetC; _: class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT return
                           class_of (NNetI cT) (NNetO cT) (NNetC cT) in c.

  End Packing.

  Module Exports.

    Notation neuron1Type := type.
    Definition NNetI := NNetI.
    Definition NNetO := NNetO.
    Definition NNetC := NNetC.
    Definition NNaction S := action (class S).
    Definition NNop S := op (class S).

  End Exports.
End neuron1.
Import neuron1.Exports.

Section neuron1_lemma.

  Variable (S:neuron1Type).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.

  Lemma NNopA : associative op.
  Proof. rewrite /op. by case : S => NNetI NNetO NNetC []. Qed.

  Definition neuron1 Idim (coeff:C ^ Idim) b : I ^ Idim -> O :=
    fun input => \big[op/b]_(i < Idim) action (coeff i) (input i).

  Definition MP1parameter Idim Odim : Type :=
    ((C ^ Idim) ^ Odim : Type) * O ^ Odim.

  Definition coeff_zero c0 Idim Odim : (C ^ Idim) ^ Odim : Type :=
    [ffun => [ffun => c0]].

  Definition bias_zero o0 Odim : O ^ Odim := [ffun => o0].

  Definition MP1parameter_zero o0 c0 Idim Odim : MP1parameter Idim Odim :=
    (coeff_zero c0 Idim Odim,bias_zero o0 Odim).

  Definition MP1 Idim Odim (p:MP1parameter Idim Odim) :
    I ^ Idim -> O ^ Odim :=
    fun input => [ffun j => neuron1 (p.1 j) (p.2 j) input].

(* ***************************** *)

  Lemma neuron1_Idim0 (coeff:C ^ 0) b input :
    neuron1 coeff b input = b.
  Proof. by rewrite /neuron1 big_ord0. Qed.

  Lemma MP1_Idim0 Odim (p:MP1parameter 0 Odim) input:
    MP1 p input = p.2.
  Proof. apply /ffunP => i. rewrite ffunE. exact : neuron1_Idim0. Qed.

  Lemma neuron1_op_bias Idim (coeff:C ^ Idim) b b' input:
    neuron1 coeff (op b b') input = op (neuron1 coeff b input) b'.
  Proof. by rewrite /neuron1 big_idx_assoc; last exact NNopA. Qed.

  Lemma MP1_op_bias Idim Odim (coeff:(C ^ Idim) ^ Odim: Type)
        (bias bias':O ^ Odim) input:
    MP1 (coeff,[ffun j => op (bias j) (bias' j)]) input
    = [ffun j => op (MP1 (coeff,bias) input j) (bias' j)].
  Proof. apply /ffunP => j. by rewrite !ffunE -/neuron1 neuron1_op_bias. Qed.

  Lemma neuron1_appI Idim Idim' (coeff:C ^ (Idim + Idim')) b input:
    neuron1 coeff b input =
    neuron1 (index_projl coeff)
            (neuron1 (index_projr coeff) b (index_projr input))
            (index_projl input).
  Proof.
    rewrite /neuron1 big_split_ord_nested.
    rewrite (eq_bigr (fun i => action (index_projl coeff i)
                                      (index_projl input i)))=>[|i _];
      last by rewrite !ffunE.
    congr bigop. apply : eq_bigr => i _. by rewrite !ffunE.
  Qed.

  Lemma MP1_appI Idim Idim' Odim (p:MP1parameter (Idim + Idim') Odim) input:
    MP1 p input =
    MP1 ([ffun i => index_projl (p.1 i)],
         MP1 ([ffun i => index_projr (p.1 i)],p.2) (index_projr input))
        (index_projl input).
  Proof. apply /ffunP => j. rewrite !ffunE. exact : neuron1_appI. Qed.

  Lemma MP1_sumO Idim Odim Odim'
        (coeff:(C ^ Idim) ^ Odim: Type) (coeff':(C ^ Idim) ^ Odim' : Type) bias bias' input:
    MP1 ((index_app coeff coeff'),(index_app bias bias')) input =
    index_app (MP1 (coeff,bias) input) (MP1 (coeff',bias') input).
  Proof.
    apply /ffunP => j. rewrite !ffunE /=.
    case splitP =>/= j' Heq /=; by rewrite !ffunE.
  Qed.

  Lemma MP1_appO Idim Odim Odim' (p:MP1parameter Idim (Odim + Odim')) input:
    MP1 p input =
    index_app (MP1 (index_projl p.1, index_projl p.2) input)
              (MP1 (index_projr p.1, index_projr p.2) input).
  Proof. by rewrite -MP1_sumO !index_app_proj. Qed.

  Lemma index_projl_MP1 Idim Odim Odim'
        (p:MP1parameter Idim (Odim + Odim')) input:
    index_projl (MP1 p input) = MP1 (index_projl p.1, index_projl p.2) input.
  Proof. by rewrite MP1_appO index_projl_app. Qed.

  Lemma index_projr_MP1 Idim Odim Odim'
        (p:MP1parameter Idim (Odim + Odim')) input:
    index_projr (MP1 p input) = MP1 (index_projr p.1, index_projr p.2) input.
  Proof. by rewrite MP1_appO index_projr_app. Qed.

  
(* ***************************** *)

  Definition cast_MP1parameter Idim1 Odim1 Idim2 Odim2
             (eqIdim : Idim1 = Idim2) (eqOdim : Odim1 = Odim2)
             (p:MP1parameter Idim1 Odim1) : MP1parameter Idim2 Odim2 :=
    ecast Idim2 _ eqIdim (ecast Odim2 _ eqOdim p).

  Lemma cast_MP1parameter_id Idim Odim eqIdim eqOdim (p:MP1parameter Idim Odim):
    cast_MP1parameter eqIdim eqOdim p = p.
  Proof. by rewrite !eq_axiomK. Qed.

  Lemma cast_MP1parameterK Idim1 Odim1 Idim2 Odim2
        (eqIdim:Idim1 = Idim2) (eqOdim:Odim1 = Odim2):
    cancel (cast_MP1parameter eqIdim eqOdim)
           (cast_MP1parameter (esym eqIdim) (esym eqOdim)).
  Proof. by case : Idim2 / eqIdim; case : Odim2 / eqOdim. Qed.

  Lemma cast_MP1parameterKV Idim1 Odim1 Idim2 Odim2
        (eqIdim:Idim1 = Idim2) (eqOdim:Odim1 = Odim2):
    cancel (cast_MP1parameter (esym eqIdim) (esym eqOdim))
           (cast_MP1parameter eqIdim eqOdim).
  Proof. by case : Idim2 / eqIdim; case : Odim2 / eqOdim. Qed.

  Lemma cast_MP1parameter_trans Idim1 Odim1 Idim2 Odim2 Idim3 Odim3
        eqIdim12 eqIdim23 eqOdim12 eqOdim23 (p:MP1parameter Idim1 Odim1):
    @cast_MP1parameter _ _ Idim3 Odim3 eqIdim23 eqOdim23
                       (@cast_MP1parameter _ _ Idim2 Odim2 eqIdim12 eqOdim12 p)
    = cast_MP1parameter (etrans eqIdim12 eqIdim23) (etrans eqOdim12 eqOdim23) p.
  Proof. by case : Idim3 / eqIdim23; case : Odim3 / eqOdim23. Qed.

  Lemma cast_MP1parameter_inj Idim1 Odim1 Idim2 Odim2
        (eqIdim:Idim1 = Idim2) (eqOdim:Odim1 = Odim2):
    injective (cast_MP1parameter eqIdim eqOdim).
  Proof. exact : can_inj (cast_MP1parameterK _ _). Qed.

  Lemma cast_MP1parameterE Idim1 Odim1 Idim2 Odim2
        (eqIdim : Idim1 = Idim2) (eqOdim : Odim1 = Odim2)
        (p:MP1parameter Idim1 Odim1):
    cast_MP1parameter eqIdim eqOdim p =
    (cast_index eqOdim [ffun i => cast_index eqIdim (p.1 i)],
     cast_index eqOdim p.2).
  Proof.
    case : Idim2 / eqIdim. case : Odim2 /eqOdim.
    rewrite cast_MP1parameter_id !cast_index_id. case : p => p1 p2.
    congr(_,_). apply /ffunP => i. by rewrite ffunE cast_index_id.
  Qed.

  Lemma MP1_cast Idim1 Odim1 Idim2 Odim2
        (eqIdim:Idim1 = Idim2) (eqOdim:Odim1 = Odim2)
        (p:MP1parameter Idim1 Odim1) input:
    MP1 (cast_MP1parameter eqIdim eqOdim p) (cast_index eqIdim input) =
    cast_index eqOdim (MP1 p input).
  Proof.
    apply /ffunP => i. rewrite cast_MP1parameterE ffunE !cast_indexE !ffunE /=.
    rewrite /neuron1 (big_cast_ord _ _ eqIdim).
    apply : eq_bigr => j _. by rewrite !cast_indexE cast_ordK.
  Qed.

End neuron1_lemma.

(* ***************************** *)
Module mononeuron1.

  Record mixin_of (S:neuron1Type) :=
    Mixin {
        id: NNetO S;
        _: left_id id (@NNop S);
        _: right_id id (@NNop S)
      }.

  Section Packing.

    Structure class_of (I O C:Type) :=
      Class {
          neuron1_class : neuron1.class_of I O C;
          mixin : mixin_of (neuron1.Pack neuron1_class)
        }.
    Structure type := Pack {NNetI; NNetO; NNetC; _: class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT
                           return class_of (NNetI cT) (NNetO cT) (NNetC cT)
      in c.

    Definition neuron1 := neuron1.Pack (neuron1_class class).

  End Packing.

  Module Exports.

    Notation mononeuron1Type := type.
    Coercion neuron1_class : class_of >-> neuron1.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion neuron1 : mononeuron1Type >-> neuron1Type.
    Canonical neuron1.
    Definition NNid S := id (mixin (class S)).

  End Exports.
End mononeuron1.
Import mononeuron1.Exports.

(* ***************************** *)
Section mononeuron1_lemma.

  Variable (S:mononeuron1Type).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let id := @NNid S.

  Lemma NNop0o : left_id id op.
  Proof. rewrite /op /id. by case : S => NNetI NNetO NNetC [class []]. Qed.

  Lemma NNopo0 : right_id id op.
  Proof. rewrite /op /id. by case : S => NNetI NNetO NNetC [class []]. Qed.

  Canonical NNop_monoid := Monoid.Law (@NNopA S) NNop0o NNopo0.

  Definition bias0 := bias_zero id.

  Lemma neuron1_bias Idim (coeff:C ^ Idim) b input:
    neuron1 coeff b input = op (neuron1 coeff id input) b.
  Proof. by rewrite /op -neuron1_op_bias -/op NNop0o. Qed.

  Lemma MP1_bias Idim Odim (coeff:(C ^ Idim) ^ Odim: Type) bias input:
    MP1 (coeff,bias) input =
    [ffun j => op (MP1 (coeff,bias0 _) input j) (bias j)].
  Proof. apply /ffunP => j. by rewrite !ffunE -/neuron1 neuron1_bias. Qed.

End mononeuron1_lemma.

(* ***************************** *)
Module idCneuron1.

  Record mixin_of (V:mononeuron1Type) :=
    Mixin {
        idC: NNetC V;
        _: forall x, NNaction idC x = @NNid V
      }.

  Section Packing.

    Structure class_of (I O C:Type) :=
      Class {
          mono_class:mononeuron1.class_of I O C;
          mixin:mixin_of (mononeuron1.Pack mono_class)
        }.
    Structure type := Pack {NNetI; NNetO; NNetC; _: class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT
                           return class_of (NNetI cT) (NNetO cT) (NNetC cT)
      in c.
    Definition neuron1 := neuron1.Pack (mono_class class).
    Definition mononeuron1 := mononeuron1.Pack (mono_class class).

  End Packing.

  Module Exports.

    Notation idCneuron1Type := type.
    Coercion mono_class : class_of >-> mononeuron1.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion neuron1 : idCneuron1Type >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : idCneuron1Type >-> mononeuron1Type.
    Canonical mononeuron1.
    Definition NNidC S := idC (class S).

  End Exports.
End idCneuron1.
Export idCneuron1.Exports.

Section idCneuron1_lemma.

  Variable (S:idCneuron1Type).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let id := @NNid S.
  Let idC := @NNidC S.
  Let parameter := @MP1parameter S.

  Definition coeff0 := coeff_zero idC.
  Definition MP1parameter0 := MP1parameter_zero id idC.

  Lemma action_idl x: action idC x = id.
  Proof.
    rewrite /action /idC /id. by case : S x => NNetI NNetO NNetC [class []].
  Qed.

  Lemma neuron1_idC Idim (input:I ^ Idim) b:
    neuron1 [ffun _ => idC] b input = b.
  Proof.
    rewrite neuron1_bias /neuron1 big1; first exact : NNop0o.
    move => i _. rewrite ffunE. exact : action_idl.
  Qed.

  Lemma MP1_coeff0 Idim Odim (bias:O ^ Odim) (input:I ^ Idim):
    MP1 (coeff0 _ _,bias) input = bias.
  Proof. by apply /ffunP => j; rewrite !ffunE neuron1_idC. Qed.

  Definition coeff_app Idim Odim Idim' Odim'
             (coeff:(C ^ Idim) ^ Odim: Type) (coeff':(C ^ Idim') ^ Odim': Type)
    :=
    index_app
      [ffun j:'I_Odim => (index_app (coeff j) [ffun _ :'I_Idim' => idC])]
      [ffun j:'I_Odim' => (index_app [ffun _ :'I_Idim => idC] (coeff' j))].

  Definition MP1parameter_sum Idim1 Odim1 Idim2 Odim2
             (p1:parameter Idim1 Odim1) (p2:parameter Idim2 Odim2) :
    parameter (Idim1 + Idim2) (Odim1 + Odim2) :=
    (coeff_app p1.1 p2.1,index_app p1.2 p2.2).

  Lemma MP1parameter_sumA Idim1 Odim1 Idim2 Odim2 Idim3 Odim3
        (p1:parameter Idim1 Odim1) (p2:parameter Idim2 Odim2)
        (p3:parameter Idim3 Odim3):
    MP1parameter_sum p1 (MP1parameter_sum p2 p3) =
    cast_MP1parameter (esym (addnA _ _ _)) (esym (addnA _ _ _))
                      (MP1parameter_sum (MP1parameter_sum p1 p2) p3).
  Proof.
    rewrite /MP1parameter_sum cast_MP1parameterE /=.
    congr(_,_); last exact : index_appA. apply /ffunP => i.
    rewrite cast_indexE esymK !ffunE !cast_ord_addnA /=.
    case : splitP => j _/=; last (rewrite !ffunE /=; case : splitP => k _/=);
      rewrite ?split_lshift ?split_rshift /= !ffunE /=
              ?split_lshift ?split_rshift /= ?ffunE -?index_appA =>//.
    - congr index_app. apply /ffunP => k /=. rewrite !ffunE /=.
      by case : splitP => ? _/=; rewrite ffunE.
    - rewrite index_appA. congr cast_index. congr index_app. apply /ffunP => t.
      rewrite !ffunE /=. by case : split => ? /=; rewrite ffunE.
  Qed.

  Lemma MP1parameter_sum0 Idim1 Idim2 Odim1 Odim2:
    MP1parameter_sum (MP1parameter0 Idim1 Odim1) (MP1parameter0 Idim2 Odim2) =
    (MP1parameter0 _ _).
  Proof.
    rewrite /MP1parameter_sum /MP1parameter0.
    by congr(_,_); apply /ffunP => i;
      rewrite !ffunE /=; case : splitP => i' _/=; rewrite !ffunE //;
      apply /ffunP => j; rewrite !ffunE /=; case : splitP => j' /=;
      rewrite !ffunE.
  Qed.    

End idCneuron1_lemma.

(* ***************************** *)
Module comoneuron1.

  Record mixin_of (S:mononeuron1Type) :=
    Mixin { _: commutative (@NNop S)}.

  Section Packing.

    Record class_of (I O C:Type) :=
      Class {
          mono_class : mononeuron1.class_of I O C;
          mixin : mixin_of (mononeuron1.Pack mono_class)
        }.

    Structure type := Pack {NNetI; NNetO; NNetC; _:class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT
                           return class_of (NNetI cT) (NNetO cT) (NNetC cT)
      in c.
    Definition neuron1 := neuron1.Pack (mono_class class).
    Definition mononeuron1 := mononeuron1.Pack (mono_class class).

  End Packing.

  Module Exports.

    Notation comoneuron1Type := type.
    Coercion mono_class : class_of >-> mononeuron1.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion neuron1 : comoneuron1Type >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : comoneuron1Type >-> mononeuron1Type.
    Canonical mononeuron1.

  End Exports.
End comoneuron1.
Export comoneuron1.Exports.

Section comoneuron1_lemma.

  Variable (S:comoneuron1Type).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let id := @NNid S.

  Lemma NNopC : commutative op.
  Proof. rewrite /op. by case : S => NNetI NNetO NNetC [class []]. Qed.

  Canonical NNop_comoid := Monoid.ComLaw NNopC.

  Lemma NNopCA : left_commutative op. Proof. exact : Monoid.mulmCA. Qed.
  Lemma NNopAC : right_commutative op. Proof. exact : Monoid.mulmAC. Qed.
  Lemma NNopACA : interchange op op. Proof. exact : Monoid.mulmACA. Qed.

  Lemma neuron1_sumI Idim Idim'
        (coeff:C ^ Idim) (coeff':C ^ Idim') b b' input:
    neuron1 (index_app coeff coeff') (op b b') input
    = op (neuron1 coeff b (index_projl input))
         (neuron1 coeff' b' (index_projr input)).
  Proof.
    rewrite neuron1_bias [_ _ b _]neuron1_bias [_ _ b' _]neuron1_bias.
    rewrite NNopACA /neuron1. congr(op _ _). rewrite big_split_ord.
    congr (op _ _); apply: eq_bigr => i _.
    - congr(action _ _); first exact : index_app_lshift. by rewrite ffunE.
    - congr(action _ _); first exact : index_app_rshift. by rewrite ffunE.
  Qed.

  Lemma MP1_sumI Idim Idim' Odim
      (coeff:(C ^ Idim) ^ Odim: Type) (coeff':(C ^ Idim') ^ Odim: Type)
      (bias bias':O ^ Odim) input:
    MP1 ([ffun j => index_app (coeff j) (coeff' j)],
         [ffun j => op (bias j) (bias' j)]) input
    = [ffun j => op (MP1 (coeff,bias) (index_projl input) j)
                    (MP1 (coeff',bias') (index_projr input) j)].
  Proof. apply /ffunP => j. by rewrite !ffunE neuron1_sumI. Qed.

  Lemma neuron1_appl Idim Idim'
        (coeff:C ^ Idim) (coeff':C ^ Idim') b input:
    neuron1 (index_app coeff coeff') b input
    = op (neuron1 coeff b (index_projl input))
         (neuron1 coeff' id (index_projr input)).
  Proof. by rewrite -neuron1_sumI /id /op NNopo0. Qed.

  Lemma neuron1_appr Idim Idim'
        (coeff:C ^ Idim) (coeff':C ^ Idim') b input:
    neuron1 (index_app coeff coeff') b input
    = op (neuron1 coeff id (index_projl input))
         (neuron1 coeff' b (index_projr input)).
  Proof. by rewrite -neuron1_sumI /id /op NNop0o. Qed.

  Lemma MP1_appl Idim Idim' Odim
      (coeff:(C ^ Idim) ^ Odim: Type) (coeff':(C ^ Idim') ^ Odim: Type)
      (bias :O ^ Odim) input:
    MP1 ([ffun j => index_app (coeff j) (coeff' j)],bias) input
    = [ffun j => op (MP1 (coeff,bias) (index_projl input) j)
                    (MP1 (coeff',bias0 _ _) (index_projr input) j)].
  Proof. apply /ffunP => j. by rewrite !ffunE neuron1_appl. Qed.

  Lemma MP1_appr Idim Idim' Odim
      (coeff:(C ^ Idim) ^ Odim: Type) (coeff':(C ^ Idim') ^ Odim: Type)
      (bias :O ^ Odim) input:
    MP1 ([ffun j => index_app (coeff j) (coeff' j)],bias) input
    = [ffun j => op (MP1 (coeff,bias0 _ _) (index_projl input) j)
                    (MP1 (coeff',bias) (index_projr input) j)].
  Proof. apply /ffunP => j. by rewrite !ffunE neuron1_appr. Qed.

  Lemma neuron1_linear Idim coeff b (input1 input2:I ^ Idim) k:
    let input1' := [ffun i => if i == k then input2 i else input1 i] in
    let input2' := [ffun i => if i == k then input1 i else input2 i] in
    op (neuron1 coeff b input1) (neuron1 coeff b input2) =
    op (neuron1 coeff b input1') (neuron1 coeff b input2').
  Proof.
    rewrite /= ![_ _ b _]neuron1_bias /op !NNopA -/op. congr op.
    rewrite ![op (_ _ b) _]NNopAC. congr op.
    rewrite /neuron1 !(bigD1 k is_true_true).
    rewrite ![op _ (_ (_ (coeff k) _)_)]NNopACA !ffunE eq_refl.
    congr op; first exact : NNopC.
    by congr op; apply : eq_bigr => i /negbTE; rewrite ffunE =>->.
  Qed.

  Lemma MP1_linear Idim Odim (p:MP1parameter S Idim Odim)
        (input1 input2:I ^ Idim) k:
    let input1' := [ffun i => if i == k then input2 i else input1 i] in
    let input2' := [ffun i => if i == k then input1 i else input2 i] in
    [ffun j => op (MP1 p input1 j) (MP1 p input2 j)]
    = [ffun j => op (MP1 p input1' j) (MP1 p input2' j)].
  Proof. apply /ffunP => j. rewrite !ffunE. exact : neuron1_linear. Qed.

End comoneuron1_lemma.

Module comidCneuron1.

  Record class_of (I O C:Type) :=
    Class {
        mono_class : mononeuron1.class_of I O C;
        como_mixin : comoneuron1.mixin_of (mononeuron1.Pack mono_class);
        idC_mixin : idCneuron1.mixin_of (mononeuron1.Pack mono_class)
      }.

  Definition como_class I O C m := comoneuron1.Class (@como_mixin I O C m).
  Definition idC_class I O C m := idCneuron1.Class (@idC_mixin I O C m).

  Section Packing.

    Record type := Pack {NNetI; NNetO; NNetC; _:class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT
                           return class_of (NNetI cT) (NNetO cT) (NNetC cT)
      in c.
    Definition neuron1 := neuron1.Pack (mono_class class).
    Definition mononeuron1 := mononeuron1.Pack (mono_class class).
    Definition comoneuron1 := comoneuron1.Pack (como_class class).
    Definition idCneuron1 := idCneuron1.Pack (idC_class class).

  End Packing.

  Module Exports.

    Notation comidCneuron1Type := type.
    Coercion mono_class : class_of >-> mononeuron1.class_of.
    Coercion como_mixin : class_of >-> comoneuron1.mixin_of.
    Coercion idC_mixin : class_of >-> idCneuron1.mixin_of.
    Coercion como_class : class_of >-> comoneuron1.class_of.
    Coercion idC_class : class_of >-> idCneuron1.class_of.
    Coercion neuron1 : comidCneuron1Type >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : comidCneuron1Type >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion comoneuron1 : comidCneuron1Type >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion idCneuron1 : comidCneuron1Type >-> idCneuron1Type.
    Canonical idCneuron1.

  End Exports.
End comidCneuron1.
Export comidCneuron1.Exports.

Section comidCneuron1_lemma.

  Variable (S:comidCneuron1Type).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let id := @NNid S.
  Let idC := @NNidC S.
  Let parameter := @MP1parameter S.

  Lemma MP1_sum Idim1 Odim1 Idim2 Odim2
        (p1:parameter Idim1 Odim1) (p2:parameter Idim2 Odim2) input:
    MP1 (MP1parameter_sum p1 p2) input =
    index_app (MP1 p1 (index_projl input)) (MP1 p2 (index_projr input)).
  Proof.
    apply /ffunP => i. rewrite !ffunE /=.
    case : splitP => j Heq /=; rewrite !ffunE /=.
    - by rewrite -[p1.2 j]NNopo0 neuron1_sumI neuron1_idC !NNopo0.
    - by rewrite -[p2.2 j]NNop0o neuron1_sumI neuron1_idC !NNop0o.
  Qed.

End comidCneuron1_lemma.

(* ***************************** *)
Module NNet.

  Record mixin_of (S:neuron1Type) :=
    Mixin {activation : NNetO S -> NNetI S}.

  Section Packing.

    Structure class_of (I O C:Type) :=
      Class {
          neuron1_class: neuron1.class_of I O C;
          mixin: mixin_of (neuron1.Pack neuron1_class)
        }.

    Structure type := Pack {NNetI; NNetO; NNetC; _:class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT
                           return class_of (NNetI cT) (NNetO cT) (NNetC cT)
      in c.
    Definition neuron1 := neuron1.Pack (neuron1_class class).

  End Packing.

  Module Exports.

    Notation NNetType := type.
    Coercion neuron1_class : class_of >-> neuron1.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion neuron1 : NNetType >-> neuron1Type.
    Canonical neuron1.
    Definition NNactivation (S:NNetType) := activation (class S).
    Definition NNactf (S:NNetType) dim (f:NNetO S ^ dim)
      := finfun ((@NNactivation S) \o f).

  End Exports.
End NNet.
Export NNet.Exports.

Section NNet_lemma.

  Variable (S:NNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let actf := @NNactf S.
  Let parameter := MP1parameter S.

  Lemma actf_app dim dim' (f:O ^ dim) (f':O ^ dim'):
    NNactf (index_app f f') = index_app (NNactf f) (NNactf f').
  Proof. by rewrite /NNactf index_app_additive. Qed.

  Fixpoint MPparameter Idim l Odim : Type :=
    match l with
    | [::] => parameter Idim Odim
    | Hdim :: l' => parameter Idim Hdim * MPparameter Hdim l' Odim
    end.

  Fixpoint MPparameter_zero o0 c0 {Idim l Odim} : MPparameter Idim l Odim :=
    match l return MPparameter Idim l Odim with
    | [::] => MP1parameter_zero o0 c0 _ _
    | _ :: _ => (MP1parameter_zero o0 c0 _ _, MPparameter_zero o0 c0)
    end.

  Fixpoint MPfunction Idim l Odim :
    MPparameter Idim l Odim -> I ^ Idim -> O ^ Odim :=
    match l return MPparameter Idim l Odim -> I ^ Idim -> O ^ Odim with
    | [::] => fun p => MP1 p
    | Hdim :: l' => fun p => MPfunction p.2 \o @actf _ \o MP1 p.1
    end.

  Definition cast_MPparameter Idim1 l1 Odim1 Idim2 l2 Odim2
             (eqIdim:Idim1 = Idim2) (eql:l1 = l2) (eqOdim:Odim1 = Odim2)
             (p:MPparameter Idim1 l1 Odim1) : MPparameter Idim2 l2 Odim2 :=
    ecast Odim2 _ eqOdim (ecast l2 _ eql (ecast Idim2 _ eqIdim p)).

  Lemma cast_MPparameter_id Idim l Odim eqIdim eql eqOdim
        (p:MPparameter Idim l Odim):
    cast_MPparameter eqIdim eql eqOdim p = p.
  Proof. by rewrite !eq_axiomK. Qed.

  Lemma cast_MPparameterK Idim1 l1 Odim1 Idim2 l2 Odim2
        (eqIdim:Idim1 = Idim2) (eql:l1 = l2) (eqOdim:Odim1 = Odim2):
    cancel (cast_MPparameter eqIdim eql eqOdim)
           (cast_MPparameter (esym eqIdim) (esym eql) (esym eqOdim)).
  Proof. by case : Idim2 / eqIdim; case : l2 / eql; case : Odim2 / eqOdim. Qed.

  Lemma cast_MPparameterKV Idim1 l1 Odim1 Idim2 l2 Odim2
        (eqIdim:Idim1 = Idim2) (eql:l1 = l2) (eqOdim:Odim1 = Odim2):
    cancel (cast_MPparameter (esym eqIdim) (esym eql) (esym eqOdim))
           (cast_MPparameter eqIdim eql eqOdim).
  Proof. by case : Idim2 / eqIdim; case : l2 / eql; case : Odim2 / eqOdim. Qed.

  Lemma cast_MPparameter_trans Idim1 l1 Odim1 Idim2 l2 Odim2 Idim3 l3 Odim3
        eqIdim12 eqIdim23 eql12 eql23 eqOdim12 eqOdim23
        (p:MPparameter Idim1 l1 Odim1):
    @cast_MPparameter _ _ _ Idim3 l3 Odim3 eqIdim23 eql23 eqOdim23
                      (@cast_MPparameter _ _ _ Idim2 l2 Odim2
                                         eqIdim12 eql12 eqOdim12 p)
    = cast_MPparameter (etrans eqIdim12 eqIdim23) (etrans eql12 eql23)
                       (etrans eqOdim12 eqOdim23) p.
  Proof.
      by case : Idim3 / eqIdim23; case : l3 / eql23;case : Odim3 / eqOdim23.
  Qed.

  Lemma cast_MPparameter_inj Idim1 l1 Odim1 Idim2 l2 Odim2
        (eqIdim:Idim1 = Idim2) (eql:l1 = l2) (eqOdim:Odim1 = Odim2):
    injective (cast_MPparameter eqIdim eql eqOdim).
  Proof. exact : can_inj (cast_MPparameterK _ _ _). Qed.

  Fixpoint cast_MPparameter_ind Idim1 l1 Odim1 Idim2 l2 Odim2:
    MPparameter Idim1 l1 Odim1 -> MPparameter Idim2 l2 Odim2 -> Prop :=
    match l1,l2 return MPparameter Idim1 l1 Odim1 ->
                       MPparameter Idim2 l2 Odim2 -> Prop with
    | [::],[::] => fun p1 p2 => exists eqIdim eqOdim,
                       cast_MP1parameter eqIdim eqOdim p1 = p2
    | _ :: _,_ :: _ => fun p1 p2 => exists eqIdim eqHdim,
                           cast_MP1parameter eqIdim eqHdim p1.1 = p2.1 /\
                           cast_MPparameter_ind p1.2 p2.2
    | _,_ => fun _ _ => False
    end.

  Lemma cast_MPparameterP Idim1 l1 Odim1 Idim2 l2 Odim2 eqIdim eql eqOdim
        (p1:MPparameter Idim1 l1 Odim1) (p2:MPparameter Idim2 l2 Odim2):
    cast_MPparameter eqIdim eql eqOdim p1 = p2 <-> cast_MPparameter_ind p1 p2.
  Proof.
    split.
    - case : Idim2 / eqIdim p2; case : l2 / eql; case : Odim2 / eqOdim => p2.
      rewrite cast_MPparameter_id =><-{p2}.
      elim : l1 =>[|Hdim1 l1 IHl1] in Idim1 p1 *;
                    by exists (erefl _), (erefl _).
    - case : Idim2 / eqIdim p2; case : l2 / eql; case : Odim2 / eqOdim => p2.
      rewrite cast_MPparameter_id.
      elim : l1 =>[|Hdim1 l1 IHl] in Idim1 p1 p2 *.
      + move =>[eqIdim] [eqOdim] <-. by rewrite cast_MP1parameter_id.
      + move : p1 p2 => [p11 p12] [p21 p22] [eqIdim] [eqHdim] []/=<- /IHl <-.
          by rewrite cast_MP1parameter_id.
  Qed.

  Lemma MPfunction_cast Idim1 l1 Odim1 Idim2 l2 Odim2
        (eqIdim:Idim1 = Idim2) (eql:l1 = l2) (eqOdim:Odim1 = Odim2) p input:
    MPfunction (cast_MPparameter eqIdim eql eqOdim p)
               (cast_index eqIdim input) =
    cast_index eqOdim (MPfunction p input).
  Proof.
    case : Idim2 / eqIdim p; case : l2 / eql; case : Odim2 / eqOdim => p.
    by rewrite cast_MPparameter_id !cast_index_id.
  Qed.

  Fixpoint MPparameter_app Idim l1 Hdim l2 Odim :
    MPparameter Idim l1 Hdim -> MPparameter Hdim l2 Odim ->
    MPparameter Idim (l1 ++ Hdim :: l2) Odim :=
    match l1 return MPparameter Idim l1 Hdim ->
                    MPparameter Hdim l2 Odim ->
                    MPparameter Idim (l1 ++ Hdim :: l2) Odim with
    | [::] => fun p1 p2 => (p1, p2)
    | dim :: l1' => fun p1 p2 => (p1.1, (MPparameter_app p1.2 p2))
    end.

  Lemma MPparameter_appA Idim l1 Hdim1 l2 Hdim2 l3 Odim
        (p1:MPparameter Idim l1 Hdim1)
        (p2:MPparameter Hdim1 l2 Hdim2)
        (p3:MPparameter Hdim2 l3 Odim) :
    MPparameter_app p1 (MPparameter_app p2 p3) =
    cast_MPparameter (erefl _) (esym (catA _ _ _)) (erefl _)
                     (MPparameter_app (MPparameter_app p1 p2) p3).
  Proof.
    symmetry. apply /cast_MPparameterP.
    elim : l1 =>[|dim l1' IHl1]/= in Idim p1 *; exists (erefl _), (erefl _);
    split=>//. exact /cast_MPparameterP.
  Qed.

  Lemma MPfunction_app Idim l1 Hdim l2 Odim
        (p1:MPparameter Idim l1 Hdim) (p2:MPparameter Hdim l2 Odim) :
    MPfunction (MPparameter_app p1 p2)
    =1 MPfunction p2 \o @actf _ \o MPfunction p1.
  Proof.
    elim : l1 =>[|dim l1' IHl1] in Idim p1 *=> input //=. by rewrite IHl1.
  Qed.

  Fixpoint MPparameter_rcons Idim l Hdim Odim :
    MPparameter Idim l Hdim -> parameter Hdim Odim ->
    MPparameter Idim (rcons l Hdim) Odim :=
    match l return MPparameter Idim l Hdim ->
                   parameter Hdim Odim ->
                   MPparameter Idim (rcons l Hdim) Odim with
    | [::] => fun p1 p2 => (p1,p2)
    | x :: l' => fun p1 p2 => (p1.1,MPparameter_rcons p1.2 p2)
    end.

  Fixpoint MPparameter_last Idim l Hdim Odim :
    MPparameter Idim (rcons l Hdim) Odim -> parameter Hdim Odim :=
    match l return MPparameter Idim (rcons l Hdim) Odim ->
                   parameter Hdim Odim with
    | [::] => fun p => p.2
    | a :: l' => fun p => MPparameter_last p.2
    end.

  Fixpoint MPparameter_belast Idim l Hdim Odim :
    MPparameter Idim (rcons l Hdim) Odim -> MPparameter Idim l Hdim :=
    match l return MPparameter Idim (rcons l Hdim) Odim ->
                   MPparameter Idim l Hdim with
    | [::] => fun p => p.1
    | a :: l' => fun p => (p.1,MPparameter_belast p.2)
    end.

  Lemma MPparameter_last_rcons Idim l Hdim Odim
        (p1:MPparameter Idim l Hdim) (p2:parameter Hdim Odim):
    MPparameter_last (MPparameter_rcons p1 p2) = p2.
  Proof. by elim : l =>[|a l IHl] in Idim p1 p2 *=>//=. Qed.

  Lemma MPparameter_belast_rcons Idim l Hdim Odim
        (p1:MPparameter Idim l Hdim) (p2:parameter Hdim Odim):
    MPparameter_belast (MPparameter_rcons p1 p2) = p1.
  Proof.
    elim : l =>[|a l IHl] in Idim p1 p2 *=>//=. rewrite IHl. by case : p1.
  Qed.

  Lemma MPfunction_rcons Idim l Hdim Odim
        (p:MPparameter Idim (rcons l Hdim) Odim) :
    MPfunction p
    =1 MP1 (MPparameter_last p) \o @actf _ \o
       MPfunction (MPparameter_belast p).
  Proof.
    elim : l =>[|l dim IHl] in Idim p *=> input //=. by rewrite IHl /=.
  Qed.

  Lemma MPfunction_in0 Idim l Odim (p:MPparameter Idim l Odim):
    0 \in l -> exists y, MPfunction p =1 (fun => y).
  Proof.
    move => H.
    elim /last_ind : l H Odim p =>[|l Hdim IHl]//=.
    rewrite mem_rcons => /orP [/eqP<-|/IHl H] Odim p.
    - exists (MPparameter_last p).2 => input.
        by rewrite MPfunction_rcons /= MP1_Idim0.
    - case : (H _ (MPparameter_belast p)) => y0 Hy0.
      exists (MP1 (MPparameter_last p) (actf y0)) => input.
        by rewrite MPfunction_rcons /= Hy0.
  Qed.

End NNet_lemma.

(* ***************************** *)
Module monoNNet.

    Record class_of (I O C:Type) : Type :=
      Class {
          neuron1_class : neuron1.class_of I O C;
          mono_mixin : mononeuron1.mixin_of (neuron1.Pack neuron1_class);
          NNet_mixin : NNet.mixin_of (neuron1.Pack neuron1_class)
        }.

    Definition mono_class I O C m := mononeuron1.Class (@mono_mixin I O C m).
    Definition NNet_class I O C m := NNet.Class (@NNet_mixin I O C m).

  Section Packing.

    Structure type := Pack {NNetI; NNetO; NNetC; _:class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT
                           return class_of (NNetI cT) (NNetO cT) (NNetC cT)
      in c.
    Definition neuron1 := neuron1.Pack (neuron1_class class).
    Definition mononeuron1 := mononeuron1.Pack (mono_class class).
    Definition NNet := NNet.Pack (NNet_class class).

  End Packing.

  Module Exports.

    Notation monoNNetType := type.
    Coercion mono_mixin : class_of >-> mononeuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : class_of >-> neuron1.class_of.
    Coercion mono_class : class_of >-> mononeuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion neuron1 : monoNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : monoNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion NNet : monoNNetType >-> NNetType.
    Canonical NNet.

  End Exports.
End monoNNet.
Export monoNNet.Exports.

Section monoNNet_lemma.

  Variable (S:monoNNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let id := @NNid S.
  Let parameter := MP1parameter S.
  Let MPparameter := MPparameter S.

End monoNNet_lemma.

(* ***************************** *)
Module idCNNet.

  Record class_of (I O C:Type) :=
    Class {
        neuron1_class : neuron1.class_of I O C;
        mono_mixin : mononeuron1.mixin_of (neuron1.Pack neuron1_class);
        idC_mixin : idCneuron1.mixin_of
                      (mononeuron1.Pack (mononeuron1.Class mono_mixin));
        NNet_mixin : NNet.mixin_of (neuron1.Pack neuron1_class)
      }.

  Definition mono_class I O C m := mononeuron1.Class (@mono_mixin I O C m).
  Definition idC_class I O C m := idCneuron1.Class (@idC_mixin I O C m).
  Definition NNet_class I O C m := NNet.Class (@NNet_mixin I O C m).
  Definition monoNNet_class I O C m :=
    monoNNet.Class (@mono_class I O C m) (NNet_class m).

  Section Packing.

    Structure type := Pack {NNetI; NNetO; NNetC; _:class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT
                           return class_of (NNetI cT) (NNetO cT) (NNetC cT)
      in c.
    Definition neuron1 := neuron1.Pack (neuron1_class class).
    Definition mononeuron1 := mononeuron1.Pack (mono_class class).
    Definition idCneuron1 := idCneuron1.Pack (idC_class class).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).

  End Packing.

  Module Exports.

    Notation idCNNetType := type.
    Coercion mono_mixin : class_of >-> mononeuron1.mixin_of.
    Coercion idC_mixin : class_of >-> idCneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : class_of >-> neuron1.class_of.
    Coercion mono_class : class_of >-> mononeuron1.class_of.
    Coercion idC_class : class_of >-> idCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion neuron1 : idCNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : idCNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion idCneuron1 : idCNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion NNet : idCNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : idCNNetType >-> monoNNetType.
    Canonical monoNNet.

  End Exports.
End idCNNet.
Export idCNNet.Exports.

Section idCNNet_lemma.

  Variable (S:idCNNetType).
  Let I := NNetI S.
  Let O := NNetO S.
  Let C := NNetC S.
  Let action := @NNaction S.
  Let op := @NNop S.
  Let id := @NNid S.
  Let idC := @NNidC S.
  Let parameter := MP1parameter S.
  Let MPparameter := MPparameter S.

  Definition MPparameter0 := @MPparameter_zero S id idC.

  Fixpoint MPparameter_sum Idim1 l1 Odim1 Idim2 l2 Odim2 :
           MPparameter Idim1 l1 Odim1 ->
           MPparameter Idim2 l2 Odim2 ->
           MPparameter (Idim1 + Idim2) (l1 +l l2) (Odim1 + Odim2) :=
    match l1, l2 return
          MPparameter Idim1 l1 Odim1 ->
          MPparameter Idim2 l2 Odim2 ->
          MPparameter (Idim1 + Idim2) (l1 +l l2) (Odim1 + Odim2) with
    | [::],[::] => fun p1 p2 => MP1parameter_sum p1 p2
    | [::],_ => fun p1 _ => MP1parameter_sum p1 (MP1parameter0 _ _ _)
    | _,[::] => fun _ p2 => MP1parameter_sum (MP1parameter0 _ _ _) p2
    | _ :: _,_ :: _ => fun p1 p2 =>
                         (MP1parameter_sum p1.1 p2.1, MPparameter_sum p1.2 p2.2)
    end.

  Lemma MPparameter_sumA Idim1 l1 Odim1 Idim2 l2 Odim2 Idim3 l3 Odim3
        (p1:MPparameter Idim1 l1 Odim1) (p2:MPparameter Idim2 l2 Odim2)
        (p3:MPparameter Idim3 l3 Odim3):
    MPparameter_sum p1 (MPparameter_sum p2 p3) =
    cast_MPparameter (esym (addnA _ _ _))
                     (esym (seqopA addnA _ _ _))
                     (esym (addnA _ _ _))
                     (MPparameter_sum (MPparameter_sum p1 p2) p3).
  Proof.
    elim : l1 =>[|Hdim1 l1 IHl1] in Idim1 p1 Idim2 l2 p2 Idim3 l3 p3 *;
      case : l2 =>[|Hdim2 l2] in Idim2 p2 Idim3 l3 p3 *;
      case : l3 =>[|Hdim3 l3] in Idim3 p3 *;
      symmetry; apply /cast_MPparameterP;
      exists (esym (addnA _ _ _)), (esym (addnA _ _ _))=>/=;
      rewrite -?MP1parameter_sum0 -MP1parameter_sumA =>//.
    split=>//.
    apply /(cast_MPparameterP (esym (addnA _ _ _)) (esym (seqopA addnA _ _ _))
                              (esym (addnA _ _ _))).
    symmetry. exact : IHl1.
  Qed.

End idCNNet_lemma.

Module comoNNet.

  Record class_of (I O C:Type) :=
    Class {
        neuron1_class : neuron1.class_of I O C;
        mono_mixin : mononeuron1.mixin_of (neuron1.Pack neuron1_class);
        como_mixin : comoneuron1.mixin_of
                       (mononeuron1.Pack (mononeuron1.Class mono_mixin));
        NNet_mixin : NNet.mixin_of (neuron1.Pack neuron1_class)
      }.

  Definition mono_class I O C m := mononeuron1.Class (@mono_mixin I O C m).
  Definition como_class I O C m := comoneuron1.Class (@como_mixin I O C m).
  Definition NNet_class I O C m := NNet.Class (@NNet_mixin I O C m).
  Definition monoNNet_class I O C m :=
    monoNNet.Class (@mono_class I O C m) (NNet_class m).

  Section Packing.

    Structure type := Pack {NNetI; NNetO; NNetC; _:class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT
                           return class_of (NNetI cT) (NNetO cT) (NNetC cT)
      in c.
    Definition neuron1 := neuron1.Pack (neuron1_class class).
    Definition mononeuron1 := mononeuron1.Pack (mono_class class).
    Definition comoneuron1 := comoneuron1.Pack (como_class class).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).

  End Packing.

  Module Exports.

    Notation comoNNetType := type.
    Coercion mono_mixin : class_of >-> mononeuron1.mixin_of.
    Coercion como_mixin : class_of >-> comoneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : class_of >-> neuron1.class_of.
    Coercion mono_class : class_of >-> mononeuron1.class_of.
    Coercion como_class : class_of >-> comoneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion neuron1 : comoNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : comoNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion comoneuron1 : comoNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion NNet : comoNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : comoNNetType >-> monoNNetType.
    Canonical monoNNet.

  End Exports.
End comoNNet.
Export comoNNet.Exports.

Section comoNNet_lemma.
End comoNNet_lemma.

(* ***************************** *)
Module comidCNNet.

  Record class_of (I O C:Type) :=
    Class {
        neuron1_class : neuron1.class_of I O C;
        mono_mixin : mononeuron1.mixin_of (neuron1.Pack neuron1_class);
        como_mixin : comoneuron1.mixin_of
                       (mononeuron1.Pack (mononeuron1.Class mono_mixin));
        idC_mixin : idCneuron1.mixin_of
                      (mononeuron1.Pack (mononeuron1.Class mono_mixin));
        NNet_mixin : NNet.mixin_of (neuron1.Pack neuron1_class)
      }.

  Definition mono_class I O C m := mononeuron1.Class (@mono_mixin I O C m).
  Definition como_class I O C m := comoneuron1.Class (@como_mixin I O C m).
  Definition idC_class I O C m := idCneuron1.Class (@idC_mixin I O C m).
  Definition comidC_class I O C m :=
    comidCneuron1.Class (@como_class I O C m) (idC_class m).
  Definition NNet_class I O C m := NNet.Class (@NNet_mixin I O C m).
  Definition monoNNet_class I O C m :=
    monoNNet.Class (@mono_class I O C m) (NNet_class m).
  Definition comoNNet_class I O C m :=
    comoNNet.Class (@como_class I O C m) (NNet_class m).
  Definition idCNNet_class I O C m :=
    idCNNet.Class  (@idC_class I O C m) (NNet_class m).

  Section Packing.

    Structure type := Pack {NNetI; NNetO; NNetC; _:class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT
                           return class_of (NNetI cT) (NNetO cT) (NNetC cT)
      in c.
    Definition neuron1 := neuron1.Pack (neuron1_class class).
    Definition mononeuron1 := mononeuron1.Pack (mono_class class).
    Definition comoneuron1 := comoneuron1.Pack (como_class class).
    Definition idCneuron1 := idCneuron1.Pack (idC_class class).
    Definition comidCneuron1 := comidCneuron1.Pack (comidC_class class).
    Definition NNet := NNet.Pack (NNet_class class).
    Definition monoNNet := monoNNet.Pack (monoNNet_class class).
    Definition comoNNet := comoNNet.Pack (comoNNet_class class).
    Definition idCNNet := idCNNet.Pack (idCNNet_class class).

  End Packing.

  Module Exports.

    Notation comidCNNetType := type.
    Coercion mono_mixin : class_of >-> mononeuron1.mixin_of.
    Coercion como_mixin : class_of >-> comoneuron1.mixin_of.
    Coercion idC_mixin : class_of >-> idCneuron1.mixin_of.
    Coercion NNet_mixin : class_of >-> NNet.mixin_of.
    Coercion neuron1_class : class_of >-> neuron1.class_of.
    Coercion mono_class : class_of >-> mononeuron1.class_of.
    Coercion como_class : class_of >-> comoneuron1.class_of.
    Coercion idC_class : class_of >-> idCneuron1.class_of.
    Coercion comidC_class : class_of >-> comidCneuron1.class_of.
    Coercion NNet_class : class_of >-> NNet.class_of.
    Coercion monoNNet_class : class_of >-> monoNNet.class_of.
    Coercion comoNNet_class : class_of >-> comoNNet.class_of.
    Coercion idCNNet_class : class_of >-> idCNNet.class_of.
    Coercion neuron1 : comidCNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : comidCNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion comoneuron1 : comidCNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion idCneuron1 : comidCNNetType >-> idCneuron1Type.
    Canonical idCneuron1.
    Coercion comidCneuron1 : comidCNNetType >-> comidCneuron1Type.
    Canonical comidCneuron1.
    Coercion NNet : comidCNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : comidCNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion comoNNet : comidCNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion idCNNet : comidCNNetType >-> idCNNetType.
    Canonical idCNNet.

  End Exports.
End comidCNNet.
Export comidCNNet.Exports.

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
  Let parameter := MP1parameter S.
  Let MPparameter := MPparameter S.

  Lemma MPfunction_sum Idim1 l1 Odim1 Idim2 l2 Odim2
        (p1:MPparameter Idim1 l1 Odim1) (p2:MPparameter Idim2 l2 Odim2) input:
    size l1 = size l2 ->
    MPfunction (MPparameter_sum p1 p2) input =
    index_app (MPfunction p1 (index_projl input))
              (MPfunction p2 (index_projr input)).
  Proof.
    elim : l1 l2 =>[|Hdim1 l1 IHl1][|Hdim2 l2]//= in Idim1 p1 Idim2 p2 input *;
      rewrite MP1_sum =>//[][] /IHl1 =>->.
      by rewrite !actf_app index_projl_app index_projr_app.
  Qed.

End comidCNNet_lemma.

(* ***************************** *)
Module eqneuron1.

  Section Packing.

    Record type := Pack {NNetI:eqType; NNetO; NNetC;
                         neuron1_class : neuron1.class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition neuron1 := neuron1.Pack (neuron1_class cT).

  End Packing.

  Module Exports.

    Notation eqneuron1Type := type.
    Coercion NNetI : eqneuron1Type >-> eqType.
    Coercion neuron1_class : eqneuron1Type >-> neuron1.class_of.
    Coercion neuron1 : eqneuron1Type >-> neuron1Type.
    Canonical neuron1.

  End Exports.
End eqneuron1.
Export eqneuron1.Exports.

Section eqneuron1_lemma.

  Variable (V:eqneuron1Type).
  Let I := NNetI V.
  Let O := NNetO V.
  Let C := NNetC V.
  Let action := @NNaction V.
  Let op := @NNop V.

End eqneuron1_lemma.

(* ***************************** *)
Module eqcomoNNet.

  Section Packing.

    Structure type := Pack {NNetI:eqType; NNetO; NNetC;
                            comNNet_class :comoNNet.class_of NNetI NNetO NNetC}.
    Variable (cT:type).
    Definition class :=
      let: Pack _ _ _ c := cT
                           return comoNNet.class_of
                                    (NNetI cT) (NNetO cT) (NNetC cT) in c.
    Definition neuron1 := neuron1.Pack class.
    Definition mononeuron1 := mononeuron1.Pack class.
    Definition comoneuron1 := comoneuron1.Pack class.
    Definition NNet := NNet.Pack class.
    Definition monoNNet := monoNNet.Pack class.
    Definition comoNNet := comoNNet.Pack class.
    Definition eqneuron1 := eqneuron1.Pack class.

  End Packing.

  Module Exports.

    Notation eqcomoNNetType := type.
    Coercion NNetI : eqcomoNNetType >-> eqType.
    Coercion neuron1 : eqcomoNNetType >-> neuron1Type.
    Canonical neuron1.
    Coercion mononeuron1 : eqcomoNNetType >-> mononeuron1Type.
    Canonical mononeuron1.
    Coercion comoneuron1 : eqcomoNNetType >-> comoneuron1Type.
    Canonical comoneuron1.
    Coercion NNet : eqcomoNNetType >-> NNetType.
    Canonical NNet.
    Coercion monoNNet : eqcomoNNetType >-> monoNNetType.
    Canonical monoNNet.
    Coercion comoNNet : eqcomoNNetType >-> comoNNetType.
    Canonical comoNNet.
    Coercion eqneuron1 : eqcomoNNetType >-> eqneuron1Type.
    Canonical eqneuron1.

  End Exports.
End eqcomoNNet.
Export eqcomoNNet.Exports.

Section eqcomoNNet_lemma.

  Variable (V:eqcomoNNetType).
  Let I := NNetI V.
  Let O := NNetO V.
  Let C := NNetC V.
  Let action := @NNaction V.
  Let op := @NNop V.
  Let id := @NNid V.
  Let actf := @NNactf V.

End eqcomoNNet_lemma.

End NNetDef.

Export neuron1.Exports mononeuron1.Exports comoneuron1.Exports
       idCneuron1.Exports comidCneuron1.Exports NNet.Exports monoNNet.Exports
       comoNNet.Exports idCNNet.Exports comidCNNet.Exports
       eqneuron1.Exports eqcomoNNet.Exports.
