From mathcomp
     Require Import all_ssreflect all_algebra.
From mathcomp
     Require Import ssralg.
Add LoadPath "../mylib".
Require Export mylib mybig myalg.
Require Export NNet_sub_def NNet NNet_alg NNet_num MPsolvable MPsolvable_alg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export GRing NNetDef NNet_algDef.

(* ***************************** *)
Section numDomainNNet.
  Variable (R:numDomainNNetType).
  Let I := NNetI R.
  Let O := NNetO R.
  Let C := NNetC R.
  Let actf := @NNactf R.
  Let activation := @NNactivation R.
  Let parameter := @MP1parameter R.
  Let MPparameter := @MPparameter R.
  Let expressive_number := @expressive_number R.
  Let inner_prod := (@inner_prod _ (regular_lmodType R)).

  Lemma expressive_number_Idim1 Idim l Odim n:
    expressive_number 1 l Odim n -> expressive_number Idim l Odim n.
  Proof.
    move => H1 s f Hsize. case : (inner_prod_ex_inj s) => w Hinj.
    case : (in_inj_inv 0%R Hinj) => g Hg.
    move : {H1}(H1 (map (fun x => [ffun => inner_prod w x]) s)
                   (fun x => f (g (x ord0)))).
    rewrite size_map => H. case : {H}(H Hsize).
    case : l =>[|Hdim l]/= p Hp.
    - exists ([ffun i => [ffun j => p.1 i ord0 * w j]%R],p.2) => x Hx /=.
      apply /ffunP => i. move : (Hp [ffun => (inner_prod w x)] (map_f _ Hx)).
      rewrite !ffunE /= (Hg _ Hx) (@neuron1_inner_prod R) inner_prod_mull =>->.
      rewrite ffunE (@neuron1_inner_prod R).
      by rewrite {1}/myalg.inner_prod big_ord_recl big_ord0 ffunE addr0.
    - exists (([ffun i => [ffun j => p.1.1 i ord0 * w j]%R],p.1.2),p.2)
      => x Hx /=. move : (Hp [ffun => (inner_prod w x)] (map_f _ Hx)).
      rewrite !ffunE (Hg _ Hx) =>->. congr(MPfunction p.2 (NNactf _)).
      apply /ffunP => i.
      rewrite !ffunE /= !(@neuron1_inner_prod R) inner_prod_mull.
        by rewrite {1}/myalg.inner_prod big_ord_recl big_ord0 ffunE addr0.
  Qed.

  Lemma expressive_number_Idim_independent Idim1 Idim2 l Odim n:
    0 < Idim1 ->
    expressive_number Idim1 l Odim n -> expressive_number Idim2 l Odim n.
  Proof.
    move => H1. move /(expressive_number_Idim_le H1).
    exact : expressive_number_Idim1.
  Qed.

End numDomainNNet.