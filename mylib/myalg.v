From mathcomp
     Require Import all_ssreflect.
From mathcomp
     Require Import ssralg zmodp ssrnum.
Require Export mylib mybig.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export GRing Num Num.Theory.

(* ***************************** *)
Section ssralg.

  Section zmod_rel.
    Variable (R:zmodType).
    Variable (r0:R).

    Variable (T:zmodType).
    Variable (order:rel T).
    Definition sgn (t:T) : R :=
      if order 0%R t then if order t 0%R then 0%R else r0
      else if order t 0%R then (- r0)%R else 0%R.

    Lemma sgn_posl t : strict order 0%R t -> sgn t = r0.
    Proof. rewrite /strict /sgn. by case /andP =>-> /negbTE ->. Qed.

    Lemma sgn_negl t : strict order t 0%R -> sgn t = (- r0)%R.
    Proof. rewrite /strict /sgn. by case /andP =>-> /negbTE ->. Qed.

    Lemma sgn_equiv0l t : equiv order 0%R t -> sgn t = 0%R.
    Proof. rewrite /equiv /sgn. by case /andP =>->->. Qed.

    Lemma sgn_incomp t : incomp order 0%R t -> sgn t = 0%R.
    Proof. rewrite /incomp /sgn. by case /andP => /negbTE -> /negbTE ->. Qed.

    CoInductive xor_sgn t : R -> bool -> bool -> bool -> bool -> Set :=
    | XorSgnPos of strict order 0%R t : xor_sgn t r0 true false false false
    | XorSgnNeg of strict order t 0%R : xor_sgn t (- r0) false true false false
    | XorSgnEquiv of equiv order 0%R t : xor_sgn t 0 false false true false
    | XorSgnIncomp of incomp order 0%R t : xor_sgn t 0 false false false true.

    Lemma sgnP t :
      xor_sgn t (sgn t) (strict order 0%R t) (strict order t 0%R)
              (equiv order 0%R t) (incomp order 0%R t).
    Proof.
      case : relP => H.
      - rewrite sgn_posl =>//. by constructor.
      - rewrite sgn_negl =>//. by constructor.
      - rewrite sgn_equiv0l =>//. by constructor.
      - rewrite sgn_incomp =>//. by constructor.
    Qed.

    Section sgn_reflection.
      Section equiv0_reflection.

        Lemma sgn_N1neq0 : r0 <> 0%R <-> (- r0)%R <> 0%R.
        Proof.
          split.
          - move => H /eqP. by rewrite oppr_eq0 => /eqP.
          - move => H /eqP. by rewrite -[r0]opprK oppr_eq0 => /eqP.
        Qed.

        Hypothesis (Hr0:r0 <> 0%R).
        Hypothesis (Htotal : total order).

        Lemma sgn_equiv0 t : reflect (sgn t = 0%R) (equiv order 0%R t).
        Proof.
          apply /(iffP idP); first exact : sgn_equiv0l. rewrite /sgn /equiv.
          case : ifP =>H0t; case : ifP =>// Ht0 Heq.
          - by move /sgn_N1neq0 : Hr0; rewrite Heq.
          - by move : (Htotal 0%R t); rewrite H0t Ht0.
        Qed.
        
      End equiv0_reflection.

      Lemma sgn_2neq0 : (r0 *+ 2)%R <> 0%R <-> (-r0)%R <> r0.
      Proof.
        split.
        - move => H1 H. apply : H1. by rewrite mulr2n -{1}H addNr.
        - move => H H1. apply : H. apply /eqP.
          rewrite eqr_oppLR -addr_eq0 -mulr2n. exact /eqP.
      Qed.

      Hypothesis (Hr0:(r0 *+ 2)%R <> 0%R).

      Lemma sgn_1neq0 : r0 <> 0%R.
      Proof. move => H. apply : Hr0. by rewrite H mulr2n add0r. Qed.

      Lemma sgn_pos t : reflect (sgn t = r0) (strict order 0%R t).
      Proof.
        apply /(iffP idP); first exact : sgn_posl. rewrite /sgn /strict.
        case : ifP =>_; case : ifP =>_// Heq.
        - by move : sgn_1neq0; rewrite Heq.
        - by move /sgn_2neq0 : Hr0.
        - by move : sgn_1neq0; rewrite Heq.
      Qed.

      Lemma sgn_neg t : reflect (sgn t = (- r0)%R) (strict order t 0%R).
      Proof.
        apply /(iffP idP); first exact : sgn_negl. rewrite /sgn /strict.
        case : ifP =>_; case : ifP =>_// Heq.
        - by move /sgn_N1neq0 : sgn_1neq0; rewrite Heq.
        - by move /sgn_2neq0 : Hr0; rewrite -Heq.
        - by move /sgn_N1neq0 : sgn_1neq0; rewrite Heq.
      Qed.

      Inductive xor_total_sgn t : R -> bool -> bool -> bool -> Set :=
      | TotalSgnPos of strict order 0%R t : xor_total_sgn t r0 true false false
      | TotalSgnNeg of strict order t 0%R :
          xor_total_sgn t (- r0) false true false
      | TotalSgnEquiv of equiv order 0%R t : xor_total_sgn t 0 false false true.

      Hypothesis (Htotal : total order).

      Lemma total_sgnP t :
        xor_total_sgn t (sgn t)
                (strict order 0%R t) (strict order t 0%R) (equiv order 0%R t).
      Proof.
        case : (totalP Htotal 0%R t) => H.
        - rewrite (sgn_pos _ H). by constructor.
        - rewrite (sgn_neg _ H). by constructor.
        - rewrite (sgn_equiv0 sgn_1neq0 _ _ H)=>//. by constructor.
      Qed.

    End sgn_reflection.

    Section sgn_trans.

      Hypothesis (Htrans: transitive order).

      Lemma equiv_sgn x y: equiv order x y -> sgn x = sgn y.
      Proof.
        rewrite /sgn. case /andP => Hxy Hyx.
        case : ifP => H0x; first rewrite (Htrans H0x Hxy).
        - case : ifP; first by move /(Htrans Hyx) =>->.
          case : ifP =>//. by move /(Htrans Hxy) =>->.
        - case : (ifP (order 0%R y)) => Hy0;
            first by move : (Htrans Hy0 Hyx) H0x =>->.
          case : ifP; first by move /(Htrans Hyx) =>->.
          case : ifP =>//. by move /(Htrans Hxy) =>->.
      Qed.

    End sgn_trans.
  End zmod_rel.

  Section zmod_rel_monof.
    Variable (T:zmodType).

    Section homo_rel.

      Variable (order:rel T).
      Hypothesis (homoR :forall z:T, {homo +%R^~ z : x y / order x y}).

      Lemma rel_addr2r z : {mono +%R^~ z : x y / order x y}.
      Proof. apply : (ssrbool.homo_mono (addrK _)); exact : homoR. Qed.

      Lemma rel_addr2l z : {mono +%R z : x y / order x y}.
      Proof. move => x y. rewrite ![(z + _)%R]addrC. exact : rel_addr2r. Qed.

      Lemma strict_homo z : {homo +%R^~ z : x y / strict order x y}.
      Proof. move => x y. by rewrite /strict !rel_addr2r. Qed.

      Lemma strict_addr2l z : {mono +%R z : x y / strict order x y}.
      Proof. move => x y. by rewrite /strict !rel_addr2l. Qed.

      Lemma strict_addr2r z : {mono +%R^~ z : x y / strict order x y}.
      Proof. move => x y. by rewrite /strict !rel_addr2r. Qed.

    End homo_rel.

    Section mono.
      Variable (X:Type).
      Variable (R:T -> T -> X).
      Hypothesis (monof_addr2r :forall z:T, {mono +%R^~ z : x y / R x y}).

      Lemma monof_addr2l z : {mono +%R z : x y / R x y}.
      Proof. move => x y. rewrite ![(z + _)%R]addrC. exact : monof_addr2r. Qed.

      Lemma monof_subrl x y z: R (x - z) y = R x (y + z).
      Proof. by rewrite -(monof_addr2r z) -addrA addNr addr0. Qed.

      Lemma monof_subrr x y z: R x (y - z) = R (x + z) y.
      Proof. by rewrite -(monof_addr2r z) -addrA addNr addr0. Qed.

      Lemma monof_subrl0 x y: R (x - y) 0 = R x y.
      Proof. rewrite -{2}[y]add0r. exact : monof_subrl. Qed.

      Lemma monof_subrr0 x y: R 0 (y - x) = R x y.
      Proof. rewrite -{2}[x]add0r. exact : monof_subrr. Qed.

      Lemma monof_oppl x y: R (- x) y = R 0 (y + x).
      Proof. rewrite -sub0r. exact : monof_subrl. Qed.

      Lemma monof_oppr x y: R x (- y) = R (x + y) 0.
      Proof. rewrite -sub0r. exact : monof_subrr. Qed.

      Lemma monof_opp x y: R (- x) (- y) = R y x.
      Proof. by rewrite monof_oppl addrC monof_subrr0. Qed.

      Lemma monofNr x: R (- x) 0 = R 0 x.
      Proof. by rewrite monof_oppl add0r. Qed.

      Lemma monofrN x: R 0 (- x) = R x 0.
      Proof. by rewrite monof_oppr add0r. Qed.

    End mono.

    Section mono_rel.
      Variable (order:rel T).
      Hypothesis (order_mono :forall z:T, {mono +%R^~ z : x y / order x y}).

      Lemma equiv_mono z: {mono +%R^~ z : x y / equiv order x y}.
      Proof. move => x y. by rewrite /equiv !order_mono. Qed.

      Lemma strict_mono z : {mono +%R^~ z : x y / strict order x y}.
      Proof. move => x y. by rewrite /strict !order_mono. Qed.

      Hypothesis (order_trans : transitive order).

      Lemma rel_addr x y z w:
        order x y -> order z w -> order (x + z)%R (y + w)%R.
      Proof.
        move => Hxy Hzw. apply : (@order_trans (y + z)%R).
        - by rewrite order_mono.
        - by rewrite monof_addr2l.
      Qed.

      Lemma pos_addr x y: order 0%R x -> order 0%R y -> order 0%R (x + y)%R.
      Proof. rewrite -{3}[0%R]addr0. exact : rel_addr. Qed.

      Lemma neg_addr x y: order x 0%R -> order y 0%R -> order (x + y)%R 0%R.
      Proof. rewrite -{3}[0%R]addr0. exact : rel_addr. Qed.

      Lemma rel_mulrl n: {homo ((@natmul T)^~ n.+1) : x y / order x y}.
      Proof.
        move => x y Hxy. elim : n =>[|n IHn]; first by rewrite !mulr1n.
        rewrite mulrS [(y *+ _)%R]mulrS. exact : rel_addr.
      Qed.

      Lemma pos_mulrl n: {homo ((@natmul T)^~ n.+1) : x / order 0%R x}.
      Proof. move => x. move /(rel_mulrl n). by rewrite mul0rn. Qed.

      Lemma neg_mulrl n: {homo ((@natmul T)^~ n.+1) : x / order x 0%R}.
      Proof. move => x. move /(rel_mulrl n). by rewrite mul0rn. Qed.

      Lemma equiv_addr x y z w:
        equiv order z w -> order (x + z)%R (y + w)%R = order x y.
      Proof.
        case /andP => Hzw. rewrite -monof_opp =>// Hwz.
        apply :(sameP idP). apply : (iffP idP) => H; first exact : rel_addr Hzw.
        move : (rel_addr H Hwz). by rewrite -!addrA !addrN !addr0.
      Qed.

      Lemma equiv_equiv_addr x y z w:
        equiv order z w -> equiv order (x + z)%R (y + w)%R = equiv order x y.
      Proof.
        move => Hzw. rewrite /equiv !equiv_addr =>//. by rewrite equiv_symm.
      Qed.

      Lemma equiv_strict_addr x y z w:
        equiv order z w -> strict order (x + z)%R (y + w)%R = strict order x y.
      Proof.
        move => Hzw. rewrite /strict !equiv_addr =>//. by rewrite equiv_symm.
      Qed.

      Lemma equiv0_addrl x y z:
        equiv order 0%R z -> order (x + z)%R y = order x y.
      Proof. rewrite -{1}[y]addr0 equiv_symm. exact : equiv_addr. Qed.

      Lemma equiv0_addrr x y z:
        equiv order 0%R z -> order x (y + z)%R = order x y.
      Proof. rewrite -{1}[x]addr0. exact : equiv_addr. Qed.

      Lemma equiv0_equiv_addrl x y z:
        equiv order 0%R z -> equiv order (x + z)%R y = equiv order x y.
      Proof. rewrite -{1}[y]addr0 equiv_symm. exact : equiv_equiv_addr. Qed.

      Lemma equiv0_equiv_addrr x y z:
        equiv order 0%R z -> equiv order x (y + z)%R = equiv order x y.
      Proof. rewrite -{1}[x]addr0. exact : equiv_equiv_addr. Qed.

      Lemma equiv0_strict_addrl x y z:
        equiv order 0%R z -> strict order (x + z)%R y = strict order x y.
      Proof. rewrite -{1}[y]addr0 equiv_symm. exact : equiv_strict_addr. Qed.

      Lemma equiv0_strict_addrr x y z:
        equiv order 0%R z -> strict order x (y + z)%R = strict order x y.
      Proof. rewrite -{1}[x]addr0. exact : equiv_strict_addr. Qed.

      Lemma strict_pos_addr x y:
        strict order 0%R x -> order 0%R y -> strict order 0%R (x + y)%R.
      Proof.
        rewrite /strict. case /andP => Hx0 Hn0x H0y. apply /andP.
        split; first exact : pos_addr. apply /negP.
        rewrite -monof_oppr =>//. move /(rel_addr H0y).
        rewrite add0r addrN. exact /negP.
      Qed.

      Lemma strict_neg_addr x y:
        strict order x 0%R -> order y 0%R -> strict order (x + y)%R 0%R.
      Proof.
        rewrite -!(monofrN strict_mono) opprD -monofrN=>//.
        exact : strict_pos_addr.
      Qed.

      Hypothesis (Htotal:total order).

      Lemma rel_eq_addr x y z w:
        order x y = order z w -> order (x + z)%R (y + w)%R = order x y.
      Proof.
        case : (totalP Htotal x y) => []/andP[]Hxy Hyx Heq.
        - move : (Hxy). rewrite {1}Heq. by move /(rel_addr Hxy) =>->.
        - move /negbTE : (Hyx). case H : (order (x + z)%R (y + w)%R)=>//.
          rewrite {1}Heq => Hzw. move : (Hzw) (Htotal z w) =>->/=.
          rewrite -monof_opp=>//. move /(rel_addr H). by rewrite !addrK =>->.
        - move : (Hxy). rewrite {1}Heq. by move /(rel_addr Hxy) =>->.
      Qed.

      Lemma rel_mulr n: {mono ((@natmul T)^~ n.+1) : x y / order x y}.
      Proof.
        move => x y. elim : n =>[|n IHn]; first by rewrite mulr1n.
        rewrite mulrS [(y *+ _)%R]mulrS. exact : rel_eq_addr.
      Qed.

      Lemma pos_mulr n: {mono ((@natmul T)^~ n.+1) : x / order 0%R x}.
      Proof. move => x. by rewrite -(rel_mulr n _ x) mul0rn. Qed.

      Lemma neg_mulr n: {mono ((@natmul T)^~ n.+1) : x / order x 0%R}.
      Proof. move => x. by rewrite -(rel_mulr n x _) mul0rn. Qed.

      Lemma equiv_mulr n: {mono ((@natmul T)^~ n.+1) : x y / equiv order x y}.
      Proof. move => x y. by rewrite /equiv !rel_mulr. Qed.

      Lemma equiv_pos_mulr n:
        {mono ((@natmul T)^~ n.+1) : x / equiv order 0%R x}.
      Proof. move => x. by rewrite /equiv pos_mulr neg_mulr. Qed.

      Lemma equiv_neg_mulr n:
        {mono ((@natmul T)^~ n.+1) : x / equiv order x 0%R}.
      Proof. move => x. by rewrite /equiv neg_mulr pos_mulr. Qed.

      Lemma strict_mulr n: {mono ((@natmul T)^~ n.+1) : x y / strict order x y}.
      Proof. move => x y. by rewrite /strict !rel_mulr. Qed.

      Lemma strict_pos_mulr n:
        {mono ((@natmul T)^~ n.+1) : x / strict order 0%R x}.
      Proof. move => x. by rewrite /strict pos_mulr neg_mulr. Qed.

      Lemma strict_neg_mulr n:
        {mono ((@natmul T)^~ n.+1) : x / strict order x 0%R}.
      Proof. move => x. by rewrite /strict neg_mulr pos_mulr. Qed.

    End mono_rel.

    Section zmod_sgn.
      Variable (R:zmodType).
      Variable (r0:R).
      Variable (order:rel T).
      Let sgn := sgn r0 order.
      Hypothesis (order_mono :forall z:T, {mono +%R^~ z : x y / order x y}).

      Lemma sgnN : {morph sgn : x / (- x)%R}.
      Proof.
        move => x. rewrite /sgn /ssralg.sgn monofrN =>//. rewrite monofNr =>//.
        case : ifP =>_; case : ifP =>_//.
        - by rewrite oppr0.
        - by rewrite opprK.
        - by rewrite oppr0.
      Qed.

      Hypothesis (order_trans : transitive order).

      Lemma mulr_sgn0 x n: sgn (x *+ n.+1)%R = 0%R -> sgn x = 0%R.
      Proof.
        rewrite {2}/sgn. case : sgnP =>// H <-; symmetry.
        - apply : sgn_posl.
          exact : (pos_mulrl (strict_mono _) (strict_trans _)).
        - apply : sgn_negl.
          exact : (neg_mulrl (strict_mono _) (strict_trans _)).
      Qed.

      Lemma equiv0_sgn_addr x y: equiv order 0%R y -> sgn (x + y)%R = sgn x.
      Proof.
        rewrite /sgn /ssralg.sgn => H.
        rewrite (equiv0_addrl _ _ _ _ H) =>//.
          by rewrite (equiv0_addrr _ _ _ _ H) =>//.
      Qed.

      Hypothesis (Hr0:(r0 *+ 2)%R <> 0%R).
      Hypothesis (Htotal:total order).

      Lemma sgn_addr x y r: sgn x = r -> sgn y = r -> sgn (x + y)%R = r.
      Proof.
        rewrite {1}/sgn. case : (total_sgnP Hr0 Htotal) => Hx <-.
        - move /sgn_pos => H. apply /sgn_pos =>//.
          exact /(pos_addr (strict_mono _) (strict_trans _) Hx (H _)) =>//.
        - move /sgn_neg => H. apply /sgn_neg =>//.
          exact /(neg_addr (strict_mono _) (strict_trans _) Hx (H _)) =>//.
        - move /(sgn_equiv0 (sgn_1neq0 _)) => H. apply /sgn_equiv0 =>//.
          exact : sgn_1neq0.
          rewrite equiv0_equiv_addrr =>//. exact : H.
      Qed.

      Lemma sgn_mulr x n : sgn (x *+ n.+1) = sgn x.
      Proof.
        elim : n =>[|n IHn]; first by rewrite mulr1n. rewrite mulrS.
        exact : sgn_addr.
      Qed.

      Lemma sgn0_addr x y : sgn y = 0%R -> sgn (x + y)%R = sgn x.
      Proof.
        move /(sgn_equiv0 (sgn_1neq0 Hr0) Htotal).
        exact : equiv0_sgn_addr.
      Qed.

    End zmod_sgn.

    Section ring_sgn.
      Variable (R:ringType).
      Variable (order:rel T).
      Notation sgn := (sgn (1%R:R)).
      Let sgn := sgn order.

      Lemma sgnC : commutative (fun x y => (sgn x * sgn y)%R).
      Proof.
        rewrite /commutative /sgn /ssralg.sgn => x y.
        by case : ifP; case : ifP; case : ifP; case : ifP;
        rewrite ?mul0r ?mulr0 ?mulrNN ?mul1r ?mulr1.
      Qed.

      Lemma sgnCA x y z:
        (sgn x * (sgn y * sgn z))%R = (sgn y * (sgn x * sgn z))%R.
      Proof. by rewrite mulrA sgnC -mulrA. Qed.

      Lemma sgnAC x y z:
        (sgn x * sgn y * sgn z)%R = (sgn x * sgn z * sgn y)%R.
      Proof. by rewrite -mulrA sgnC mulrA. Qed.

      Lemma sgnACA x y z t:
        (sgn x * sgn y * (sgn z * sgn t))%R =
        (sgn x * sgn z * (sgn y * sgn t))%R.
      Proof. rewrite !mulrA. congr (_ * _)%R. exact : sgnAC. Qed.

    End ring_sgn.

  End zmod_rel_monof.

  Section Ring.
    Variable (R:ringType).

    Lemma prodN1_ord n:
      (\prod_(i < n) (-1:R))%R = if odd n then (-1)%R else 1%R.
    Proof.
      elim : n =>[|n IHn]/=; first by rewrite big_ord0.
      rewrite big_ord_recl IHn mulN1r. case : ifP =>//. by rewrite opprK.
    Qed.

  End Ring.

  Section vector.
    Variable (R:ringType).
    Variable (V:lmodType R).
    Variable (n:nat).

    Definition vscaler (a:R) (v:V^n) : V^n := [ffun i => (a *: (v i))%R].

    Lemma vscalerA a b v :
      vscaler a (vscaler b v) = vscaler (a * b)%R v.
    Proof. apply /ffunP => i. by rewrite !ffunE scalerA. Qed.

    Lemma vscaler1v v : vscaler 1 v = v.
    Proof. apply /ffunP => i. by rewrite ffunE scale1r. Qed.

    Lemma vscalerDr : right_distributive vscaler +%R.
    Proof. move => a u v. apply /ffunP => i. by rewrite !ffunE scalerDr. Qed.

    Lemma vscalerDl v : {morph vscaler^~ v : a b / (a + b)%R}.
    Proof. move => a b. apply /ffunP => i. by rewrite !ffunE scalerDl. Qed.

    Definition regular_vector_lmodMixin :=
      Lmodule.Mixin vscalerA vscaler1v vscalerDr vscalerDl.
    Canonical regular_vector_lmodType := LmodType _ _ regular_vector_lmodMixin.
  End vector.

  Section Lmodule.

    Lemma scaler_mul (R:ringType) (a:R) (x:regular_lmodType R) :
      (a *: x = a * x)%R.
    Proof. done. Qed.

    Section inner_prod.
      Variable (R:ringType).
      Variable (V:lmodType R).

      Definition inner_prod n (a: R^n) (v:V^n) : V := \sum_i (a i) *: (v i).

      Lemma inner_prod0r n (v:V^n): inner_prod [ffun => 0%R] v = 0%R.
      Proof. apply : big1 => i _. by rewrite ffunE scale0r. Qed.

      Lemma inner_prodr0 n (a:R^n): inner_prod a [ffun => 0%R] = 0%R.
      Proof. apply : big1 => i _. by rewrite ffunE scaler0. Qed.

      Lemma inner_prod_addr n (a:R^n) : {morph (inner_prod a) : u v /(u + v)%R}.
      Proof.
        move => u v. rewrite /inner_prod -big_split. apply : eq_bigr => i _.
          by rewrite ffunE scalerDr.
      Qed.

      Lemma inner_prod_addl n (v:V^n) :
        {morph ((@inner_prod _)^~ v) : a b /(a + b)%R}.
      Proof.
        move => a b. rewrite /inner_prod -big_split. apply : eq_bigr => i _.
          by rewrite ffunE scalerDl.
      Qed.

      Lemma inner_prod_mull n k (a:R^n) v :
        inner_prod [ffun i => (k * a i)%R] v = (k *: inner_prod a v)%R.
      Proof.
        rewrite /inner_prod scaler_sumr. apply : eq_bigr => i _.
          by rewrite ffunE scalerA.
      Qed.

      Lemma inner_prod_index_app n m (a1:R^n) (a2:R^m) v1 v2 :
        inner_prod (index_app a1 a2) (index_app v1 v2) =
        (inner_prod a1 v1 + inner_prod a2 v2)%R.
      Proof.
        rewrite /inner_prod big_split_ord.
        congr(_ + _)%R; apply : eq_bigr => i _.
        - by rewrite !index_app_lshift.
        - by rewrite !index_app_rshift.
      Qed.

    End inner_prod.

    Section inner_prod_comRing.
      Variable (R:comRingType).
      Variable (V:lmodType R).

      Lemma inner_prod_mulr n k a (v:V^n) :
        inner_prod a [ffun i => (k *: v i)%R] = (k *: inner_prod a v)%R.
      Proof.
        rewrite /inner_prod scaler_sumr. apply : eq_bigr => i _.
        by rewrite ffunE !scalerA mulrC.
      Qed.
    End inner_prod_comRing.

    Section inner_prod_regular_comRing.
      Variable (R:comRingType).

      Lemma inner_prodC n : commutative (@inner_prod _ (regular_lmodType R) n).
      Proof.
        move => x y. apply : eq_bigr => i _. exact : mulrC.
      Qed.
    End inner_prod_regular_comRing.

    Section on1line.
      Variable (R:ringType).
      Variable (V:lmodType R).

      Definition on1line (S:pred V) :=
        exists e c:V, {in S, forall x, exists a, x = ((a*:e) + c)%R}.

      Lemma on1line_add (s:seq V) b :
        on1line (pred_of_eq_seq s) ->
        on1line (pred_of_eq_seq [seq (x + b)%R | x <- s]).
      Proof.
        move => [e] [c] H. exists e, (c + b)%R => y /mapP [x] /H [a]->->.
        exists a. by rewrite addrA.
      Qed.
    End on1line.

    Section on1line_com.
      Variable (R:comRingType).
      Variable (V:lmodType R).

      Lemma on1line_mul (s:seq V) a :
        on1line (pred_of_eq_seq s) ->
        on1line (pred_of_eq_seq [seq (a *: x)%R | x <- s]).
      Proof.
        move =>[e] [c] H.
        exists (a *: e)%R, (a *: c)%R => y /mapP [x] /H [a']->->.
        exists a'. by rewrite scalerDr !scalerA mulrC.
      Qed.

      Lemma on1line_inner_prod n m (w:(R ^ n) ^ m) (s:seq (V ^ n)) :
        on1line (pred_of_eq_seq s) ->
        on1line (pred_of_eq_seq
                   [seq [ffun i => inner_prod (w i) x] | x <- s]).
      Proof.
        move =>[e] [c] H.
        exists [ffun i => inner_prod (w i) e],
        [ffun i => inner_prod (w i) c] => y /mapP [x] /H [a]->->.
        exists a. apply /ffunP => i.
        by rewrite !ffunE inner_prod_addr -inner_prod_mulr.
      Qed.
    End on1line_com.
  End Lmodule.
  Section pair.

    Lemma big_pair_add I (M1 M2:zmodType) r (P:pred I) (F:I -> M1 * M2):
      (\sum_(i <- r | P i) F i =
       (\sum_(i <- r | P i) (F i).1, \sum_(i <- r | P i) (F i).2))%R.
    Proof.
      elim : r =>[|x r IHr]; first by rewrite !big_nil.
      rewrite !big_cons IHr. by case : ifP.
    Qed.

    Lemma big_pair_mul I (M1 M2:ringType) r (P:pred I) (F:I -> M1 * M2):
      (\prod_(i <- r | P i) F i =
       (\prod_(i <- r | P i) (F i).1, \prod_(i <- r | P i) (F i).2))%R.
    Proof.
      elim : r =>[|x r IHr]; first by rewrite !big_nil.
      rewrite !big_cons IHr. by case : ifP.
    Qed.
  End pair.
End ssralg.

Section zmodp.
  Variable (p':nat).
  Local Notation p := p'.+1.

  Lemma Zp_addz0 : right_id Zp0 (@Zp_add p').
  Proof. move => x. by rewrite Zp_addC Zp_add0z. Qed.

  Lemma Zp_addzN : right_inverse Zp0 (@Zp_opp p') (@Zp_add _).
  Proof. move => x. by rewrite Zp_addC Zp_addNz. Qed.

  Lemma Zp_add_inZp : {morph (@inZp p') : x y / x + y >-> Zp_add x y}.
  Proof. move => x y. symmetry. apply /ord_inj. exact : modnDm. Qed.

  Lemma Zp_mul_inZp : {morph (@inZp p') : x y / x * y >-> Zp_mul x y}.
  Proof. move => x y. symmetry. apply /ord_inj. exact : modnMm. Qed.

  Lemma Zp_add_inZpl x (y:'I_p) : Zp_add (inZp x) y = inZp (x + y).
  Proof. apply /ord_inj. exact : modnDml. Qed.

  Lemma Zp_add_inZpr (x:'I_p) y : Zp_add x (inZp y) = inZp (x + y).
  Proof. apply /ord_inj. exact : modnDmr. Qed.

  Lemma Zp_mul_inZpl x (y:'I_p) : Zp_mul (inZp x) y = inZp (x * y).
  Proof. apply /ord_inj. exact : modnMml. Qed.

  Lemma Zp_mul_inZpr (x:'I_p) y : Zp_mul x (inZp y) = inZp (x * y).
  Proof. apply /ord_inj. exact : modnMmr. Qed.

  Lemma inZp0 : @inZp p' 0 = Zp0.
  Proof. apply /ord_inj. exact : modn0. Qed.

  Lemma inZpp : @inZp p' p = Zp0.
  Proof. apply /ord_inj. exact : modnn. Qed.

  Lemma inZpMl m : @inZp p' (m * p) = Zp0.
  Proof. apply /ord_inj. exact : modnMl. Qed.

  Lemma inZpMr m : @inZp p' (p * m) = Zp0.
  Proof. apply /ord_inj. exact : modnMr. Qed.

End zmodp.

Notation "\min_ ( i <- r | P ) F" :=
  (\Sbig[min/0%R]_(i <- r | P) F)
    (at level 41, F at level 41, i, r at level 50,
     format "'[' \min_ ( i <- r | P ) '/ ' F ']'") : ring_scope.

Notation "\min_ ( i <- r ) F" :=
  (\Sbig[min/0%R]_(i <- r) F)
    (at level 41, F at level 41, i, r at level 50,
     format "\min_ ( i <- r ) F") : ring_scope.

Notation "\min_ ( i | P ) F" :=
  (\Sbig[min/0%R]_(i | P) F%N)
    (at level 41, F at level 41, i at level 50,
     format "\min_ ( i | P ) F") : ring_scope.

Notation "\max_ ( i <- r | P ) F" :=
  (\Sbig[max/0%R]_(i <- r | P) F)
    (at level 41, F at level 41, i, r at level 50,
     format "'[' \max_ ( i <- r | P ) '/ ' F ']'") : ring_scope.

Notation "\max_ ( i <- r ) F" :=
  (\Sbig[max/0%R]_(i <- r) F)
    (at level 41, F at level 41, i, r at level 50,
     format "\max_ ( i <- r ) F") : ring_scope.

Notation "\max_ ( i | P ) F" :=
  (\Sbig[max/0%R]_(i | P) F%N)
    (at level 41, F at level 41, i at level 50,
     format "\max_ ( i | P ) F") : ring_scope.

Section ssrnum.
  Section numDomain.
    Variable (R:numDomainType).
    Notation sgn := (sgn (1%R:R) (@le R)).

    Lemma sgn_sg : {in real, sgn =1 @sg R}.
    Proof. by rewrite /sgn /sg => x /real_ltrgt0P []. Qed.

    Lemma ler_comparable (x y z:R) : le x y -> le x z -> comparable le y z.
    Proof.
      rewrite -subr_ge0 =>/ger0_real Hxy.
      rewrite -subr_ge0 =>/ger0_real /(real_leVge Hxy). by rewrite !ler_add2r.
    Qed.

    Lemma ger_comparable (z x y:R) : le x z -> le y z -> comparable le x y.
    Proof.
      rewrite -subr_le0 =>/ler0_real Hxy.
      rewrite -subr_le0 =>/ler0_real /(real_leVge Hxy). by rewrite !ler_add2r.
    Qed.

    Lemma comparable_ler_trans : transitive (comparable (@le R)).
    Proof.
      by move => y x z /orP [] Hxy /orP [] Hyz;
        rewrite ?(ler_comparable Hxy Hyz) ?(ger_comparable Hxy Hyz)
                /comparable ?(ler_trans Hxy Hyz) ?(ler_trans Hyz Hxy) ?orbT.
    Qed.

    Section CTTpred.
      Definition realmin_CTTtrans : {in (@real R) & &, transitive le}
        := fun _ _ _ _ _ _ Hxy Hyz => ler_trans Hxy Hyz.

      Definition realmin_CTTpred_class_of :=
        CTTpred.Class realmin_CTTtrans (@real_leVge _)
                      (fun _ _ => erefl _).
      Canonical realmin_CTTpred := CTTpred.Pack realmin_CTTpred_class_of.

      Definition realmax_CTTtrans : {in (@real R) & &, transitive ge}
        := fun _ _ _ _ _ _ Hxy Hyz => ler_trans Hyz Hxy.
                                      
      Definition realmax_CTTpred_class_of :=
        CTTpred.Class realmax_CTTtrans
                      (fun _ _ Hx Hy => real_leVge Hy Hx)
                      (fun _ _ => erefl _).
      Canonical realmax_CTTpred := CTTpred.Pack realmax_CTTpred_class_of.
    End CTTpred.

    Section bigle.
      Variable (I:eqType).
      Variable (P:pred I) (F:I -> R).
      Hypothesis (HP : forall x, P x -> F x \in real).

      Lemma bigminr_hasC r: ~~ has P r -> (\min_(i <- r | P i) F i = 0)%R.
      Proof. exact : Sbig_hasC. Qed.

      Lemma bigminr_real r: (\min_(i <- r | P i) F i)%R \is real.
      Proof. exact : (Sbig_in_CTT (@real0 _)). Qed.

      Lemma bigminr_sup r M:
        {in r, forall x, P x -> le (F x) M -> le (\min_(i <- r | P i) F i)%R M}.
      Proof.
        move => x Hx Px Hle. move : (ler_real Hle) (HP Px) (Hle) =>-> HM.
        exact : (CTT_Sbigl (@real0 _)).
      Qed.

      Lemma bigminr_supP r M:
        has P r ->
        reflect (exists2 x, x \in r & P x /\ le (F x) M)
                (le (\min_(i <- r | P i) F i)%R M).
      Proof.
        move => Hhas.
        apply /(iffP idP) =>[Hle|[x Hx []]]; last exact : bigminr_sup.
        apply /(CTT_SbiglP (@real0 _))=>//=.
        rewrite (ger_real Hle). exact : bigminr_real.
      Qed.

      Lemma bigminr_infP r m:
        has P r ->
          reflect {in r, forall x, P x -> le m (F x)}
                  (le m (\min_(i <- r | P i) F i)%R).
      Proof.
        move => Hhas. apply /(iffP idP) =>[Hle|].
        - apply /(CTT_SbigrP (@real0 _))=>//=.
          rewrite (ler_real Hle). exact : bigminr_real.
        - case /hasP : (Hhas) => x Hx Px H.
          apply /(CTT_SbigrP (@real0 _))=>//=.
          move /ler_real : (H _ Hx Px) =>->. exact : HP.
      Qed.

      Lemma bigminr_le r:
        {in r, forall x, P x -> le (\min_(i <- r | P i) F i)%R (F x)}.
      Proof. exact : (CTT_Sbig_rel (@real0 _)). Qed.

      Lemma bigmaxr_hasC r: ~~ has P r -> (\max_(i <- r | P i) F i = 0)%R.
      Proof. exact : Sbig_hasC. Qed.

      Lemma bigmaxr_real r: (\max_(i <- r | P i) F i)%R \is real.
      Proof.
        exact : (@Sbig_in_CTT _ _ realmax_CTTpred _ (@real0 _)).
      Qed.

      Lemma bigmaxr_inf r m:
        {in r, forall x, P x -> le m (F x) -> le m (\max_(i <- r | P i) F i)%R}.
      Proof.
        move => x Hx Px Hle. move : (ger_real Hle) (HP Px) (Hle) =>-> HM.
        exact : (@CTT_Sbigl _ _ realmax_CTTpred _ (@real0 _)).
      Qed.

      Lemma bigmaxr_infP r m:
        has P r ->
        reflect (exists2 x, x \in r & P x /\ le m (F x))
                (le m (\max_(i <- r | P i) F i)%R).
      Proof.
        move => Hhas.
        apply /(iffP idP) =>[Hle|[x Hx []]]; last exact : bigmaxr_inf.
        apply /(@CTT_SbiglP _ _ realmax_CTTpred _ (@real0 _))=>//=.
        rewrite (ler_real Hle). exact : bigmaxr_real.
      Qed.

      Lemma bigmaxr_supP r M:
        has P r ->
          reflect {in r, forall x, P x -> le (F x) M}
                  (le (\max_(i <- r | P i) F i)%R M).
      Proof.
        move => Hhas. apply /(iffP idP) =>[Hle|].
        - apply /(@CTT_SbigrP _ _ realmax_CTTpred _ (@real0 _))=>//=.
          rewrite (ger_real Hle). exact : bigmaxr_real.
        - case /hasP : (Hhas) => x Hx Px H.
          apply /(@CTT_SbigrP _ _ realmax_CTTpred _ (@real0 _))=>//=.
          move /ger_real : (H _ Hx Px) =>->. exact : HP.
      Qed.

      Lemma bigmaxr_le r:
        {in r, forall x, P x -> le (F x) (\max_(i <- r | P i) F i)%R}.
      Proof.
        exact : (@CTT_Sbig_rel _ _ realmax_CTTpred _ (@real0 _)).
      Qed.
    End bigle.

    Definition mindist (r:seq R) :=
      (\min_(i <- [seq (x,y) | x <- r, y <- r]| let (x,y) := i in x != y)
        let (x,y) := i in norm (x - y))%R.

    Lemma mindist_le0 (r:seq R): le 0%R (mindist r).
    Proof.
      case Hhas : (has (fun i : R * R => let (x,y) := i in x != y)
                       [seq (x,y) | x <- r, y <- r]).
      - apply /(bigminr_infP _ _ Hhas)=>[[x y _]|[x y _ _]];
          first exact : normr_real. exact : normr_ge0.
      - rewrite /mindist bigminr_hasC; first by rewrite lerr.
        exact /negPf.
    Qed.

    Lemma mindist_inf (r:seq R):
      {in r &, forall x y, x != y -> le (mindist r) (norm (x - y))}.
    Proof.
      move => x y Hx Hy Hxy.
      apply : (@bigminr_sup _ _ _ _ _ _ (x,y))=>//[[a b _]|];
        first exact : normr_real.
      apply /allpairsP. by exists (x,y).
    Qed.

    Lemma mindist_eq0P r : reflect (mindist r = 0)%R (constant r).
    Proof.
      apply /(iffP (constant_inP r)) =>[H|H x y Hx Hy].
      - apply : bigminr_hasC.
        apply /hasPn =>[[x y]]/allpairsP [[a b]][]/= Ha Hb []->->.
          by rewrite (H _ _ Ha Hb) eq_refl.
      - case Hxy : (x != y); last by move /eqP : Hxy.
        move : H (@lerr R 0%R) =>{1}<-.
        case /bigminr_supP =>[[a b] _||[a b] _ [] /negP Hab];
          first exact : normr_real.
        + apply /hasP. exists (x,y)=>//. apply /allpairsP. by exists (x,y).
        + by rewrite normr_le0 subr_eq0.
    Qed.

    Definition maxdist (r:seq R) :=
      (\max_(i <- [seq (x,y) | x <- r, y <- r])
        let (x,y) := i in norm (x - y))%R.

    Lemma maxdist_le0 (r:seq R): le 0%R (maxdist r).
    Proof.
      case : r =>[|k r];
        first by (rewrite /maxdist bigmaxr_hasC //; exact : lerr).
      apply : bigmaxr_inf =>[[x y]|||]//.
      - apply /allpairsP. exists (k,k) =>/=. by rewrite mem_head.
      - exact : normr_ge0.
    Qed.

    Lemma maxdist_sup (r:seq R):
      {in r &, forall x y, le (norm (x - y)) (maxdist r)}.
    Proof.
      move => x y Hx Hy.
      apply : (@bigmaxr_inf _ _ _ _ _ _ (x,y))=>//[[a b _]|];
        first exact : Theory.normr_real.
      apply /allpairsP. by exists (x,y).
    Qed.

    Lemma maxdist_eq0P r : reflect (maxdist r = 0)%R (constant r).
    Proof.
      apply /(iffP (constant_inP r)) =>[|H x y Hx Hy].
      - case : r =>[|k r]// H. apply /eqP. rewrite eqr_le. apply /andP.
        split.
        + apply /bigmaxr_supP
          =>[[x y] _||[x y]/allpairsP[][a b][]/H Ha /Ha/=->[]->->_];
            first exact : normr_real.
          * apply /hasP. exists (k,k)=>//. apply /allpairsP. exists (k,k)=>/=.
              by rewrite mem_head.
          * by rewrite subrr normr0.
        + apply /bigmaxr_infP =>[[x y] _||]; first exact : normr_real.
          * apply /hasP. exists (k,k)=>//. apply /allpairsP. exists (k,k)=>/=.
              by rewrite mem_head.
          * exists (k,k); last by rewrite subrr normr0. apply /allpairsP.
            exists (k,k). by rewrite mem_head.
      - move : H (@lerr R 0%R) =>{1}<-. move /bigmaxr_supP => H.
        have : (le (norm (x - y)) 0%R).
        apply : (H _ _ (x,y))=>[[]|||]=>//;
                                      first (apply /hasP; exists (x,y)=>//);
          apply /allpairsP; by exists (x,y).
        by rewrite normr_le0 subr_eq0 =>/eqP.
    Qed.

    Lemma inner_prod_ex_inj_sublemma (a1 a2 b1 b2 M m:R):
      lt 0%R m -> (a1 != b1 -> le m (norm (a1 - b1))) ->
      lt (norm (a2 - b2)) M ->
      (M * a1 + m * a2 = M * b1 + m * b2)%R -> a1 = b1 /\ a2 = b2.
    Proof.
      case Heq : (a1 == b1);
      first by (rewrite ltr_def =>/andP [Hm _] _ _;
                 move /eqP : Heq =>-> /addrI /mulfI ->).
      move =>/= H0m Hm HM /eqP.
      rewrite -subr_eq -addrA addrC eq_sym -subr_eq -!mulrBr mulrC =>/eqP H.
      move : H (lerr (norm ((b1 - a1) * M)%R)) =>{2}->.
      move : (ler_trans (normr_ge0 _) (ltrW HM)) => H0M.
      rewrite !normrM (gtr0_norm H0m) (ger0_norm H0M) => H.
      move : (ler_trans H (ler_wpmul2r (normr_ge0 _) (Hm (erefl _)))).
      rewrite distrC ler_pmul2l; first by rewrite ltr_geF.
      rewrite normr_gt0. apply /negPf. by rewrite subr_eq0.
    Qed.
 
    Lemma inner_prod_ex_inj n (r:seq (regular_lmodType R ^ n)):
      exists w:R^n, {in r &, injective (inner_prod w)}.
    Proof.
      elim : n =>[|n IHn] in r *.
      - exists (empty_index _) => x y. by rewrite 2!eq_empty_index.
      - pose r' := [seq @index_projr _ 1 _ x|x <- r].
        case : (IHn r') => w' Hr'.
        exists (if (constant [seq @index_projl _ 1 _ x ord0 | x <- r])
                then (index_app [ffun : 'I_1 => 0%R] w')
                else (index_app
                        [ffun : 'I_1 =>
                         ((maxdist [seq inner_prod w' x | x <- r']) + 1)%R]
                        [ffun i =>
                         (mindist [seq @index_projl _ 1 _ x ord0 | x <- r]
                          * w' i)%R])).
        move => a b Ha Hb.
        case : ifP =>[|/mindist_eq0P /eqP Hmindist];
        rewrite -[a](@index_app_proj _ 1) -[b](@index_app_proj _ 1);
        rewrite !(@inner_prod_index_app _ _ 1) ?inner_prod_mull;
        rewrite ![inner_prod _ (index_projl _)]/inner_prod;
        rewrite !big_ord_recl !big_ord0 !ffunE /= !addr0 ?scale0r ?add0r.
        + move /constant_inP => Hconstant /Hr' ->; try exact /map_f.
          apply /ffunP => i. rewrite !ffunE /=. case : splitP =>//= j _.
          rewrite eq_ord0. apply : Hconstant; exact : map_f.
        + case /inner_prod_ex_inj_sublemma.
          * rewrite ltr_def Hmindist /=. exact : mindist_le0.
          * apply : mindist_inf; try apply /mapP.
            exists a =>//; by rewrite ffunE.
            exists b =>//; by rewrite ffunE.
            rewrite -[(norm _)]addr0. apply : ler_lt_add ltr01.
            apply : maxdist_sup; apply : map_f; exact : map_f.
          * move => Heql /Hr' ->; try exact : map_f.
            apply /ffunP => i. rewrite !ffunE /=. case : splitP =>//= j _.
              by rewrite eq_ord0 !ffunE.
    Qed.

  End numDomain.
End ssrnum.