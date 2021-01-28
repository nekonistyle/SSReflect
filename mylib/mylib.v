From mathcomp
     Require Import all_ssreflect.
Require Import Recdef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ***************************** *)
(* ssrfun *)
(* ***************************** *)
Section ssrfun.

  Variable (V S T U:Type).

  Section SopTisS.
    Implicit Type op : (V -> S) -> T -> V -> S.
    Definition right_idfun e op := forall x, op x e =1 x.
    Definition left_zerofun z op := forall x, op z x =1 z.
    Definition right_commutativefun op
      := forall x y z, op (op x y) z =1 op (op x z) y.
    Definition left_distributivefun op add :=
      forall x y z, op (add x y) z =1 add (op x z) (op y z).
  End SopTisS.
  
  Section SopTisT.
    Implicit Type op : S -> (V -> T) -> V -> T.
    Definition left_idfun e op := forall x, op e x =1 x.
    Definition right_zerofun z op := forall x, op x z =1 z.
    Definition left_commutativefun op
      := forall x y z, op x (op y z) =1 op y (op x z).
    Definition right_distributivefun op add :=
      forall x y z, op x (add y z) =1 add (op x y) (op x z).
  End SopTisT.

  Section SopSisT.
    Implicit Type op : (V -> S) -> (V -> S) -> U -> T.
    Definition self_inversefun e op := forall x, op x x =1 e.
    Definition commutativefun op := forall x y, op x y =1 op y x.
  End SopSisT.

  Section SopSisS.
    Implicit Type op : (V -> S) -> (V -> S) -> V -> S.
    Definition idempotentfun op := forall x, op x x =1 x.
    Definition associativefun op :=
      forall x y z, op x (op y z) =1 op (op x y) z.
    Definition interchangefun op1 op2 :=
      forall x y z t, op1 (op2 x y) (op2 z t) =1 op2 (op1 x z) (op1 y t).
  End SopSisS.

End ssrfun.

(* ***************************** *)
(* ssrbool *)
(* ***************************** *)
Section ssrbool.

  Section rel.

    Variable (T:Type).
    Variable (R:rel T).

    Definition strict x y := R x y && ~~ R y x.
    Definition equiv x y := R x y && R y x.
    Definition comparable x y := R x y || R y x.
    Definition incomp x y := ~~ R x y && ~~ R y x.

    Lemma subrel_strict : subrel strict R.
    Proof. move => x y. by case /andP. Qed.

    Lemma strict_irrefl : irreflexive strict.
    Proof. move => x. exact : andbN. Qed.

    Lemma strict_trans : transitive R -> transitive strict.
    Proof.
      move => Htrans y x z /andP [HRxy HnRyx] /andP [HRyz HnRyz]. apply /andP.
      split; first exact : Htrans HRyz.
      case HRzx : (R z x) =>//. by rewrite (Htrans _ _ _ HRzx HRxy) in HnRyz.
    Qed.

    Lemma subrel_equiv : subrel equiv R.
    Proof. move => x y. by case /andP. Qed.

    Lemma equiv_refl : reflexive R -> reflexive equiv.
    Proof. move => Hrefl x. rewrite /equiv. by move : (Hrefl x) =>->. Qed.

    Lemma equiv_symm : symmetric equiv.
    Proof. move => x y. exact : andbC. Qed.

    Lemma equiv_trans : transitive R -> transitive equiv.
    Proof.
      move => Htrans y x z /andP [HRxy HRyx] /andP [HRyz HRzy]. apply /andP.
      split. exact : Htrans HRyz. exact : Htrans HRyx.
    Qed.

    Lemma comparable_refl : reflexive R -> reflexive comparable.
    Proof. rewrite /comparable => H x. by rewrite H. Qed.

    Lemma comparable_symm : symmetric comparable.
    Proof. move => x y. exact : orbC. Qed.

    Lemma comparable_total : total R -> total comparable.
    Proof.
      rewrite /comparable => H x y. by case /orP : (H x y) =>->; rewrite ?orbT.
    Qed.

    Lemma incomp_symm : symmetric incomp.
    Proof. move => x y. exact : andbC. Qed.

    Lemma comparable_incomp x y : comparable x y = ~~ incomp x y.
    Proof. by rewrite /incomp -negb_or negbK. Qed.

    Lemma rel_strict_trans :
      transitive R -> forall y x z, R x y -> strict y z -> strict x z.
    Proof.
      rewrite /strict. move => Htrans y x z Hxy /andP[Hyz Hnzy].
      rewrite (Htrans _ _ _ Hxy Hyz) /=. case Hzx : (R z x) Hnzy =>//.
        by rewrite (Htrans _ _ _ Hzx Hxy).
    Qed.

    Lemma strict_rel_trans :
      transitive R -> forall y x z, strict x y -> R y z -> strict x z.
    Proof.
      rewrite /strict. move => Htrans y x z /andP[Hxy Hnyx] Hyz.
      rewrite (Htrans _ _ _ Hxy Hyz) /=. case Hzx : (R z x) Hnyx =>//.
        by rewrite (Htrans _ _ _ Hyz Hzx).
    Qed.

    Lemma equiv_rell : transitive R -> forall x y z, equiv x y -> R x z = R y z.
    Proof.
      move => Htrans x y z. case /andP => Hxy Hyx.
      case Hyz : (R y z); first exact : Htrans Hyz.
      case Hxz : (R x z)=>//. by rewrite (Htrans _ _ _ Hyx Hxz) in Hyz.
    Qed.

    Lemma equiv_relr : transitive R -> forall x y z, equiv x y -> R z x = R z y.
    Proof.
      move => Htrans x y z. case /andP => Hxy Hyx.
      case Hzy : (R z y); first exact : Htrans Hyx.
      case Hzx : (R z x)=>//. by rewrite (Htrans _ _ _ Hzx Hxy) in Hzy.
    Qed.

    Lemma equiv_strictl :
      transitive R -> forall x y z, equiv x y -> strict x z = strict y z.
    Proof.
      move => Htrans x y z Hxy.
        by rewrite /strict (equiv_rell Htrans _ Hxy) (equiv_relr Htrans _ Hxy).
    Qed.

    Lemma equiv_strictr :
      transitive R -> forall x y z, equiv x y -> strict z x = strict z y.
    Proof.
      move => Htrans x y z Hxy.
        by rewrite /strict (equiv_rell Htrans _ Hxy) (equiv_relr Htrans _ Hxy).
    Qed.

    Lemma rel_strict_equiv x y : R x y = strict x y || equiv x y.
    Proof. by rewrite /strict /equiv -andb_orr orNb andbT. Qed.

    Lemma relNRstrict x y : R x y -> ~~ strict y x.
    Proof. move => HRxy. by rewrite /strict negb_and HRxy orbT. Qed.

    Lemma strictNRrel x y : strict x y -> ~~ R y x.
    Proof. by case /andP. Qed.

    Lemma strictNRstrict x y : strict x y -> ~~ strict y x.
    Proof. move /subrel_strict. exact : relNRstrict. Qed.

    Lemma strictNequiv x y : strict x y -> ~~ equiv x y.
    Proof. case /andP => HRxy HnRyx. by rewrite /equiv negb_and HnRyx orbT. Qed.

    Lemma equivNstrict x y : equiv x y -> ~~ strict x y.
    Proof. case /andP => HRxy HRyx. by rewrite /strict negb_and HRyx orbT. Qed.

    CoInductive compare_rel x y :
      bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
    | CompareRelLt of strict x y :
        compare_rel x y true false true true true false false false false false
    | CompareRelGt of strict y x :
        compare_rel x y false true true true false true false false false false
    | CompareRelEq of equiv x y :
        compare_rel x y true true true true false false true true false false
    | CompareRelIC of incomp x y :
        compare_rel x y false false false false false false false false true true.

    Lemma relP x y :
      compare_rel x y (R x y) (R y x) (comparable x y) (comparable y x)
                  (strict x y) (strict y x) (equiv x y) (equiv y x)
                  (incomp x y) (incomp y x).
    Proof.
      rewrite /comparable /strict /equiv /incomp.
      case Hxy : (R x y); case Hyx : (R y x) =>/=.
      - constructor. by rewrite /equiv Hxy Hyx.
      - constructor. by rewrite /strict Hxy Hyx.
      - constructor. by rewrite /strict Hxy Hyx.
      - constructor. by rewrite /incomp Hxy Hyx.
    Qed.

    Lemma antisymmP x y :
      reflexive R -> antisymmetric R -> reflect (x = y) (equiv x y).
    Proof.
      move => Hrefl Hanti. apply /(iffP idP) =>[|->]; first exact : Hanti.
      exact : equiv_refl.
    Qed.

    Hypothesis (Htotal : total R).

    Lemma total_rel_strict x y : R x y || strict y x.
    Proof.
      case /orP : (Htotal x y); first by move =>->. rewrite /strict =>->.
      exact : orbN.
    Qed.

    Lemma total_Nincomp x y : ~~ incomp x y.
    Proof.
      case /orP : (Htotal x y); rewrite /incomp =>->//=. by rewrite andbF.
    Qed.

    Lemma total_strict_equiv x y : [|| strict x y , equiv x y | strict y x].
    Proof. by rewrite orbA -rel_strict_equiv total_rel_strict. Qed.

    CoInductive compare_total x y :
      bool -> bool -> bool -> bool -> bool -> bool -> Set :=
    | CompareTotalLt of strict x y :
        compare_total x y true false true false false false
    | CompareTotalGt of strict y x :
        compare_total x y false true false true false false
    | CompareTotalEq of equiv x y :
        compare_total x y true true false false true true.

    Lemma totalP x y :
      compare_total x y (R x y) (R y x) (strict x y) (strict y x)
                    (equiv x y) (equiv y x).
    Proof.
      case : relP; try constructor =>//.
      - by rewrite equiv_symm.
      - by move /negbTE : (total_Nincomp y x) =>->.
    Qed.

  End rel.
  Section argrel.
    Variable (S T:Type).
    Variable (f:S -> T).
    Variable (R:rel T).

    Definition argrel : rel S := fun x y => R (f x) (f y).

    Lemma argrel_refl : reflexive R -> reflexive argrel.
    Proof. move => H x. exact : H. Qed.

    Lemma argrel_symm : symmetric R -> symmetric argrel.
    Proof. move => H x y. exact : H. Qed.

    Lemma argrel_trans : transitive R -> transitive argrel.
    Proof. move => H y x z. exact : H. Qed.

    Lemma argrel_total : total R -> total argrel.
    Proof. move => H x y. exact : H. Qed.

    Lemma argrel_anti : injective f -> antisymmetric R -> antisymmetric argrel.
    Proof. by move => Hf H x y /H /Hf. Qed.

  End argrel.

  Section argrel_lemma.
    Variable (S T:Type).
    Variable (f:S -> T).
    Variable (R:rel T).

    Lemma strict_argrel : strict (argrel f R) =2 argrel f (strict R).
    Proof. done. Qed.

    Lemma equiv_argrel : equiv (argrel f R) =2 argrel f (equiv R).
    Proof. done. Qed.

    Lemma comparable_argrel :
      comparable (argrel f R) =2 argrel f (comparable R).
    Proof. done. Qed.

    Lemma incomp_argrel : incomp (argrel f R) =2 argrel f (incomp R).
    Proof. done. Qed.

  End argrel_lemma.
  
  Section lexicsum.
    Variable (T S:Type).
    Variable (R:rel T).
    Variable (Q:rel S).

    Definition lexicsum : rel (T + S) :=
      fun x y => match x, y with
                 | inl a, inl b => R a b
                 | inl _, inr _ => true
                 | inr _, inl _ => false
                 | inr a, inr b => Q a b
                 end.

    Lemma lexicsum_refl : reflexive R -> reflexive Q -> reflexive lexicsum.
    Proof. move => HR HQ [x|x]. exact : HR. exact : HQ. Qed.

    Lemma lexicsum_trans : transitive R -> transitive Q -> transitive lexicsum.
    Proof. move => HR HQ [y|y] [x|x] [z|z]//. exact : HR. exact : HQ. Qed.

    Lemma lexicsum_total : total R -> total Q -> total lexicsum.
    Proof. move => HR HQ [x|x] [y|y]//. exact : HR. exact : HQ. Qed.

    Lemma lexicsum_anti :
      antisymmetric R -> antisymmetric Q -> antisymmetric lexicsum.
    Proof. move => HR HQ [x|x] [y|y]//. by move /HR ->. by move /HQ ->. Qed.

  End lexicsum.

  Section lexicsum_lemma.
    Variable (T S:Type).
    Variable (R:rel T).
    Variable (Q:rel S).

    Lemma strict_lexicsum :
      strict (lexicsum R Q) =2 lexicsum (strict R) (strict Q).
    Proof. by move => [x|x] [y|y]. Qed.

  End lexicsum_lemma.

  Section lexicographic.
    Variable (T S:Type).
    Variable (R:rel T).
    Variable (Q:rel S).

    Definition lexicographic : rel (T * S) :=
      fun x y => strict R x.1 y.1 || equiv R x.1 y.1 && Q x.2 y.2.

    Lemma lexicgraphic_refl :
      reflexive R -> reflexive Q -> reflexive lexicographic.
    Proof.
      rewrite /lexicographic => /equiv_refl HR HQ x.
        by rewrite HR HQ orbT.
    Qed.

    Lemma lexicographic_trans :
      transitive R -> transitive Q -> transitive lexicographic.
    Proof.
      rewrite /lexicographic
      => HR HQ y x z
            /orP [HRxy|/andP[HRxy HQxy]] /orP [HRyz|/andP[HRyz HQyz]].
      - by rewrite (strict_trans HR HRxy HRyz).
      - by rewrite -(equiv_strictr HR _ HRyz) HRxy.
      - by rewrite (equiv_strictl HR _ HRxy) HRyz.
      - by rewrite (equiv_trans HR HRxy HRyz) (HQ _ _ _ HQxy HQyz) orbT.
    Qed.

    Lemma lexicoghraphic_total : total R -> total Q -> total lexicographic.
    Proof.
      rewrite /lexicographic => HR HQ x y. by case /totalP : HR =>//=. 
    Qed.

    Lemma lexicographic_anti :
      antisymmetric R -> antisymmetric Q -> antisymmetric lexicographic.
    Proof.
      rewrite /lexicographic => HR HQ [x1 x2] [y1 y2].
        by case : relP =>//= /HR -> /HQ ->.
    Qed.

  End lexicographic.

  Section lexicographic_lemma.
    Variable (T S:Type).
    Variable (R:rel T).
    Variable (Q:rel S).

    Lemma strict_lexicographic :
      strict (lexicographic R Q) =2 lexicographic R (strict Q).
    Proof. rewrite /lexicographic /strict => x y. by case : relP. Qed.

  End lexicographic_lemma.

  Lemma predTI T (A:pred T) : [predI predT & A] =1 A.
  Proof. move => x. exact : andTb. Qed.

  Lemma predFI T (A:pred T) : [predI pred0 & A] =1 pred0.
  Proof. move => x. exact : andFb. Qed.

  Lemma predIT T (A:pred T) : [predI A & predT] =1 A.
  Proof. move => x. exact : andbT. Qed.

  Lemma predIF T (A:pred T) : [predI A & pred0] =1 pred0.
  Proof. move => x. exact : andbF. Qed.

  Lemma predII T (A:pred T) : [predI A & A] =1 A.
  Proof. move => x. exact : andbb. Qed.

  Lemma predIC T (A B:pred T) :
    [predI A & B] =1 [predI B & A].
  Proof. move => x. exact : andbC. Qed.

  Lemma predIA T (A B C:pred T) :
    [predI A & [predI B & C]] =1 [predI [predI A & B] & C].
  Proof. move => x. exact : andbA. Qed.

  Lemma predICA T (A B C:pred T) :
    [predI A & [predI B & C]] =1 [predI B & [predI A & C]].
  Proof. move => x. exact : andbCA. Qed.

  Lemma predIAC T (A B C:pred T) :
    [predI [predI A & B] & C] =1 [predI [predI A & C] & B].
  Proof. move => x. exact : andbAC. Qed.

  Lemma predIACA T (A B C D:pred T) :
    [predI [predI A & B] & [predI C & D]]
    =1 [predI [predI A & C] & [predI B & D]].
  Proof. move => x. exact : andbACA. Qed.

  Lemma predTU T (A:pred T) : [predU predT & A] =1 predT.
  Proof. move => x. exact : orTb. Qed.

  Lemma predFU T (A:pred T) : [predU pred0 & A] =1 A.
  Proof. move => x. exact : orFb. Qed.

  Lemma predUT T (A:pred T) : [predU A & predT] =1 predT.
  Proof. move => x. exact : orbT. Qed.

  Lemma predUF T (A:pred T) : [predU A & pred0] =1 A.
  Proof. move => x. exact : orbF. Qed.

  Lemma predUU T (A:pred T) : [predU A & A] =1 A.
  Proof. move => x. exact : orbb. Qed.

  Lemma predUC T (A B:pred T) :
    [predU A & B] =1 [predU B & A].
  Proof. move => x. exact : orbC. Qed.

  Lemma predUA T (A B C:pred T) :
    [predU A & [predU B & C]] =1 [predU [predU A & B] & C].
  Proof. move => x. exact : orbA. Qed.

  Lemma predUCA T (A B C:pred T) :
    [predU A & [predU B & C]] =1 [predU B & [predU A & C]].
  Proof. move => x. exact : orbCA. Qed.

  Lemma predUAC T (A B C:pred T) :
    [predU [predU A & B] & C] =1 [predU [predU A & C] & B].
  Proof. move => x. exact : orbAC. Qed.

  Lemma predUACA T (A B C D:pred T) :
    [predU [predU A & B] & [predU C & D]]
    =1 [predU [predU A & C] & [predU B & D]].
  Proof. move => x. exact : orbACA. Qed.

  Lemma predIUl T (A B C:pred T) :
    [predI [predU A & B] & C] =1 [predU [predI A & C] & [predI B & C]].
  Proof. move => x. exact : andb_orl. Qed.

  Lemma predIUr T (A B C:pred T) :
    [predI A & [predU B & C]] =1 [predU [predI A & B] & [predI A & C]].
  Proof. move => x. exact : andb_orr. Qed.

  Lemma predUIl T (A B C:pred T) :
    [predU [predI A & B] & C] =1 [predI [predU A & C] & [predU B & C]].
  Proof. move => x. exact : orb_andl. Qed.

  Lemma predUIr T (A B C:pred T) :
    [predU A & [predI B & C]] =1 [predI [predU A & B] & [predU A & C]].
  Proof. move => x. exact : orb_andr. Qed.

End ssrbool.

(* ***************************** *)
(* ssrnat *)
(* ***************************** *)
Section ssrnat.

  Lemma pred_leq m n : m <= n -> m.-1 <= n.-1.
  Proof. by case : m n =>[|m][|n]. Qed.

  Lemma ltn_subLR m n p : 0 < p -> (m - n < p) = (m < n + p).
  Proof. case : p =>// p _. rewrite addnS !ltnS. exact : leq_subLR. Qed.

  Lemma leqb (b1 b2:bool) : b1 <= b2 = b1 ==> b2.
  Proof. by move : b1 b2 =>[][]. Qed.

End ssrnat.

(* ***************************** *)
(* seq *)
(* ***************************** *)
Section seq.
  Section normal.
    Variable (T:Type).

    Lemma head_filter p x0 (s:seq T) : has p s -> p (head x0 (filter p s)).
    Proof. elim : s =>[|a s IHs]//=. by case : ifP. Qed.

    Lemma filter_size p (s:seq T) : size (filter p s) <= size s.
    Proof. by rewrite size_filter count_size. Qed.

    Lemma filter_nilP p (s:seq T) :
      reflect (filter p s = [::]) (all (xpredC p) s).
    Proof.
      apply /(iffP idP).
      - by elim : s =>[|x s IHs]//= /andP [] /negbTE ->.
      - elim : s =>[|x s IHs]//=. by case : ifP.
    Qed.

    Lemma all_filter p (s:seq T) : all p s -> forall q, all p (filter q s).
    Proof.
      elim : s =>[|x s IHs]//= /andP [px /IHs IH] q.
      case : ifP=>//=_. by rewrite px IH.
    Qed.

    Lemma iotanS m n : iota m n.+1 = rcons (iota m n) (m + n).
    Proof. by rewrite -addn1 iota_add cats1. Qed.

  End normal.
  Section eqType.
    Variable (T:eqType).
    Implicit Types (x:T).

    Lemma in_inj_inv (S:eqType) (x0:T) (s:seq T) (f:T -> S) :
      {in s &, injective f} -> exists (g:S -> T), {in s, cancel f g}.
    Proof.
      move => Hinj.
      exists (fun y => (head x0 (filter (fun x => f x == y) s))) => x.
      elim : s =>[|a s IHs] in Hinj *=>//=. rewrite in_cons.
      case /orP =>[/eqP->|Hx]; first by rewrite eq_refl.
      case : ifP =>[/eqP /Hinj|_].
      - rewrite mem_head in_cons Hx orbT. exact.
      - apply : IHs Hx => y z Hy Hz.
        apply : Hinj; by rewrite in_cons ?Hy ?Hz orbT.
    Qed.

    Lemma constant_inP (s:seq T) :
      reflect {in s &, forall x y, x = y} (constant s).
    Proof.
      apply /(iffP idP).
      - case : s =>[|x s]//= /allP H a b. rewrite !in_cons.
          by case /orP =>[|/H]/eqP->; case /orP =>[|/H]/eqP->.
      - case : s =>[|x s]//= H. apply /allP => y Hy.
        rewrite (H _ y (mem_head _ _))=>//=. by rewrite in_cons Hy orbT.
    Qed.

    Lemma head_rot_index x0 x s: x \in s -> head x0 (rot (index x s) s) = x.
    Proof.
      elim : s =>[|y s IHs]//=. rewrite in_cons.
      case /orP; first by (move /eqP =>->; rewrite eq_refl rot0).
      case : ifP =>[|_ Hin]; first by (move /eqP =>->; rewrite rot0).
      rewrite rotS; last exact : index_size. rewrite rot_rot rot1_cons -cats1.
      move : (IHs Hin). rewrite -index_mem in Hin.
        by rewrite /rot drop_cat (Hin) (drop_nth x0).
    Qed.

    Lemma mem_rem (X:eqType) (x y:X) s : y <> x -> y \in s -> y \in rem x s.
    Proof.
      move => Hyx. elim : s =>[|z s IHs]//=. rewrite in_cons.
      case : (y =P z) =>[<-|] _/=.
      - case : (y =P x)=>//. by rewrite mem_head.
      - case : ifP =>// _ /IHs Hy. by rewrite in_cons Hy orbT.
    Qed.

    Lemma notin_rem (X:eqType) (x:X) s : uniq s -> x \notin rem x s.
    Proof.
      elim : s =>[|y s IHs]//= /andP[]. case : ifP; first by move /eqP =>->.
        by rewrite eq_sym in_cons =>->.
    Qed.

    Lemma uniq_all_equal_to (x0:T) :
      all_equal_to x0 -> forall s, uniq s -> s = [::] \/ s = [:: x0].
    Proof.
      move => H [|x [|y s]/=]; first (by left); rewrite H; first by right.
        by rewrite H mem_head.
    Qed.

    Lemma undup_subseq (s:seq T) : subseq (undup s) s.
    Proof.
      elim : s =>[|x s IHs]//=. case : ifP; last by rewrite eq_refl.
      case : (undup s) => [|b s']in IHs *=>//_. case : ifP=>//_.
      exact : subseq_trans (subseq_cons _ _) IHs.
    Qed.

    Lemma undup_id (s:seq T) : undup (undup s) = undup s.
    Proof.
      elim : s =>[|x s IHs]//=. case : ifP =>//=. by rewrite IHs mem_undup =>->.
    Qed.

    Lemma perm_cat (s1 s2 s1' s2':seq T) :
      perm_eq s1 s2 -> perm_eq s1' s2' -> perm_eq (s1 ++ s1') (s2 ++ s2').
    Proof.
      move => H12 H12'.
      apply : (@perm_trans _ (s1 ++ s2')); first by rewrite perm_cat2l.
        by rewrite perm_cat2r.
    Qed.

  End eqType.
End seq.

(* ***************************** *)
(* div *)
(* ***************************** *)
Section div.

  Lemma modn_eqP p x y:
    reflect (exists n m, n * p + x = m * p + y) (x == y %[mod p]).
  Proof.
    apply /(iffP idP) =>[/eqP H|[n] [m] /(congr1 (fun n => n %% p))];
                          last by rewrite !modnMDl =>/eqP.
    exists (y %/ p), (x %/ p).
      by rewrite {1}(divn_eq x p) {2}(divn_eq y p) addnCA H.
  Qed.

End div.

(* ***************************** *)
(* path *)
(* ***************************** *)
Section path.
  Section mysort.
    Variable (T:Type).
    Variable (R:rel T).

    Fixpoint mysorted (s:seq T) :=
      if s is x :: s' then all (fun y => ~~ R y x || R x y) s' && mysorted s'
      else true.

    Lemma mysorted_rcons s y :
      mysorted (rcons s y) = mysorted s && all (fun x => ~~ R y x || R x y) s.
    Proof.
      elim : s =>[|x s IHs]//=. rewrite IHs all_rcons !andbA.
      congr(_ && _). by rewrite -!andbA andbC andbA.
    Qed.

    Lemma mysorted_cat s1 s2 :
      mysorted s1 -> mysorted s2 ->
      all (fun x => all (fun y => ~~ R y x || R x y) s2) s1 ->
      mysorted (s1 ++ s2).
    Proof.
      elim : s1 =>[|x s1 IHs1]//=.
      rewrite all_cat => /andP [->] Hs1 Hs2 /andP [->]/=. exact : IHs1.
    Qed.

    Lemma mysorted_filter (s:seq T) P:
      mysorted s -> mysorted (filter P s).
    Proof.
      elim : s =>[|x s IHs]//=. case : ifP =>_/andP [] H //= /IHs ->{IHs}.
      rewrite andbT. elim : s H =>[|y s IHs]//= /andP [].
        by case : ifP =>//=_->.
    Qed.

    Fixpoint myTsorted (s:seq T) :=
      if s is x :: s' then all (R x) s' && myTsorted s'
      else true.

    Lemma myTsorted_rcons s y :
      myTsorted (rcons s y) = myTsorted s && all (fun x => R x y) s.
    Proof.
      elim : s =>[|x s IHs]//=. rewrite IHs all_rcons !andbA.
      congr(_ && _). by rewrite -!andbA andbC andbA.
    Qed.

    Lemma mysorted_Tsorted (s:seq T) :
      total R -> mysorted s = myTsorted s.
    Proof.
      move => HR. elim : s =>[|x s /=->]//=. congr(_ && _).
      apply : eq_all => y. case /orP : (HR x y) =>->; by rewrite ?orbT.
    Qed.

    Function qsort (s:seq T) {measure size s} :=
      if s is x :: s'
      then qsort [seq y <- s' | R y x] ++ x :: qsort [seq y <- s' | ~~ R y x]
      else [::].
    Proof.
      - move => _ x s _/=. apply /ltP. by rewrite ltnS size_filter count_size.
      - move => _ x s _/=. apply /ltP. by rewrite ltnS size_filter count_size.
    Defined.

    Lemma my_qsort_ind (P:seq T -> Prop) :
      P [::] ->
      (forall x s, P [seq y <- s | R y x] ->
                   P [seq y <- s | ~~ R y x] -> P (x :: s)) ->
      forall s, P s.
    Proof.
      move => Hnil Hcons s.
      elim : s {-2}s (leqnn (size s)) =>[|xs s IHs][]//= yl l Hsize.
        by apply : Hcons; exact : IHs (leq_trans (filter_size _ _) Hsize).
(*
      elim : (size s) {-2}s (leqnn (size s)) =>[|n IHn][]//= x t Hsize.
        by apply : Hcons; exact : IHn (leq_trans (filter_size _ _) Hsize).
 *)
    Qed.

    Lemma size_qsort s : size (qsort s) = size s.
    Proof.
      elim /my_qsort_ind : s =>[|x s]//=.
      rewrite [qsort (_ :: _)]qsort_equation size_cat /==>->->.
        by rewrite addnS !size_filter count_predC.
    Qed.

    Lemma all_qsort p s : all p (qsort s) = all p s.
    Proof.
      elim /my_qsort_ind : s =>[|x s]//=.
      rewrite [qsort (_ :: _)]qsort_equation all_cat /==>->->.
      case : (p x) =>/=; last exact : andbF. elim : s =>[|y s]//=.
      case : ifP =>_/=<-; case : (p y)=>//=. exact : andbF.
    Qed.

    Lemma qsort_rcons_min s x:
      all (R x) s -> qsort (rcons s x) = x :: qsort s.
    Proof.
      elim /my_qsort_ind : s =>[|y s IHsl IHsr]// /andP [].
      rewrite ![qsort (_ :: _)]qsort_equation !filter_rcons =>->/= Hx.
        by rewrite (IHsl (all_filter Hx _)).
    Qed.

    Lemma qsort_rcons_max s x:
      all (fun y => ~~ R x y) s -> qsort (rcons s x) = rcons (qsort s) x.
    Proof.
      elim /my_qsort_ind : s =>[|y s IHsl IHsr]// /andP [].
      rewrite ![qsort (_ :: _)]qsort_equation !filter_rcons.
      case : ifP =>//_ _ Hx. by rewrite (IHsr (all_filter Hx _)) rcons_cat.
    Qed.

    Lemma qsort_cat s1 s2:
      all (fun x => all (fun y => ~~ R y x) s2) s1 ->
      qsort (s1 ++ s2) = qsort s1 ++ qsort s2.
    Proof.
      elim /my_qsort_ind : s1 =>[|x s1 IHs1l IHs1r]// /andP [] Hx Hs1 /=.
      rewrite ![qsort (_ :: _)]qsort_equation /= !filter_cat.
      move /filter_nilP : (Hx) =>->. rewrite cats0.
      move /all_filterP : Hx =>->. by rewrite -catA (IHs1r (all_filter Hs1 _)).
    Qed.

    Hypothesis (Htrans:transitive R).

    Lemma qsort_sorted s : mysorted (qsort s).
    Proof.
      elim /my_qsort_ind : s =>[|x s IHs1 IHs2]//.
      rewrite qsort_equation. apply : mysorted_cat =>//=.
      - rewrite IHs2 andbT all_qsort.
          by apply : (sub_all _ (filter_all _ _)) => y ->.
      - rewrite all_qsort.
        apply : (sub_all _ (filter_all _ _)) => y Hyx.
        rewrite Hyx orbT all_qsort /=.
        apply : (sub_all _ (filter_all _ _)) => z.
        case Hzy : (R z y)=>//. by rewrite (Htrans Hzy Hyx).
    Qed.

    Hypothesis (Htotal:total R).

    Lemma qsort_Tsorted s: myTsorted (qsort s).
    Proof. rewrite -(mysorted_Tsorted _ Htotal). exact : qsort_sorted. Qed.

  End mysort.

  Section sorted.
    Variable (T:Type).
    Variable (R:rel T).

    Lemma mysorted_map (T':Type) (R':rel T') (f:T -> T') s:
      {mono f : x y / R x y >-> R' x y} ->
      mysorted R s -> mysorted R' (map f s).
    Proof.
      move => H. elim : s =>[|x s IHs]//= /andP[Hx /IHs ->].
      rewrite all_map andbT. apply : sub_all Hx => y /=. by rewrite !H.
    Qed.

    Lemma myTsorted_map (T':Type) (R':rel T') (f:T -> T') s:
      {homo f : x y / R x y >-> R' x y} ->
      myTsorted R s -> myTsorted R' (map f s).
    Proof.
      move => H. elim : s =>[|x s IHs]//= /andP[Hx /IHs ->].
      rewrite all_map andbT. apply : sub_all Hx. exact : H.
    Qed.

    Lemma rev_mysorted s :
      mysorted R (rev s) = mysorted (fun x y => R y x) s.
    Proof.
      elim /last_ind : s =>[|s x IHs]//.
        by rewrite rev_rcons mysorted_rcons /= all_rev IHs andbC.
    Qed.

    Lemma rev_myTsorted s :
      myTsorted R (rev s) = myTsorted (fun x y => R y x) s.
    Proof.
      elim /last_ind : s =>[|s x IHs]//.
        by rewrite rev_rcons myTsorted_rcons /= all_rev IHs andbC.
    Qed.

  End sorted.

  Section eqType.
    Variable (T:eqType).
    Variable (R:rel T).

    Lemma perm_qsort s: perm_eq (qsort R s) s.
    Proof.
      elim /(@my_qsort_ind _ R) : s =>[|x s IHs1 IHs2]//.
      rewrite qsort_equation perm_catC /= perm_cons perm_sym
             -(perm_filterC (R^~ x)) perm_catC perm_sym. exact : perm_cat.
    Qed.

    Definition uniq_qsort s:
      uniq (qsort R s) = uniq s := perm_uniq (perm_qsort s).

    Lemma mysorted_subseq s1 s2:
      subseq s1 s2 -> mysorted R s2 -> mysorted R s1.
    Proof.
      elim : s2 =>[|x2 s2 IHs2]//= in s1 *; first by move /eqP =>->.
      case : s1 =>[|x1 s1]//=.
      case : ifP =>[/eqP->|_] Hs12 /andP [/allP Hx] /(IHs2 _ Hs12)//->.
      rewrite andbT. apply /allP => y /(mem_subseq Hs12). exact : Hx.
    Qed.

    Lemma myTsorted_subseq s1 s2:
      subseq s1 s2 -> myTsorted R s2 -> myTsorted R s1.
    Proof.
      elim : s2 =>[|x2 s2 IHs2]//= in s1 *; first by move /eqP =>->.
      case : s1 =>[|x1 s1]//=.
      case : ifP =>[/eqP->|_] Hs12 /andP [/allP Hx] /(IHs2 _ Hs12)//->.
      rewrite andbT. apply /allP => y /(mem_subseq Hs12). exact : Hx.
    Qed.

    Lemma myTsorted_sorted s: myTsorted R s -> sorted R s.
    Proof.
      elim : s =>[|x s IHs]//= /andP [/allP H]. rewrite path_min_sorted //.
      exact /allP.
    Qed.

    Lemma mysorted_sorted s: total R -> mysorted R s -> sorted R s.
    Proof.
      by move => /mysorted_Tsorted -> /myTsorted_sorted.
    Qed.

    Lemma sorted_mysorted s: transitive R -> sorted R s -> mysorted R s.
    Proof.
      move => Htrans. elim : s =>[|x s IHs]//= Hpath.
      move /path_sorted /IHs : Hpath (Hpath) =>->{IHs}. rewrite andbT.
      elim : s =>[|y s IHs] =>//= /andP [Hxy Hpath].
      rewrite Hxy orbT IHs =>//{IHs}.
        by case : s Hpath =>[|z s]//= /andP [] /(Htrans _ _ _ Hxy)->->.
    Qed.

    Lemma sorted_myTsorted s: transitive R -> sorted R s = myTsorted R s.
    Proof.
      move => Htrans. case H : (myTsorted R s); first exact : myTsorted_sorted.
      case H': (sorted R s) =>//. rewrite -H {H}. apply : esym. move : H'.
      elim : s =>[|x s IHs]//= Hpath. rewrite andbC (IHs (path_sorted Hpath))/=.
      move : Hpath {IHs}. case : s =>[|y s]//=/andP [Hxy]. rewrite Hxy /=.
      elim : s =>[|z s IHs]//= in y Hxy *=> /andP [] /(Htrans _ _ _ Hxy) => Hxz.
        by rewrite Hxz =>/(IHs _ Hxz)->.
    Qed.

    Lemma mysorted_count_le s x:
      transitive R -> total R -> mysorted R s ->
      count (R^~ x) s = find (fun y => ~~ R y x) s.
    Proof.
      move => Htrans Htotal. elim : s =>[|y s IHs]//= /andP [].
      case Hyx : (R y x) (Htotal x y); first by move =>_ _/IHs->.
      rewrite orbF add0n =>/= Hxy.
      elim : s {IHs} =>[|z s IHs]//= /andP [Hyz Hy] /andP [Hz /(IHs Hy)->].
      case Hzx : (R z x) =>//.
      move /orP : Hyz (Htotal y z) Hyx =>[/negbTE->|];
        first rewrite orbF; move => Hyz; by rewrite (Htrans _ _ _ Hyz Hzx).
    Qed.

    Lemma count_le s x:
      transitive R -> total R ->
      count (R^~ x) s = find (fun y => ~~ R y x) (qsort R s).
    Proof.
      move => Htrans Htotal.
      rewrite -(mysorted_count_le _ Htrans Htotal (qsort_sorted Htrans _)).
      symmetry. apply /permP. exact : perm_qsort.
    Qed.

    Implicit Types (x:T).

    Lemma next_nil x: next [::] x = x.
    Proof. done. Qed.

    Lemma next_head x s: next (x :: s) x = head x s.
    Proof. by case : s =>[|y s]//=; rewrite eq_refl. Qed.

    Lemma next_cons x y s:
      next (y :: s) x =
      if x == y
      then head x s
      else if x \in s
           then if (index x s).+1 < size s then next s x else y
           else x.
    Proof.
      case : ifP; first by (move /eqP =>->; exact : next_head). 
      rewrite !next_nth in_cons /= [y == _]eq_sym =>->/=.
      case : ifP =>//. case : s =>[|z s]//.
      case : ifP =>/=; (case : ifP =>_; last rewrite ltnS => Hlt _).
      - by rewrite !nth0; case : s.
      - exact : set_nth_default.
      - by case : s.
      - apply : nth_default. by rewrite leqNgt Hlt.
    Qed.

    Lemma next_default x s: x \notin s -> next s x = x.
    Proof.
      case : s =>[|y s]//. rewrite next_cons in_cons negb_or.
      case /andP. move /negbTE =>->. by move /negbTE =>->.
    Qed.

    Lemma next_last x s:
      x \in s -> (index x s).+1 < size s = false -> next s x = head x s.
    Proof.  
      case : s=>[|y s]//. rewrite next_cons in_cons /=.
      case : ifP; first move /eqP =>->_; rewrite ltnS.
      - rewrite eq_refl. by case : s.
      - by rewrite eq_sym =>->/=->->.
    Qed.

    Lemma next_cat x s1 s2:
      next (s1 ++ s2) x =
      if x \in s1
      then if (index x s1).+1 < size s1
           then next s1 x else head (head x s1) s2
      else if x \in s2
           then if (index x s2).+1 < size s2
                then next s2 x else head (head x s2) s1
           else x.
    Proof.
      case : ifP.
      - elim : s1 =>[|y s1 IHs1]//. rewrite cat_cons !next_cons in_cons.
        case : ifP =>/=;
                   first by (move /eqP =>->; rewrite eq_refl {IHs1}; case : s1).
        rewrite eq_sym ltnS index_cat size_cat mem_cat =>-> Hin.
        rewrite (IHs1 Hin) Hin {IHs1} addnC =>/=.
        case Hlt : ((index x s1).+1 < size s1).
        + rewrite (leq_trans Hlt)=>//. exact : leq_addl.
        + rewrite -index_mem in Hin.
          case : s2 =>[|z s2]/=; first by rewrite Hlt.
          rewrite addSn ltnS. rewrite (leq_trans Hin)=>//. exact : leq_addl.
      - elim : s1 =>[_/=|y s1 IHs1].
        + case : ifP; last by (move /negbT; exact : next_default).
          case : ifP =>// Hlt Hin. exact : next_last.
        + rewrite in_cons cat_cons next_cons index_cat size_cat mem_cat.        
          move /negbT. rewrite negb_or. case /andP. move /negbTE =>->.
          move /negbTE => Hin.
          rewrite (IHs1 Hin) Hin {IHs1} -addnS ltn_add2l /=.
          case : ifP =>//->. by case : ifP=>//->.
    Qed.

    Lemma next_rcons x s:
      uniq s -> x \notin s -> next (rcons s x) x = head x s.
    Proof.
      move => Huniq Hnotin.
      rewrite -rot1_cons next_rot /=; first exact : next_head.
        by rewrite Huniq Hnotin.
    Qed.

    Lemma index_next s x:
      uniq s -> x \in s ->
                      index (next s x) s = if (index x s).+1 < size s
                                           then (index x s).+1
                                           else 0.
    Proof.
      elim : s =>[|y s IHs]//. rewrite next_cons in_cons /=. case /andP.
      case Hy : (x == y); first (move /eqP : Hy =>->; rewrite eq_refl).
      - case : s {IHs} =>[|z s]/=; rewrite eq_refl //.
        rewrite in_cons negb_or. case /andP. by move /negbTE =>->.
      - move : Hy. rewrite eq_sym ltnS =>->/= Hnotin Huniq Hin. rewrite (Hin).
        case Hlt : ((index x s).+1 < size s); last by rewrite eq_refl.
        rewrite (IHs Huniq Hin) Hlt. case : ifP Hnotin =>//. move /eqP =>->.
          by rewrite mem_next Hin.
    Qed.
  End eqType.
End path.

(* ***************************** *)
(* choice *)
(* ***************************** *)
Section choice.
  Variable (T:eqType).

  Lemma AllSeq_pcancel (s:seq T) :
    (forall x, x \in s) ->
    pcancel (index^~ s)
            (fun n => if n < size s then nth None (map (@Some _) s) n
                      else None).
  Proof.
    move => HAll x.
    rewrite index_mem HAll -(index_map (@Some_inj _)) nth_index //.
      by rewrite (mem_map (@Some_inj _)) HAll.
  Qed.

  Definition AllSeq_choiceMixin (s:seq T) (H:forall x, x \in s)
    := PcanChoiceMixin (AllSeq_pcancel H).

  Definition AllSeq_countMixin (s:seq T) (H:forall x, x \in s)
    := CountMixin (AllSeq_pcancel H).

End choice.

(* ***************************** *)
(* fintype *)
(* ***************************** *)
Section fintype.

  Lemma enum0: enum 'I_0 = [::].
  Proof. apply : (inj_map val_inj). by rewrite val_enum_ord. Qed.

  Lemma eq_ord0: all_equal_to (@ord0 0).
  Proof.
    move => i. apply : ord_inj. move : (leq_ord i). rewrite leqn0. by move /eqP.
  Qed.

  Lemma in_enum (T:finType) (x:T) : x \in enum T.
  Proof. by rewrite mem_enum. Qed.

  Lemma map_val_lshift_enum n m :
    map (val \o @lshift _ m) (enum 'I_n) = iota 0 n.
  Proof.
    rewrite (@eq_map _ _ _ val) =>//; exact : val_enum_ord.
  Qed.

  Lemma map_val_rshift_enum n m :
    map (val \o @rshift n _) (enum 'I_m) = iota n m.
  Proof.
    rewrite (@eq_map _ _ _ (addn n \o val))=>//.
      by rewrite map_comp val_enum_ord -iota_addl addn0.
  Qed.

  Lemma enum_ord_add n m :
    enum 'I_(n + m) =
    map (@lshift _ _) (enum 'I_n) ++ map (@rshift _ _) (enum 'I_m).
  Proof.
    apply : (inj_map val_inj).
    rewrite map_cat val_enum_ord -map_comp map_val_lshift_enum.
      by rewrite -map_comp map_val_rshift_enum iota_add add0n.
  Qed.

  Lemma arg_min_pred0 (T:finType) i0 P (F:T -> nat) :
    P =1 pred0 -> [arg min_(i < i0 | P i) F i] = i0.
  Proof.
    rewrite /arg_min /extremum => HP. case : pickP =>// x /=. by rewrite HP.
  Qed.

  Lemma arg_max_pred0 (T:finType) i0 P (F:T -> nat) :
    P =1 pred0 -> [arg max_(i > i0 | P i) F i] = i0.
  Proof.
    rewrite /arg_max /extremum => HP. case : pickP =>// x /=. by rewrite HP.
  Qed.

  Lemma cast_widen_ord n m (eq_n_m: n = m) :
    cast_ord eq_n_m =1 widen_ord (eq_leq eq_n_m).
  Proof. move => i. exact : ord_inj. Qed.

  Lemma cast_ord_eqneq (n m:nat) (eq1 eq2:n = m) :
    cast_ord eq1 =1 cast_ord eq2.
  Proof. move => i. exact : ord_inj. Qed.

  Lemma cast_ord_addn (n n' m m':nat) (eqn:n = n') (eqm:m = m')
        (eqnm:n + m = n' + m') (i:'I_(n + m)):
    cast_ord eqnm i = match split i with
                      | inl j => lshift m' (cast_ord eqn j)
                      | inr j => rshift n' (cast_ord eqm j)
                      end.
  Proof. apply ord_inj. case : splitP => j //=->. by rewrite eqn. Qed.

  Lemma cast_ord_addnA n m l (i:'I_(n + (m + l))) :
    cast_ord (addnA _ _ _) i = match split i with
                               | inl j => lshift l (lshift m j)
                               | inr j => match split j with
                                          | inl k => lshift l (rshift n k)
                                          | inr k => rshift (n + m) k
                                          end
                               end.
  Proof.
    apply : ord_inj. case : splitP =>//= j ->. case : splitP => k ->//=.
    exact : addnA.
  Qed.

  Lemma split_lshift m n (i:'I_m) : split (lshift n i) = inl i.
  Proof. exact : (canLR (@unsplitK _ _)). Qed.

  Lemma split_rshift m n (i:'I_n) : split (rshift m i) = inr i.
  Proof. exact : (canLR (@unsplitK _ _)). Qed.

  Lemma image_comp (T1 T2:finType) (T:eqType)
        (f:T2 -> T) (g:T1 -> T2) (A:pred T1) :
    image (f \o g) A =i image f (image g A).
  Proof.
    move => z. apply /(sameP mapP). apply /(iffP mapP) =>[[y]|[x] Hx /=->].
    - rewrite mem_enum. case /mapP => x Hx ->->. by exists x.
    - exists (g x) =>//. rewrite mem_enum. apply /mapP. by exists x.
  Qed.

  Lemma subsetIl (T:finType) (A B:pred T) :
    [predI A & B] \subset A.
  Proof. apply /subsetP => x. by case /andP. Qed.

  Lemma subsetIr (T:finType) (A B:pred T) :
    [predI A & B] \subset B.
  Proof. apply /subsetP => x. by case /andP. Qed.

  Lemma disjointP (T:finType) (A B:pred T) :
    reflect ([predI A & B] =1 pred0) [disjoint A & B].
  Proof. exact : pred0P. Qed.

  Lemma disjoint_cardP (T:finType) (A B:pred T) :
    reflect (#|[predU A & B]| = #|A| + #|B|) [disjoint A & B].
  Proof.
    rewrite -cardUI. apply /(iffP idP).
    - move /eqP =>->. by rewrite addn0.
    - move /eqP. by rewrite -{1}[#|_|]addn0 eqn_add2l eq_sym.
  Qed.

  Lemma disjointIlP (T:finType) (A B:pred T) :
    reflect (forall (C:pred T), [disjoint [predI C & A] & [predI C & B]])
            [disjoint A & B].
  Proof.
    apply /(iffP idP).
    - rewrite disjoint_sym => Hdis C.
      apply : (disjoint_trans (B:=A)); first exact : subsetIr.
      rewrite disjoint_sym.
      apply : (disjoint_trans (B:=B))=>//; exact : subsetIr.
    - rewrite -(eq_disjoint (predTI _)) -(eq_disjoint_r (predTI _)). exact.
  Qed.

  Lemma disjointIrP (T:finType) (A B:pred T) :
    reflect (forall (C:pred T), [disjoint [predI A & C] & [predI B & C]])
            [disjoint A & B].
  Proof.
    apply /(iffP idP).
    - move /disjointIlP => H C.
      have /eq_disjoint -> : [predI A & C] =i [predI C & A]
        by move => ?; exact : andbC.
      rewrite (eq_disjoint_r (predIC _ _)).
      exact : H.
    - rewrite -(eq_disjoint (predIT _)) -(eq_disjoint_r (predIT _)). exact.
  Qed.

  Lemma pred_card_addn (T:finType) (A B P: pred T):
    [disjoint A & B]
    -> [predU A & B] =i predT
    -> #|P| = #|[predI A & P]| + #|[predI B & P]|.
  Proof.
    move => Hdis HU. rewrite -(elimT (disjoint_cardP _ _));
      last by move /disjointIrP : Hdis =>->.
    apply : eq_card => x. move : (HU x). by rewrite !inE -andb_orl =>->.
  Qed.

  Lemma pred_sum_card (T1 T2:finType) (P : pred (T1 + T2)) :
    #|P| = #|P \o inl| + #|P \o inr|.
  Proof.
    rewrite (@card_preim _ _ inl); last by move => x y [].
    rewrite (@card_preim _ _ inr); last by move => x y [].
    apply : pred_card_addn.
    - apply /disjointP => [][]x/=; rewrite codom_f ?andbT /=;
      by apply /codomP =>[][]y.
    - case => x; rewrite !unfold_in /=; rewrite codom_f//. exact : orbT.
  Qed.

End fintype.

(* ***************************** *)
(* finfun *)
(* ***************************** *)
Section finfun.

  Variable (X:Type).

  Definition empty_index: X ^ 0.
  Proof. by apply : finfun => -[?]. Defined.

  Lemma eq_empty_index: all_equal_to empty_index.
  Proof. move => index. apply /ffunP => i. by move : (ltn_ord i). Qed.

  Lemma eq_index1 (x:X):
    all_equal_to x -> forall n, all_equal_to [ffun _:'I_n => x].
  Proof. move => H n index. apply /ffunP => i. by rewrite ffunE H. Qed.

  Definition cast_index n m (eq_nm:n = m) (f:X^n) := ecast m _ eq_nm f.

  Lemma cast_index_id n (f:X^n) (eqn: n = n) : cast_index eqn f = f.
  Proof. by rewrite eq_axiomK. Qed.

  Lemma cast_indexK n m (eq_nm:n = m):
    cancel (cast_index eq_nm) (cast_index (esym eq_nm)).
  Proof. by case : m / eq_nm. Qed.

  Lemma cast_indexKV n m (eq_nm:n = m):
    cancel (cast_index (esym eq_nm)) (cast_index eq_nm).
  Proof. by case : m / eq_nm. Qed.

  Lemma cast_index_trans n1 n2 n3 (eq12:n1 = n2) (eq23:n2 = n3) f:
    cast_index eq23 (cast_index eq12 f) = cast_index (etrans eq12 eq23) f.
  Proof. by case : n3 / eq23. Qed.

  Lemma cast_index_inj n m (eq_nm:n = m):
    injective (cast_index eq_nm).
  Proof. exact : can_inj (cast_indexK _). Qed.

  Lemma cast_indexE n m (eq_nm:n = m) f i:
    (cast_index eq_nm f) i = f (cast_ord (esym eq_nm) i).
  Proof. case : m / eq_nm in i *. by rewrite cast_index_id cast_ord_id. Qed.

End finfun.

Section index_app.

  Variable (X:Type).
  Variable (dim dim':nat).

  Definition index_disjoint (index:X ^ dim) (index':X ^ dim') :=
    fun i :'I_dim + 'I_dim'
    => match i with
       | inl j => index j
       | inr j => index' j
       end.

  Definition index_app (index:X ^ dim) (index':X ^ dim') :=
    finfun ((index_disjoint index index') \o @split dim dim').

End index_app.

Section index_app_lemma.

  Variable (X Y:Type).
  Variable (dim dim' dim'':nat).

  Lemma index_app_unsplit (index:X ^ dim) (index':X ^ dim'):
    (index_app index index') \o (@unsplit dim dim')
    =1 index_disjoint index index'.
  Proof.
    move => i /=. by rewrite /index_app ffunE /= unsplitK.
  Qed.

  Lemma index_app_lshift (index:X ^ dim) (index':X ^ dim') (i:'I_dim):
    (index_app index index') (lshift dim' i) = index i.
  Proof. exact : index_app_unsplit (inl i). Qed.

  Lemma index_app_rshift (index:X ^ dim) (index':X ^ dim') (i:'I_dim'):
    (index_app index index') (rshift dim i) = index' i.
  Proof. exact : index_app_unsplit (inr i). Qed.

  Definition index_projl (index:X ^ (dim + dim')) :=
    finfun (index \o @unsplit dim dim' \o inl).

  Definition index_projr (index:X ^ (dim + dim')) :=
    finfun (index \o @unsplit dim dim' \o inr).

  Lemma index_app_proj (index:X ^ (dim + dim')) :
    index_app (index_projl index) (index_projr index) = index.
  Proof.
    apply /ffunP => i. rewrite ffunE /=.
    case : splitP => j Heq /=; rewrite ffunE; congr(index _); exact : ord_inj.
  Qed.

  Lemma index_projl_app (index:X ^ dim) (index':X ^ dim'):
    index_projl (index_app index index') = index.
  Proof.
    apply /ffunP => i. by rewrite ffunE /index_app !/comp ffunE unsplitK.
  Qed.

  Lemma index_projr_app (index:X ^ dim) (index':X ^ dim'):
    index_projr (index_app index index') = index'.
  Proof.
    apply /ffunP => i. by rewrite ffunE /index_app !/comp ffunE unsplitK.
  Qed.

  Lemma index_appA (index:X ^ dim) (index':X ^ dim') (index'':X ^ dim''):
    index_app index (index_app index' index'')
    = cast_index (esym (addnA _ _ _))
                 (index_app (index_app index index') index'').
  Proof.
    apply /ffunP => i. rewrite cast_indexE !ffunE esymK cast_ord_addnA /=.
    by case : splitP => j _/=; last (rewrite ffunE /=; case : splitP => k _);
      rewrite ?split_lshift ?split_rshift //=
              ?index_app_lshift ?index_app_rshift.
  Qed.

  Lemma coeff_index_app_proj k (coeff:(X ^ (dim + dim') : Type) ^ k):
    [ffun j => index_app (index_projl (coeff j)) (index_projr (coeff j))] =
    coeff.
  Proof. apply /ffunP => i. by rewrite ffunE index_app_proj. Qed.

  Lemma index_app_additive (index:X ^ dim) (index':X ^ dim') (f:X -> Y):
    finfun (f \o (index_app index index'))
    = index_app (finfun (f \o index)) (finfun (f \o index')).
  Proof.
    apply /ffunP => x. rewrite !ffunE /= !ffunE /=.
    case : splitP => i Heq /=; by rewrite ffunE.
  Qed.

End index_app_lemma.

(* ***************************** *)
(* bigop *)
(* ***************************** *)
Section big_idx.

  Variable (R I:Type).
  Variable (op:R -> R -> R).
  Implicit Types (P:pred I).

  Lemma big_idx_assoc r P F x y:
    associative op ->
    op (\big[op/x]_(i <- r | P i) F i) y
    = \big[op/op x y]_(i <- r | P i) F i.
  Proof.
    move => Hassoc.
    elim : r =>[|i r IHr]; first by rewrite !big_nil.
    rewrite !big_cons. by case : ifP; rewrite -IHr.
  Qed.

  Lemma big_idx_distrl S (op':R -> S -> R) r P F x s:
    left_distributive op' op ->
    op' (\big[op/x]_(i <- r | P i) F i) s
    = \big[op/op' x s]_(i <- r | P i) op' (F i) s.
  Proof.
    move => Hdist.
    elim : r =>[|i r IHr]; first by rewrite !big_nil.
    rewrite !big_cons. by case : ifP; rewrite -IHr.
  Qed.

  Lemma big_idx_distrr S (op':S -> R -> R) r P F x s:
    right_distributive op' op ->
    op' s (\big[op/x]_(i <- r | P i) F i)
    = \big[op/op' s x]_(i <- r | P i) op' s (F i).
  Proof.
    move => Hdistr.
    elim : r =>[|i r IHr]; first by rewrite !big_nil.
    rewrite !big_cons. by case : ifP; rewrite -IHr.
  Qed.

  Lemma big_idx_distr op' r P F x y:
    right_distributive op op' ->
    \big[op/op' x y]_(i <- r | P i) F i
    = op' (\big[op/x]_(i <- r | P i) F i) (\big[op/y]_(i <- r | P i) F i).
  Proof.
    move => Hdistr.
    elim : r =>[|i r IHr]; first by rewrite !big_nil.
    rewrite !big_cons. by case : ifP; rewrite IHr.
  Qed.

End big_idx.

Section big_ord.

  Variable (R:Type).
  Variable (idx:R).
  Variable (op:R -> R -> R).

  Lemma big_split_ord_nested m n (P : pred 'I_(m + n)) F :
    let x := \big[op/idx]_(i | P (rshift m i)) F (rshift m i) in
    \big[op/idx]_(i | P i) F i =
    \big[op/x]_(i | P (lshift n i)) F (lshift n i).
  Proof.
    move =>/=.
    rewrite -(big_map (lshift n)) -(big_map (@rshift m n)) -big_cat_nested.
    congr bigop. apply : (inj_map val_inj). rewrite /index_enum -!enumT.
    rewrite val_enum_ord map_cat -map_comp val_enum_ord -map_comp.
      by rewrite (map_comp (addn m)) val_enum_ord -iota_addl addn0 iota_add.
  Qed.

  Lemma big_cast_ord n m (eq_n_m: n = m) (P:pred _) F :
    \big[op/idx]_(i < m | P i) F i =
    \big[op/idx]_(i < n | P (cast_ord eq_n_m i)) F (cast_ord eq_n_m i).
  Proof.
    rewrite (eq_bigl (fun i => P i && (i < n)));
    last by (move => i; rewrite eq_n_m ltn_ord andbT).
    rewrite (big_ord_narrow_cond (eq_leq eq_n_m)).
    apply : eq_big => i; by rewrite cast_widen_ord.
  Qed.

End big_ord.

Section big_eqType.
  Variable (T : eqType) (l : seq eqType).
  Definition bigprod_eqType := \big[prod_eqType/T]_(S <- l) S.
  Definition bigsum_eqType := \big[sum_eqType/T]_(S <- l) S.
End big_eqType.

Section big_finType.
  Variable (T : finType) (l : seq finType).
  Definition bigprod_finType := \big[prod_finType/T]_(S <- l) S.
  Definition bigsum_finType := \big[sum_finType/T]_(S <- l) S.
End big_finType.
