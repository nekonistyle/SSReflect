From mathcomp
     Require Import all_ssreflect all_algebra.
Add LoadPath "../mylib".
Require Export mylib mybig myalg.
Require Export NNet_sub_def NNet NNet_alg NNet_num ReLUNNet
        MPsolvable MPsolvable_alg MPsolvable_num.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export GRing Num.Theory NNetDef NNet_algDef NNet_numDef ReLUNNetDef.

(* ***************************** *)
Section ReLUMPsolvable_exNum_lower_bound.
  Variable (F:numFieldType).

  Let MPsolvable Idim l Odim s := @MPsolvable F Idim l Odim (pred_of_seq s).
  Let expressive_number := @expressive_number F.

(*
  Let inner_prod := @inner_prod _ (regular_lmodType F).

  Lemma ReLUMPsolvable_sorted_finite_set Idim Odim (s:seq (F ^ Idim))
        (f:F ^ Idim -> F ^ Odim) (w:F ^ Idim):
    {in s &, injective (inner_prod w)} ->
    mysorted (arg ge (inner_prod w)) s ->
    exists (bias1:F ^ _) (p2:MP1parameter _ _ _),
      (forall i:'I_(size s).-1,
          le 0%R (inner_prod w (nth 0%R s i) + bias1 i)%R) /\
      {in s, f =1 @MPfunction F _ [:: (size s).-1] _ ([ffun => w],bias1,p2)}.
  Proof.
    elim : s =>[_ _|x [_ _ _|y s IHs Hinj /andP [/allP Hge Hsorted]]].
    - exists (empty_index _), (MP1parameter0 _ _ _). split =>//= i.
        by move : (ltn_ord i).
    - exists (empty_index _), ((coeff0 _ _ _),f x).
      split =>[i|input]/=; first by move : (ltn_ord i).
      by rewrite MP1_coeff0 mem_seq1 =>/eqP ->.
    - case : (IHs _ Hsorted) =>{IHs}[u v Hu Hv|bias1 [] p2 [Hbias Heq] /=];
        first by (apply : Hinj; rewrite in_cons ?Hu ?Hv orbT).
      pose wx := inner_prod w x.
      pose s' := (filter (arg ge (inner_prod w) x) (y :: s)).
      case Hs' : s' =>[|z s''];
        last (move : (mem_head z s'');
               rewrite -Hs' mem_filter /arg /ge /==>/andP [Hzx Hz];
              case Hxz : (inner_prod w x == inner_prod w z)).
      + move /filter_nilP /allP : Hs' => H.
        exists (index_app [ffun _:'I_1 => (- wx + 1)%R] bias1),
        ([ffun i =>
          index_app [ffun _:'I_1 => (f x i - p2.2 i)%R] (p2.1 i)],p2.2).
        split =>[i|input].
        * rewrite -[i](@splitK 1 _).
          case : (@split 1 _ i) => j /=;
            rewrite ?(@index_app_lshift _ 1) ?(@index_app_rshift _ 1) =>//.
            by rewrite ffunE eq_ord0 /= addNKr ler01.
        * rewrite in_cons =>/orP [/eqP ->|Hinput];
          rewrite !(@MP1_inner_prod F) /=; apply /ffunP => i;
            rewrite !ffunE /= {1}/myalg.inner_prod -[_.+1]/(1 + _);
            rewrite big_split_ord big_ord_recl big_ord0 Monoid.mulm1;
            rewrite  index_app_lshift !ffunE /= ffunE index_app_lshift;
            rewrite !ffunE ReLU_def /max.
          rewrite addNKr ler01 /scale /= mulr1.
          rewrite big1 =>[|j _]; first by rewrite addr0 addrNK.
          rewrite !ffunE /= ffunE index_app_rshift ffunE ReLU_def /max.
          case : ifP =>[|_]; last exact : mulr0.
          move /(ger_leVge (Hbias j)). rewrite !ler_add2r.
          move : (@mem_nth _ 0%R (y :: s) _ (leqW (ltn_ord j))) => Hin /orP.
          move /negbTE : (H _ Hin). case /orP : (Hge _ Hin) =>[|->]//.
            by rewrite /arg /ge /= =>/negbTE ->->/orP.
          rewrite addrA -ler_subl_addl sub0r opprB. case : ifP =>[/ler1_real|_].
          rewrite realE subr_ge0 subr_le0 /wx. 
          case /orP : (Hge _ Hinput) (H _ Hinput) =>[|->]//.
            by rewrite /arg /ge /= =>/negbTE -> /negbTE ->.
          rewrite /scale /= mulr0 add0r (Heq _ Hinput) /= !(@MP1_inner_prod F).
          rewrite ffunE /myalg.inner_prod /=. congr (_ + _)%R.
          apply : eq_bigr => j _. rewrite index_app_rshift !ffunE /= ReLU_def.
          congr(_ * _)%R. congr max. rewrite !ffunE /= -index_app_unsplit /=.
            by rewrite splitK index_app_rshift.
      + exists (index_app [ffun _:'I_1 => (- wx)%R] bias1),
        ([ffun i => index_app [ffun _:'I_1 => 0%R] (p2.1 i)],p2.2).
        split =>[i|input].
        * rewrite -[i](@splitK 1 _).
          case : (@split 1 _ i) => j /=;
            rewrite ?(@index_app_lshift _ 1) ?(@index_app_rshift _ 1) =>//.
            by rewrite ffunE eq_ord0 /= addrN lerr.
        * rewrite in_cons =>/orP [/eqP->|Hinput];
          rewrite (@MP1_inner_prod F) /=; apply /ffunP => i;
            rewrite !ffunE /= {1}/myalg.inner_prod -[_.+1]/(1 + _);
            rewrite big_split_ord big_ord_recl big_ord0 Monoid.mulm1;
            rewrite index_app_lshift !ffunE scale0r /= add0r Heq =>//=.
          rewrite !(@MP1_inner_prod F) ffunE {1}/myalg.inner_prod /=.
          congr(_ + _)%R. apply : eq_bigr => j _. rewrite index_app_rshift.
            by rewrite !ffunE /= 3!ffunE index_app_rshift ffunE.
          move /eqP /(Hinj _ _ (mem_head _ _)) : Hxz =>->//.
            by rewrite in_cons Hz orbT.
          rewrite !(@MP1_inner_prod F) !ffunE {1}/myalg.inner_prod /=.
          congr(_ + _)%R. apply : eq_bigr => j _. rewrite index_app_rshift.
            by rewrite !ffunE /= 3!ffunE index_app_rshift ffunE.
      + pose wz := inner_prod w z.
        exists (index_app [ffun _:'I_1 => (- wz)%R] bias1),
        ([ffun i =>
          index_app
            [ffun _:'I_1 =>
             ((f x i - @MPfunction F _ [:: (size s)] _
                                   ([ffun => w], bias1, p2) x i) / (wx - wz))%R]
            (p2.1 i)], p2.2).
        split =>[i|input].
        * rewrite -[i](@splitK 1 _).
          case : (@split 1 _ i) => j /=;
            rewrite ?(@index_app_lshift _ 1) ?(@index_app_rshift _ 1) =>//.
          by rewrite ffunE eq_ord0 /= /wz subr_ge0.
        * rewrite in_cons =>/orP [/eqP->|Hinput];
          rewrite !(@MP1_inner_prod F) /=; apply /ffunP => i;
            rewrite !ffunE /= {1}/myalg.inner_prod -[_.+1]/(1 + _);
            rewrite big_split_ord big_ord_recl big_ord0 Monoid.mulm1;
            rewrite index_app_lshift !ffunE /= ffunE index_app_lshift;
            rewrite !ffunE ReLU_def /max /wx /wz subr_ge0.
          rewrite Hzx /scale /= mulfVK;
            last by (apply /negP; rewrite subr_eq0 Hxz).
          apply /eqP. rewrite -addrA addrC -subr_eq opprD opprK addNKr.
          rewrite (@neuron1_inner_prod F) {1}/myalg.inner_prod /=. apply /eqP.
          congr(_ + _)%R. apply : eq_bigr => j _. rewrite index_app_rshift.
          rewrite !ffunE /= 3!ffunE index_app_rshift (@neuron1_inner_prod F).
            by rewrite ffunE.
          rewrite (Heq _ Hinput) /= (@MP1_inner_prod F) ffunE.
          rewrite {1}/myalg.inner_prod /=.
          have : (if le (inner_prod w z) (inner_prod w input)
                  then (inner_prod w input - inner_prod w z)%R
                  else 0%R) = 0%R.
            case : ifP =>[Hzinput|]//.
            have Hs : mysorted (arg ge (inner_prod w)) (y :: s). done.
            have : mysorted (arg ge (inner_prod w)) s'.
              exact : (mysorted_filter _ Hs).
            have : input \in s'. move : (Hge _ Hinput).
            rewrite /s' mem_filter Hinput andbT /arg /ge /=.
              by case /orP : (ler_comparable Hzx Hzinput) =>->.
            rewrite Hs' in_cons /==>/orP [/eqP ->_|H /andP [/allP Hall _]];
              first exact : addrN.
            apply /eqP. rewrite subr_eq0. apply /eqP. apply : ler_anti.
            case /orP : (Hall _ H); by rewrite /arg /ge /= Hzinput =>//->.
          move =>->. rewrite scaler0 add0r. congr(_ + _)%R.
          apply : eq_bigr => j _. rewrite index_app_rshift !ffunE /= 3!ffunE.
          by rewrite index_app_rshift (@neuron1_inner_prod F) ffunE.
  Qed.

  Lemma ReLUMPsolvable_finite_set
        Idim Odim (s:seq (F ^ Idim)) (f:F ^ Idim -> F ^ Odim) :
    MPsolvable [:: (size s).-1] s f.
  Proof.
    case : (inner_prod_ex_inj s) => w Hw.
    pose s' := qsort (arg ge (inner_prod w)) s.
    have Heq : perm_eq s' s := perm_eq_qsort _ _.
    case : (@ReLUMPsolvable_sorted_finite_set
              _ _ s' f w _ (qsort_sorted (arg_trans _) _))
    =>[x y|y x z Hyx Hzy|bias1 [p2][_ Hf]].
    - rewrite !(perm_mem Heq). exact : Hw.
    - exact : (ler_trans Hzy Hyx).
    - rewrite -(perm_size Heq). apply : (MPsolvable_eql (perm_mem Heq)).
        by exists ([ffun => w], bias1, p2).
  Qed.

  Lemma ReLUexpressive_number_Hdim1 Idim Hdim Odim:
    expressive_number Idim [:: Hdim] Odim Hdim.+1.
  Proof.
    move => [|x s] f //[]<-. exact : (ReLUMPsolvable_finite_set (_ :: _)).
  Qed.
*)
(*
  Lemma ReLUMPsolvable_sorted_finite_set Odim (s:seq (F ^ 1))
        (f:F ^ 1 -> F ^ Odim) :
    mysorted (arg ge (fun x:_ ^ _ => x ord0)) s ->
    exists (bias1:_ ^ _) (p2:MP1parameter _ _ _),
      (forall i:'I_(size s).-1, le 0%R (nth 0%R s i ord0 + bias1 i)%R) /\
      let p : @MPparameter F 1 [:: (size s).-1] Odim
          := ([ffun => [ffun => 1%R]], bias1, p2) in
      {in s, f =1 MPfunction p}.
  Proof.
    elim : s =>[_|x [_ _/=|y s IHs /andP [/allP Hx Hsorted]]].
    - exists (empty_index _), (MP1parameter0  _ _ _). split =>//= i.
        by move : (ltn_ord i).
    - exists (empty_index _), ((coeff0 _ _ _),f x).
      split =>[i|input]; first by move : (ltn_ord i).
        by rewrite MP1_coeff0 mem_seq1 =>/eqP ->.
    - move : (IHs Hsorted) =>/=[bias1][p2][Hbias Hp2].
      pose mkbias1 (g:F ^ 1) : F ^ (size s).+1 := index_app g bias1.
      pose mkp2 (g:(F ^ 1) ^ Odim) : MP1parameter F (size s).+1 Odim
        := ([ffun i => index_app (g i) (p2.1 i)], p2.2).
      pose s' := (filter (arg ge (fun x:_ ^ _ => x ord0) x) (y :: s)).
      case Hs' : s' =>[|z s''];
        last (move : (mem_head z s'');
               rewrite -Hs' mem_filter /arg /ge /==>/andP [Hzx Hz];
               case : (x =P z) => Hxz).
      + move /filter_nilP /allP : Hs' => H.
        exists (mkbias1 [ffun => (- x ord0 + 1%R)%R]),
        (mkp2 [ffun i => [ffun => (f x i - p2.2 i)%R]]).
        split =>[i|input].
        * rewrite -[i](@splitK 1 _).
          case : (@split 1 _ i) => j /=;
            rewrite ?(@index_app_lshift _ 1) ?(@index_app_rshift _ 1) =>//.
          by rewrite ffunE eq_ord0 /= addNKr ler01.
        * rewrite in_cons =>/orP [/eqP ->|Hinput];
          rewrite !(@MP1_inner_prod F) /=; apply /ffunP => i;
            rewrite !ffunE /= /myalg.inner_prod -[_.+1]/(1 + _);
            rewrite big_split_ord big_ord_recl big_ord0 Monoid.mulm1;
            rewrite  index_app_lshift !ffunE /= ffunE index_app_lshift;
            rewrite !ffunE big_ord_recl big_ord0 addr0 ffunE scale1r;
            rewrite ReLU_def /max.
          rewrite addNKr ler01 /scale /= mulr1.
          rewrite big1 =>[|j _]; first by rewrite addr0 addrNK.
          rewrite !ffunE /= ffunE index_app_rshift ffunE ReLU_def /max.
          rewrite big_ord_recl big_ord0 addr0 ffunE mul1r.
          case : ifP =>[|_]; last exact : mulr0.
          move /(ger_leVge (Hbias j)). rewrite !ler_add2r.
          have Hj : (nth 0%R (y :: s) j) \in y :: s;
            first (apply : mem_nth; exact : leqW (ltn_ord j)).
          case /orP : (Hx _ Hj) (H _ Hj) =>[|->]//;
            by rewrite /arg /ge /==>/negbTE ->/negbTE ->.
          rewrite addrA -ler_subl_addl sub0r opprB. case : ifP =>[/ler1_real|_].
          rewrite realE subr_ge0 subr_le0.
          case /orP : (Hx _ Hinput) (H _ Hinput) =>[|->]//.
            by rewrite /arg /ge /==>/negbTE ->/negbTE ->.
          rewrite scaler0 add0r (Hp2 _ Hinput) !(@MP1_inner_prod F).
          rewrite ffunE /myalg.inner_prod /=. congr (_ + _)%R.
          apply : eq_bigr => j _. rewrite index_app_rshift !ffunE /= ReLU_def.
          congr(_ * _)%R. congr max. rewrite !ffunE /= -index_app_unsplit /=.
            by rewrite splitK index_app_rshift.
      + exists (mkbias1 (- x)%R), (mkp2 (coeff0 F _ _)).
        split =>[i|input H].
        * rewrite -[i](@splitK 1 _).
          case : (@split 1 _ i) => j /=;
            rewrite ?(@index_app_lshift _ 1) ?(@index_app_rshift _ 1) =>//.
            by rewrite ffunE eq_ord0 /= addrN lerr.
        * have Hinput : input \in y :: s;
          first by (move : H; rewrite in_cons Hxz =>/orP [/eqP->|]).
          rewrite (@MP1_inner_prod F) /=; apply /ffunP => i;
            rewrite !ffunE /= /myalg.inner_prod -[_.+1]/(1 + _);
            rewrite big_split_ord big_ord_recl big_ord0 Monoid.mulm1;
            rewrite index_app_lshift !ffunE scale0r /= add0r Hxz Hp2 =>//=.
          rewrite !(@MP1_inner_prod F) ffunE /myalg.inner_prod /=.
          congr(_ + _)%R. apply : eq_bigr => j _. rewrite index_app_rshift.
            by rewrite !ffunE /= 3!ffunE index_app_rshift ffunE.
      + exists (mkbias1 (- z)%R),
        (let p : @MPparameter F _ [:: (size s)] _
             := ([ffun => [ffun => 1%R]], bias1, p2) in
         mkp2 [ffun i =>
               [ffun => ((f x i - MPfunction p x i) / (x ord0 - z ord0))%R]]).
        split =>[i|input].
        * rewrite -[i](@splitK 1 _).
          case : (@split 1 _ i) => j /=;
            rewrite ?(@index_app_lshift _ 1) ?(@index_app_rshift _ 1) =>//.
          by rewrite ffunE eq_ord0 /= subr_ge0.
        * rewrite in_cons =>/orP [/eqP->|Hinput];
          rewrite !(@MP1_inner_prod F) /=; apply /ffunP => i;
            rewrite !ffunE /= /myalg.inner_prod -[_.+1]/(1 + _);
            rewrite big_split_ord big_ord_recl big_ord0 Monoid.mulm1;
            rewrite index_app_lshift !ffunE /= ffunE index_app_lshift;
            rewrite !ffunE ReLU_def big_ord_recl big_ord0 addr0 ffunE scale1r.
          rewrite /max subr_ge0 Hzx /scale /= mulfVK;
            last by (apply /negP; rewrite subr_eq0 =>/eqP H;
                     apply : Hxz; apply /ffunP => k; rewrite eq_ord0).
          apply /eqP. rewrite -addrA addrC -subr_eq opprD opprK addNKr.
          rewrite (@neuron1_inner_prod F) /myalg.inner_prod /=. apply /eqP.
          congr(_ + _)%R. apply : eq_bigr => j _. rewrite index_app_rshift.
          rewrite !ffunE /= 3!ffunE index_app_rshift (@neuron1_inner_prod F).
            by rewrite ffunE.
          rewrite (Hp2 _ Hinput) /= (@MP1_inner_prod F) ffunE.
          rewrite /myalg.inner_prod /=.
          have ->: max (input ord0 - z ord0) 0 = 0%R.
          rewrite /max subr_ge0. case : ifP =>[Hzinput|]//.
          have : mysorted (arg ge (fun x:_ ^ _=> x ord0)) s'
            by apply : mysorted_filter.
          have : input \in s'
            by (move : (ler_comparable Hzx Hzinput) (Hx _ Hinput);
                rewrite mem_filter Hinput andbT /arg /ge /==>/orP[->|]).
          rewrite Hs' in_cons =>/orP[/eqP->_|Hs'' /andP [/allP H _]];
            first exact : subrr.
          apply /eqP. move : (H _ Hs''). rewrite subr_eq0 eqr_le /arg /ge /=.
            by rewrite Hzinput /==>->.
          rewrite scaler0 add0r. congr(_ + _)%R. apply : eq_bigr => j _.
          rewrite index_app_rshift !ffunE /= 3!ffunE.
            by rewrite index_app_rshift (@neuron1_inner_prod F) ffunE.
  Qed.
 *)
(*
  Lemma ReLUMPsolvable_sorted_finite_set Odim (s:seq (F ^ 1))
        (f:F ^ 1 -> F ^ Odim) :
    mysorted (arg ge (fun x:_ ^ _ => x ord0)) s ->
    exists (bias1:_ ^ _) (p2:MP1parameter _ _ _),
      (forall i:'I_(size s).-1, le 0%R (nth 0 s i ord0 + bias1 i)%R) /\
      let p : @MPparameter F 1 [:: (size s).-1] Odim
          := ([ffun => [ffun => 1]]%R, bias1, p2) in
      {in s, f =1 MPfunction p}.
  Proof.
    elim : s =>[_|x [_ _/=|y s IHs /andP [/allP Hx Hsorted]]].
    - exists (empty_index _), (MP1parameter0  _ _ _). split =>//= i.
        by move : (ltn_ord i).
    - exists (empty_index _), ((coeff0 _ _ _),f x).
      split =>[i|input]; first by move : (ltn_ord i).
        by rewrite MP1_coeff0 mem_seq1 =>/eqP ->.
    - move : (IHs Hsorted) =>/=[bias1][p2][Hbias Hp2].
      pose mkbias1 (g:F ^ 1) : F ^ (size s).+1 := index_app g bias1.
      pose mkp2 (g:(F ^ 1) ^ Odim) : MP1parameter F (size s).+1 Odim
        := ([ffun i => index_app (g i) (p2.1 i)], p2.2).
      pose s' := (filter (arg ge (fun x:_ ^ _ => x ord0) x) (y :: s)).
      pose z := head [ffun => x ord0 - 1]%R s'.
      have Hzx : le 0%R (x ord0 - z ord0)%R.
        rewrite /z.
        case Hs' : s' =>[|z' s'']/=; first by rewrite ffunE subKr ler01.
        move : (mem_head z' s'').
          by rewrite -Hs' mem_filter /arg /ge subr_ge0 =>/andP [].      
      pose p : @MPparameter F 1 [:: size s] Odim
        := ([ffun => [ffun => 1%R]], bias1, p2).
      exists (mkbias1 (- z)%R),
      (mkp2 (if x == z then coeff0 _ _ _
             else [ffun i => [ffun => ((f x i - MPfunction p x i)
                                         / (x ord0 - z ord0))%R]])).
      have ->: [ffun =>[ffun => 1%R]]
      = index_app [ffun =>[ffun => 1%R]] [ffun =>[ffun => 1%R]]
                  :> (F ^ 1) ^ (1 + size s)
        by (apply /ffunP => i; rewrite !ffunE /=;
            case : splitP => j/=; rewrite ffunE).
      rewrite /mkp2 /mkbias1. split =>[i|input].
      + rewrite -[i](@splitK 1 _).
        case : (@split 1 _ i) => j /=;
          rewrite ?(@index_app_lshift _ 1) ?(@index_app_rshift _ 1) =>//.
          by rewrite eq_ord0 /= ffunE.
      + rewrite (@MP1_sumO _ _ 1) (@actf_app _ 1) (@MP1_appr _ 1).
        rewrite index_projl_app index_projr_app in_cons
                =>/orP [/eqP ->|Hinput]; last rewrite (Hp2 _ Hinput);
          apply /ffunP => i; rewrite !ffunE /neuron1 big_ord_recl big_ord0;
          rewrite /NNop /NNaction /= addr0;
          case : ifP => Heq; rewrite !ffunE /NNidC /= ?mul0r ?add0r //.
        * case Hs' : s' Heq (eq_refl (x ord0)) =>[|z' s'']/eqP;
            first by (move =>{2}->;
                                rewrite /z Hs' ffunE -subr_eq0 subKr oner_eq0).
          move =>->_/=. move : (mem_head z' s'').
          rewrite /z Hs' /= -Hs' mem_filter =>/andP [_]/Hp2 ->.
            by rewrite ffunE.
        * rewrite !ffunE /= /neuron1 big_ord_recl big_ord0 /NNop /NNaction /=.
          rewrite !ffunE mul1r ReLU_def /max Hzx mulfVK ?addrNK //.
          apply /negP. rewrite subr_eq0 =>/eqP H. move /eqP : Heq. apply.
          apply /ffunP => k. by rewrite eq_ord0.
        * rewrite !ffunE /= /neuron1 big_ord_recl big_ord0 /NNop /NNaction /=.
          rewrite !ffunE mul1r ReLU_def. move : Hzx. rewrite subr_ge0 => Hzx.
          suff ->: (max (input ord0 - z ord0) 0 = 0)%R by rewrite mulr0 add0r.
          rewrite /max subr_ge0. case : ifP =>// Hzinput. apply /eqP.
          have : input \in s'. rewrite mem_filter Hinput andbT /arg /ge.
          move : (ler_comparable Hzx Hzinput) (Hx _ Hinput).
            by rewrite /arg /ge /comparable /==>/orP[]->.
          move : Hzinput. rewrite subr_eq0 eqr_le /z.
          have : mysorted (arg ge (fun x:_ ^ _=> x ord0)) s'
            by apply : mysorted_filter.
          case Hs' : s' =>[|z' s'']//= /andP[/allP H _ Hzinput].
          rewrite in_cons =>/orP[/eqP ->|/H];
            by rewrite ?lerr // /arg /ge /= Hzinput /==>->.
  Qed.
 *)
  Let wsorted := mysorted.

  Lemma ReLUMPsolvable_sorted_finite_set Odim (s:seq (F ^ 1))
        (f:F ^ 1 -> F ^ Odim) :
    wsorted (fun x y => leInput y x) s ->
    exists (bias1:_ ^ _) (p2:MP1parameter _ _ _),
      (forall i:'I_(size s).-1, (0 <= (s`_i ord0 + bias1 i))%R) /\
      let p : @MPparameter F 1 [:: (size s).-1] Odim
          := ([ffun => [ffun => 1]]%R, bias1, p2) in
      {in s, f =1 MPfunction p}.
  Proof.
    elim : s =>[_|x [_ _/=|y s IHs /andP [/allP Hx Hsorted]]].
    - exists (empty_index _), (MP1parameter0 F _ _). split =>//= i.
        by move : (ltn_ord i).
    - exists (empty_index _), ((coeff0 F _ _),f x).
      split =>[i|input]; first by move : (ltn_ord i).
        by rewrite (@MP1_coeff0 F) mem_seq1 =>/eqP ->.
    - move : (IHs Hsorted) =>/=[bias1][p2][Hbias Hp2].
      pose mkbias1 (g:F ^ 1:Type) : F ^ (size s).+1 := index_app g bias1.
      pose mkp2 (g:(F ^ 1) ^ Odim:Type) : MP1parameter F (size s).+1 Odim
        := ([ffun i => index_app (g i) (p2.1 i)], p2.2).
      pose s' := filter ((@leInput _)^~ x) (y :: s).
      pose z := head [ffun => x ord0 - 1]%R s'.
      have Hzx : le 0%R (x ord0 - z ord0)%R.
        rewrite /z.
        case Hs' : s' =>[|z' s'']/=; first by rewrite ffunE subKr ler01.
        move : (mem_head z' s'').
          by rewrite -Hs' mem_filter subr_ge0 =>/andP [].      
      pose p : @MPparameter F 1 [:: size s] Odim
        := ([ffun => [ffun => 1%R]], bias1, p2).
      exists (mkbias1 (- z)%R),
      (mkp2 (if x == z then coeff0 F _ _
             else [ffun i => [ffun => ((f x i - MPfunction p x i)
                                         / (x ord0 - z ord0))%R]])).
      have ->: [ffun =>[ffun => 1%R]]
      = index_app [ffun =>[ffun => 1%R]] [ffun =>[ffun => 1%R]]
                  :> (F ^ 1) ^ (1 + size s):Type
        by (apply /ffunP => i; rewrite !ffunE /=;
            case : splitP => j/=; rewrite ffunE).
      rewrite /mkp2 /mkbias1. split =>[i|input].
      + rewrite -[i](@splitK 1 _).
        case : (@split 1 _ i) => j /=;
          rewrite ?(@index_app_lshift _ 1) ?(@index_app_rshift _ 1) =>//.
          by rewrite eq_ord0 /= ffunE.
      + rewrite (@MP1_sumO _ _ 1) (@actf_app _ 1) (@MP1_appr F 1).
        rewrite index_projl_app index_projr_app in_cons
                =>/orP [/eqP ->|Hinput]; last rewrite (Hp2 _ Hinput);
          apply /ffunP => i; rewrite !ffunE /neuron1 big_ord_recl big_ord0;
          rewrite /NNop /NNaction /= addr0;
          case : ifP => Heq; rewrite !ffunE /NNidC /= ?mul0r ?add0r //.
        * case Hs' : s' Heq (eq_refl (x ord0)) =>[|z' s'']/eqP;
            first by (move =>{2}->;
                                rewrite /z Hs' ffunE -subr_eq0 subKr oner_eq0).
          move =>->_/=. move : (mem_head z' s'').
          rewrite /z Hs' /= -Hs' mem_filter =>/andP [_]/Hp2 ->.
            by rewrite ffunE.
        * rewrite !ffunE /= /neuron1 big_ord_recl big_ord0 /NNop /NNaction /=.
          rewrite !ffunE mul1r ReLU_def /max Hzx mulfVK ?addrNK //.
          apply /negP. rewrite subr_eq0 =>/eqP H. move /eqP : Heq. apply.
          apply /ffunP => k. by rewrite eq_ord0.
        * rewrite !ffunE /= /neuron1 big_ord_recl big_ord0 /NNop /NNaction /=.
          rewrite !ffunE mul1r ReLU_def. move : Hzx. rewrite subr_ge0 => Hzx.
          suff ->: (max (input ord0 - z ord0) 0 = 0)%R by rewrite mulr0 add0r.
          rewrite /max subr_ge0. case : ifP =>// Hzinput. apply /eqP.
          have : input \in s'. rewrite mem_filter Hinput andbT.
          move : (ler_comparable Hzx Hzinput) (Hx _ Hinput).
            by rewrite /leInput /comparable =>/orP[]->//.
          move : Hzinput. rewrite subr_eq0 eqr_le /z.
          have : mysorted (fun x y => leInput y x) s'
            by apply : mysorted_filter.
          case Hs' : s' =>[|z' s'']//= /andP[/allP H _ Hzinput].
          rewrite in_cons =>/predU1P[->|/H];
            by rewrite ?lerr // /leInput Hzinput /==>->.
  Qed.

  Lemma ReLUexpressive_number_Hdim1 Idim Hdim Odim:
    expressive_number Idim [:: Hdim] Odim Hdim.+1.
  Proof.
    apply : expressive_number_Idim1 =>[][|x0 s] f //[]<-.
    pose s' := qsort (fun x y => leInput y x) (x0 :: s).
    have Heq : perm_eq s' (x0 :: s) := perm_qsort _ _.
    case : (@ReLUMPsolvable_sorted_finite_set _ s' f (qsort_sorted _ _))
    =>[y x z Hyx Hzy|bias [p2][_ H]]; first exact : (ler_trans Hzy Hyx).
    have : size s = (size s').-1 by rewrite /s' (perm_size Heq).
    move =>->. exists ([ffun =>[ffun => 1%R]], bias, p2) => input.
    rewrite -(perm_mem Heq). exact : H.
  Qed.

End ReLUMPsolvable_exNum_lower_bound.

(* ***************************** *)
Section ReLUMPsolvable_exNum_upper_bound.
  Variable (F:realDomainType).

  Let MPsolvable Idim l Odim s := @MPsolvable F Idim l Odim (pred_of_seq s).
  Let expressive_number := @expressive_number F.
  Let maximum_expressive_number := @maximum_expressive_number F.
  Let sign b := GRing.sign F b.

  Section zigzag.
    Let Odim := 1.
    Let k := ord0 : 'I_Odim.

    Fixpoint zigzag_def (X:Type) x0 (s:seq X) (f:X -> F ^ Odim) b :=
      match s with
      | [::] => true
      | x1 :: s' =>
        (sign b * (f x0 k) < sign b * (f x1 k))%R && zigzag_def x1 s' f (~~ b)
      end.

    Definition zigzag (X:Type) (s:seq X) (f:X -> F ^ Odim) :=
      match s with
      | [::] => true
      | x0 :: s' => zigzag_def x0 s' f true || zigzag_def x0 s' f false
      end.

    Fixpoint mkzigzag_def (X:eqType) (s:seq X) b : X -> F ^ Odim :=
      match s with
      | [::] => fun x => [ffun => 0%R]
      | y :: s' => fun x => if x == y then [ffun => sign b] else
                              (mkzigzag_def s' (~~ b) x)
      end.

    Definition mkzigzag (X:eqType) (s:seq X) := mkzigzag_def s true.

    Lemma eq_zigzag_def (X:eqType) x0 (s:seq X) (f f':X -> F ^ Odim) b :
      {in x0 :: s, f =1 f'} -> zigzag_def x0 s f b = zigzag_def x0 s f' b.
    Proof.
      elim : s =>[|x1 s IHs]//= in x0 b *=> Heq.
      move : (Heq x0) (Heq x1). rewrite !in_cons !eq_refl /= orbT =>->//->//.
      rewrite IHs =>// x Hx. apply : Heq. by rewrite in_cons Hx orbT.
    Qed.

    Lemma mkzigzag_zigzag_def (X:eqType) x0 (s:seq X) b :
      uniq (x0 :: s) -> zigzag_def x0 s (mkzigzag_def (x0 :: s) b) (~~ b).
    Proof.
      elim : s =>[|x1 s IHs]//= in x0 b *=> /andP [] Hx0 Hx1.
      move : (Hx0). rewrite !eq_refl in_cons eq_sym => /norP [] /negbTE ->_.
      apply /andP. split.
      - case : b; rewrite !ffunE /sign /= !expr0 !expr1 ?mulN1r ?mul1r ?opprK;
          exact : ltr_trans (@ltrN10 _) (@ltr01 _).
      - rewrite (@eq_zigzag_def _ _ _ _ (mkzigzag_def (x1 :: s) (~~ b)))
        =>[|x]; last (case : ifP =>[/eqP->|]//; by move /negbTE : Hx0 =>->).
        exact : (IHs _ _ Hx1).
    Qed.

    Lemma mkzigzag_zigzag (X:eqType) (s:seq X) :
      uniq s -> zigzag s (mkzigzag s).
    Proof.
      case : s =>[|x0 s]//= Huniq.
        by rewrite (mkzigzag_zigzag_def _ Huniq) ?orbT.
    Qed.

  End zigzag.

  Lemma ReLUexpressive_number_Hdim2_zigzag_sorted Hdim
        x0 (s:seq (F ^ 1)) b (f : F ^ 1 -> F ^ 1):
    zigzag_def x0 s f b ->
    sorted (@leInput _) (x0 :: s) ->
    MPsolvable [:: Hdim.+1] (x0 :: s) f ->
    size s <= Hdim.+2.
  Proof.
    rewrite sorted_myTsorted => [Hzigzag Hsorted [p Hp]|y x z Hxy Hyz];
                                  last exact : ler_trans Hxy Hyz.
    suff : exists l : seq nat,
        [/\ uniq l, size l = size s, all (geq Hdim.+1) l,
         myTsorted leq l && all (leq (inputRegion1 p.1 x0)) l &
         size l > 0
         -> lt
              ((sign (~~ b)) *
               ((lRegion1Parameter p (head 0%N l)).1 ord0 ord0))%R
              0%R].
    - case => l [Huniq <- /allP Hgeq] _ _. rewrite -[Hdim.+2](size_iota 0).
      apply : (uniq_leq_size Huniq) => n /Hgeq. by rewrite mem_iota add0n ltnS.
    - move : Hzigzag Hsorted Hp.
      elim : s =>[|x1 s IHs] in b x0 *; first by exists [::].
      move =>/= /andP [Houtput Hzigzag] /andP[/andP [Hx01 Hx0] Hsorted] Hp.
      case : {Hzigzag Hsorted} (IHs _ _ Hzigzag Hsorted)
      =>[x Hx|l [Huniq Hsize Hgeq /andP [Hsorted HRegion]]];
          first by (apply : Hp; rewrite in_cons Hx orbT).
      move : Houtput. rewrite !Hp ?in_cons ?eq_refl ?orbT //.
      case : b; rewrite /sign/= ?expr1 ?expr0 ?mulN1r ?mul1r ?ltr_opp2 ltrNge.
      + case /(ltOutput_ex_negslope Hx01)
        => n0 /andP [/andP [Hx0n0 Hn0x1] Hslope] Hl.
        exists (n0 :: l).
        split; rewrite /= ?Huniq ?Hsize ?Hgeq ?Hsorted ?Hx0n0 ?andbT //=.
        * case : l HRegion Hl Huniq Hsorted {Hsize Hgeq}
          =>[|n1 l]//= /andP [/(leq_trans Hn0x1)].
          rewrite leq_eqVlt oppr_lt0 ltrNge ltnS leq0n.
          case /predU1P =>[<-_|]; first by move /ltrW : Hslope =>/=->/implyP.
          rewrite in_cons negb_or neq_ltn =>Hlt _ _ _/andP [/allP Hl] _.
          rewrite Hlt /=. apply /negP =>/Hl. by rewrite leqNgt Hlt.
        * exact : (leq_trans Hn0x1 (inputRegion1_max _ _)).
        * have H : all (leq n0) l
            by apply : (sub_all _ HRegion) => x /(leq_trans Hn0x1).
          rewrite H /=. by apply : (sub_all _ H) => x /(leq_trans Hx0n0).
        * move : Hslope. by rewrite mul1r =>->.
      + case /(ltOutput_ex_posslope Hx01)
        => n0 /andP [/andP [Hx0n0 Hn0x1] Hslope] Hl.
        exists (n0 :: l).
        split; rewrite /= ?Huniq ?Hsize ?Hgeq ?Hsorted ?Hx0n0 ?andbT //=.
        * case : l HRegion Hl Huniq Hsorted {Hsize Hgeq}
          =>[|n1 l]//= /andP [/(leq_trans Hn0x1)].
          rewrite leq_eqVlt ltrNge ltnS leq0n.
          case /predU1P =>[<-_|]; first by move /ltrW : Hslope =>/=->/implyP.
          rewrite in_cons negb_or neq_ltn =>Hlt _ _ _/andP [/allP Hl] _.
          rewrite Hlt /=. apply /negP =>/Hl. by rewrite leqNgt Hlt.
        * exact : (leq_trans Hn0x1 (inputRegion1_max _ _)).
        * have H : all (leq n0) l
            by apply : (sub_all _ HRegion) => x /(leq_trans Hn0x1).
          rewrite H /=. by apply : (sub_all _ H) => x /(leq_trans Hx0n0).
        * move : Hslope. by rewrite mulN1r oppr_lt0 =>->.
  Qed.

  Lemma ReLUexpressive_number_Hdim2 Idim Hdim Odim n:
    0 < Idim -> 0 < Odim ->
    expressive_number Idim [:: Hdim] Odim n -> n <= Hdim.+2.
  Proof.
    case : Hdim =>[|Hdim] HIdim HOdim.
    - have H10 : 1%R <> 0%R :> F. apply /eqP. exact : oner_neq0.
      move : (@maximum_expressive_number_in0
                F _ _ _ _ _ [:: 0] _ HIdim HOdim H10 H10 (mem_head _ _)).
      move /maximum_expressive_numberP => H. move /H. by case : n =>[|[|[]]].
    - case : n =>[|n]//. rewrite ltnS.
      move /(expressive_number_Idim_independent HIdim) => HI.
      move : (expressive_number_Odim_le HOdim (HI 1)) => H.
      pose s : seq (F^1) := mkseq (fun m => [ffun => (m%:R)%R]) n.+1.
      move : {H} (H s (mkzigzag s) (size_mkseq _ _)).
      move /ReLUexpressive_number_Hdim2_zigzag_sorted.
      rewrite size_map size_iota. apply.
      + apply : mkzigzag_zigzag_def.
        rewrite -(@perm_uniq _ _ s (perm_refl _)) /s.
        apply : mkseq_uniq => m l /ffunP H. move : (H ord0).
        rewrite !ffunE. exact : (mulrIn (@oner_neq0 _)).
      + rewrite sorted_myTsorted =>[|y x z Hxy Hyz];
                                     last exact : ler_trans Hxy Hyz.
        apply : (@myTsorted_subseq _ _ s _ (subseq_refl _)).
        apply : (@myTsorted_map _ leq)
        =>[x y|]; last by rewrite -(sorted_myTsorted _ leq_trans) iota_sorted.
          by rewrite /leInput !ffunE ler_nat.
  Qed.

End ReLUMPsolvable_exNum_upper_bound.

(* ***************************** *)
Section ReLUmaximum_expressive_number.
  Variable (F:realFieldType).

  Let MPsolvable Idim l Odim s := @MPsolvable F Idim l Odim (pred_of_seq s).
  Let expressive_number := @expressive_number F.
  Let maximum_expressive_number := @maximum_expressive_number F.

  Lemma ReLUmaximum_expressive_number1_bound Idim Hdim Odim n:
    0 < Idim -> 0 < Odim ->
    maximum_expressive_number Idim [:: Hdim] Odim n ->
    Hdim.+1 <= n <= Hdim.+2.
  Proof.
    move => HIdim HOdim H.
    move /maximum_expressive_numberP : (H) => H'.
    move /H' : (@ReLUexpressive_number_Hdim1 F Idim Hdim Odim) =>->/=.
      by case : H => /(ReLUexpressive_number_Hdim2 HIdim HOdim).
  Qed.

  Lemma ReLUmaximum_expressive_number1 Idim Hdim Odim:
    0 < Idim -> 0 < Odim ->
    classically (maximum_expressive_number Idim [:: Hdim] Odim Hdim.+1 \/
         maximum_expressive_number Idim [:: Hdim] Odim Hdim.+2).
  Proof.
    move => HIdim HOdim.
    apply : classic_bind
              (@maximum_expressive_number_ex F Idim [:: Hdim] Odim Hdim.+3 _)
    =>[[m Hm]|/(ReLUexpressive_number_Hdim2 HIdim HOdim)]; last by rewrite ltnn.
    apply : classicW.
    move : (ReLUmaximum_expressive_number1_bound HIdim HOdim Hm).
    rewrite leq_eqVlt andb_orl -eqn_leq =>/orP [/andP[]/eqP->_|/eqP->].
    - by left.
    - by right.
  Qed.

End ReLUmaximum_expressive_number.
