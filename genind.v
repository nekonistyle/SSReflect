From mathcomp
     Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ***************************** *)
Module Gen_Ind.
  Notation empty := Empty_set.

  Inductive nconstructor (n:nat) : Type :=
  | NConstructor of iter n (sum unit) empty.

  Fixpoint nthcon_rec (n m:nat) : iter n.+1 (sum unit) empty :=
    match n return iter n.+1 (sum unit) empty with
    | 0 => inl tt
    | n'.+1 => match m with
               | 0 => inl tt
               | m'.+1 => inr (nthcon_rec n' m')
               end
    end.

  Definition nthcon (n m:nat) : nconstructor n.+1 :=
    NConstructor (nthcon_rec n m).

  Definition day := nconstructor 7.
  Definition monday : day := nthcon _ 0.
  Definition tuesday : day := nthcon _ 1.
  Definition wednesday : day := nthcon _ 2.
  Definition thursday : day := nthcon _ 3.
  Definition friday : day := nthcon _ 4.
  Definition saturday : day := nthcon _ 5.
  Definition sunday : day := nthcon _ 6.

(* uniqueness *)
  Lemma nthcon_rec_uniq (n m m':nat) :
    m <= n -> m' <= n -> nthcon_rec n m = nthcon_rec n m' -> m = m'.
  Proof.
    elim : n m m' =>[|n IH][|m][|m']//=. by rewrite !ltnS => Hm Hm' [/IH->].
  Qed.
  Lemma nthcon_uniq (n m m':nat) :
    m <= n -> m' <= n -> nthcon n m = nthcon n m' -> m = m'.
  Proof.
    move => Hm Hm' []. exact /nthcon_rec_uniq.
  Qed.

(* case *)
  Lemma nthcon_rec_case (n:nat) (x:iter n.+1 (sum unit) empty) :
    exists m, m <= n /\ x = nthcon_rec n m.
  Proof.
    elim : n x =>[|n IHn][[]|x]//; try by exists 0.
    case : (IHn x) => m [Hm ->]. exists m.+1. by rewrite ltnS Hm.
  Qed.
  Lemma nthcon_case (n:nat) (x:nconstructor n.+1) :
    exists m, m <= n /\ x = nthcon n m.
  Proof.
    case : x =>[x]. case : (nthcon_rec_case x) => m [Hm ->]. by exists m.
  Qed.
  
(* induction principle *)
  Lemma my_nconstructor_ind (n:nat) (P:nconstructor n.+1 -> Prop):
    (forall m, m <= n -> P (nthcon _ m)) -> forall x, P x.
  Proof.
    move => H x. by case : (nthcon_case x) =>[m [/H HP ->]].
  Qed.

  (**)

  Fixpoint eachcon (T:Type) (f:T -> Type) (s:seq T) (n:nat) : Type :=
    match s with
    | [::] => empty
    | x :: s' => match n with
                  | 0 => f x
                  | n'.+1 => eachcon f s' n'
                  end
    end.

  Lemma eachcon_nthmap T (f:T -> Type) s n:
    eachcon f s n = nth (empty:Type) (map f s) n.
  Proof. by elim : s n =>[|x s IH][|n]//=. Qed.

  Inductive mkInd (T:Type) (f:T -> Type) : seq T -> Type :=
  | MkIndNil : empty -> mkInd f [::]
  | MkIndCons x s : f x + mkInd f s -> mkInd f (x :: s).

  Definition mymkInd_ind (T:Type) (f:T -> Type) (P:forall s,mkInd f s -> Prop)
    (IHf:forall x s (t:f x), P (x :: s) (MkIndCons (inl t)))
    (IHcons:forall x s (t:mkInd f s), P _ t -> P (x :: s) (MkIndCons (inr t))):
    forall s (x:mkInd f s), P _ x :=
    fix loop s x : P s x :=
      match x with
      | MkIndNil e => match e with end
      | MkIndCons x s' t => match t with
                            | inl fx => IHf _ _ fx
                            | inr t' => IHcons _ _ _ (loop s' t')
                            end
      end.

  Definition mymkInd_ind' (T:Type) (f:T -> Type) (P:forall s,mkInd f s -> Prop)
    (IHf:forall x s (t:f x), P (x :: s) (MkIndCons (inl t)))
    (IHcons:forall x s (t:mkInd f s), P _ t -> P (x :: s) (MkIndCons (inr t))) :
    forall s (x:mkInd f s), P _ x.
  Proof.
    fix HP 2.
    move => s [[]|x s' [a|t]]; [apply /IHf|apply /IHcons/HP].
  Defined.


  Fixpoint mkcon_rec (T:Type) (f:T -> Type) (s:seq T) (n:nat):
    eachcon f s n -> mkInd f s :=
    match s, n return eachcon f s n -> mkInd f s with
    | [::],_ => MkIndNil f
    | x :: s',0 => @MkIndCons _ f _ _ \o inl
    | x :: s',n'.+1 => @MkIndCons _ _ _ _ \o inr \o @mkcon_rec _ f s' n'
    end.

  Lemma mkInd_case (T:Type) (f:T -> Type) (s:seq T) (x:mkInd f s):
    exists n, n < size s /\ exists a:eachcon f s n, x = mkcon_rec a.
  Proof.
    elim /mymkInd_ind : x =>[x s' t|x s' t [n [Hn [a ->]]]].
    - exists 0. split =>//=. by exists t.
    - exists n.+1. split =>//=. by exists a.
  Qed.

  Inductive mkInductive (T:Type) (f:T -> Type) (s:seq T) : Type :=
  | MkInductive of mkInd f s.

  Definition mkcon (T:Type) (f:T -> Type) (s:seq T) (n:nat):
    eachcon f s n -> mkInductive f s :=
    @MkInductive _ _ _ \o @mkcon_rec _ f s n.

  Lemma mkcon_case (T:Type) (f:T -> Type) (s:seq T) (x:mkInductive f s):
    exists n, n < size s /\ exists a:eachcon f s n, x = mkcon a.
  Proof.
    case : x =>[x]. case : (mkInd_case x) => n [Hn [a ->]].
    exists n. split =>//. by exists a.
  Qed.

  Lemma my_mkInductive_ind (T:Type) (f:T -> Type) (s:seq T)
        (P:mkInductive f s -> Prop):
    (forall n, n < size s ->
               forall a:eachcon f s n, P (mkcon a)) ->
    forall x, P x.
  Proof.
    move => H x. by case : (mkcon_case x) =>[n [/H H'][a ->]].
  Qed.


  (**)
  Inductive sizseq (T:Type) : nat -> Type :=
  | SizNil : sizseq T 0
  | SizCons n : T -> sizseq T n -> sizseq T n.+1.

  Fixpoint sizfold (T S:Type)
           (f:T -> S -> S) (id:S) (n:nat) (i:sizseq T n) : S :=
    match i with
    | SizNil => id
    | SizCons _ x i' => f x (sizfold f id i')
    end.

  Definition seq_of_sizseq (T:Type) (n:nat) (s:sizseq T n) : seq T :=
    sizfold cons [::] s.

(**)
  Inductive basicInductive (s:seq (Type * nat)) : Type :=
  | BasicInductive
      of mkInd (fun tn => tn.1 * sizseq (basicInductive s) tn.2:Type) s.

  Definition basicInductiveCon (s:seq (Type * nat)) (n:nat) :
    eachcon (fun tn => tn.1 * sizseq (basicInductive s) tn.2:Type) s n ->
    basicInductive s := @BasicInductive _ \o @mkcon_rec _ _ _ _.

  Fixpoint mkIndProp (T:Type) (f:T -> Type)
           (P:forall x,f x -> Prop) (s:seq T) (t:mkInd f s) : Prop :=
    match t with
    | MkIndNil _ => True
    | MkIndCons x s' yt => match yt with
                          | inl y => P _ y
                          | inr t' => mkIndProp P t'
                          end
    end.

  Lemma my_basicInductive_ind'
        (s:seq (Type * nat)) (P:basicInductive s -> Prop):
    let f : Type * nat -> Type :=
        fun tn => tn.1 * sizseq (basicInductive s) tn.2:Type in
    (forall t:mkInd f s,
        @mkIndProp _ f (fun tn (x:f tn) => sizfold (and \o P) True x.2) s t ->
        P (BasicInductive t)) ->
    forall x, P x.
  Proof.
    move =>/= H.
    fix HP 1.
    case => m. apply /H. move : (basicInductive s) P HP m {H} => X P HP.
    apply : mymkInd_ind s =>[x s t|]//=. by elim : t.2.
  Qed.

  Fixpoint eachconProp (T:Type) (f:T -> Type) (P:forall x,f x -> Prop)
           (s:seq T) (n:nat) : eachcon f s n -> Prop :=
    match s,n return eachcon f s n -> Prop with
    | [::],_ => fun => True
    | t :: s',0 => @P _
    | t :: s',n'.+1 => @eachconProp _ _ P s' n'
    end.

  Lemma my_basicInductive_ind
        (s:seq (Type * nat)) (P:basicInductive s -> Prop):
    let f : Type * nat -> Type :=
        fun tn => tn.1 * sizseq (basicInductive s) tn.2:Type in
    (forall n,
      n < size s ->
      forall x:eachcon f s n,
        eachconProp (fun _ x => sizfold (and \o P) True x.2) x ->
        P (basicInductiveCon x)) ->
    forall x, P x.
  Proof.
    move => f H. elim /(my_basicInductive_ind') => t. case : (mkInd_case t).
    move => n [Hn [x ->]] H'. apply /H =>//. move : n x P H' {t f H Hn}.
    move : (basicInductive s) => X. elim : s =>[|x s IH][|n]// t P. exact /IH.
  Qed.


  (* myseq *)

  Definition seqdef (T:Type) : seq (Type * nat) := [:: (unit:Type,0); (T,1)].

  Definition myseq (T:Type) := basicInductive (seqdef T).
  Definition mynil (T:Type) : myseq T :=
    @basicInductiveCon (seqdef T) 0 (tt,SizNil _).
  Definition mycons (T:Type) (x:T) (s:myseq T) : myseq T :=
    @basicInductiveCon (seqdef T) 1 (x,SizCons s (SizNil _)).

  (**)

  Module Myseq.
    Require Import JMeq.
(*
    Inductive JMeq (A:Type) (x:A): forall B:Type, B -> Prop :=
      JMeq_refl : JMeq x x.      
    Axiom : JMeq_eq A (x y:A): JMeq x y -> x = y
*)
    Lemma sizseq0nil' (T:Type) (n:nat):
      forall s:sizseq T n, n = 0 -> JMeq s (SizNil T).
    Proof. by case. Qed.
    Lemma sizseq0nil (T:Type) : all_equal_to (SizNil T).
    Proof. move => s /=. exact /JMeq_eq/sizseq0nil'. Qed.

    Lemma sizseqScons' (T:Type) (n m:nat):
    forall s:sizseq T m, m = n.+1 ->
                         exists x (s':sizseq T n), JMeq s (SizCons x s').
    Proof. case =>// n' x s [<-]. by exists x,s. Qed.
    Lemma sizseqScons (T:Type) (n:nat):
      forall s:sizseq T n.+1, exists x s', s = SizCons x s'.
    Proof.
      move => s. case : (sizseqScons' s (erefl _)) =>[x [s' H]].
      exists x,s'. exact /JMeq_eq.
    Qed.

    Lemma myseq_case (T:Type) (s:myseq T) :
      s = mynil T \/ exists x s', s = mycons x s'.
    Proof.
      case : s => m. case : (mkInd_case m) =>[[|[|n]]][_]//=[[a x]->].
      - left. case : a. by rewrite (sizseq0nil x).
      - right. case : (sizseqScons x) =>[s' [s0 ->]]. exists a,s'.
          by rewrite (sizseq0nil s0).
    Qed.

    Lemma myseq_ind (T:Type) (P:myseq T -> Prop):
      P (mynil _) -> (forall x s, P s -> P (mycons x s)) -> forall s, P s.
    Proof.
      move => Hnil Hcons. elim /my_basicInductive_ind =>[[|[|n]]]//=_[a x]/=.
      - case : a. by rewrite (sizseq0nil x).
      - case : (sizseqScons x) =>[s' [s0 ->]]/=[Hs' _]. rewrite (sizseq0nil s0).
        exact : Hcons.
    Qed.
  End Myseq.
End Gen_Ind.

