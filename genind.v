From mathcomp
     Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ***************************** *)
Section Ind_Ind.
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


  Lemma nthcon_ex (n:nat) (x:iter n.+1 (sum unit) empty) :
    exists m, m <= n /\ x = nthcon_rec n m.
  Proof.
    elim : n x =>[|n IHn][[]|x]//; try by exists 0.
    case : (IHn x) => m [Hm ->]. exists m.+1. by rewrite ltnS Hm.
  Qed.

  Variant nthcon_or (n:nat) : iter n.+1 (sum unit) empty -> Set :=
  | NthconOr m of m <= n : nthcon_or (nthcon_rec n m).

  Lemma nthconP (n:nat) (x:iter n.+1 (sum unit) empty) : nthcon_or x.
  Proof.
    elim : n x =>[|n IHn][[]|x]//; try exact /(NthconOr (leq0n _)).
    case : (IHn x) => m. exact /(@NthconOr n.+1 m.+1).
  Qed.

  Lemma my_nconstructor_ind (n:nat) (P:nconstructor n.+1 -> Prop):
    (forall m, m <= n -> P (nthcon _ m)) -> forall x, P x.
  Proof.
    move => H [x]. by case : (nthconP x) => m /H.
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

  Lemma mkcon_ex (T:Type) (f:T -> Type) (s:seq T) (x:mkInd f s):
    exists n, n < size s /\ exists a:eachcon f s n, x = mkcon_rec a.
  Proof.
    elim /mymkInd_ind : x =>[x s' t|x s' t [n [Hn [a ->]]]].
    - exists 0. split =>//=. by exists t.
    - exists n.+1. split =>//=. by exists a.
  Qed.

  Variant mkcon_rec_or (T:Type) (f:T -> Type) (s:seq T) : mkInd f s -> Prop :=
  | MkconRecOr n (a:eachcon f s n) of n < size s : mkcon_rec_or (mkcon_rec a).

  Lemma mkcon_recP (T:Type) (f:T -> Type) (s:seq T) (x:mkInd f s) :
    mkcon_rec_or x.
  Proof.
    elim /mymkInd_ind : x =>[x s' t|x s' t [n a Hn]].
    - exact /(@MkconRecOr _ _ _ 0).
    - exact /(@MkconRecOr _ _ _ n.+1).
  Qed.

  Inductive mkInductive (T:Type) (f:T -> Type) (s:seq T) : Type :=
  | MkInductive of mkInd f s.

  Definition mkcon (T:Type) (f:T -> Type) (s:seq T) (n:nat):
    eachcon f s n -> mkInductive f s :=
    @MkInductive _ _ _ \o @mkcon_rec _ _ _ _.

  Variant mkcon_or (T:Type) (f:T -> Type) (s:seq T) : mkInductive f s -> Prop :=
  | MkconOr n (a:eachcon f s n) of n < size s : mkcon_or (mkcon a).

  Lemma mkconP (T:Type) (f:T -> Type) (s:seq T) (x:mkInductive f s) :
    mkcon_or x.
  Proof.
    case : x => x. case /mkcon_recP : x. exact /MkconOr.
  Qed.

  Lemma my_mkInductive_ind (T:Type) (f:T -> Type) (s:seq T)
        (P:mkInductive f s -> Prop):
    (forall n, n < size s -> forall a:eachcon f s n, P (mkcon a)) ->
    forall x, P x.
  Proof.
    move => H x. by case / mkconP : x =>[n a /H].
  Qed.

  (* vector *)

  Definition vector := Vector.t.
  Definition vnil (T:Type) : vector T 0 := Vector.nil _.
  Definition vcons (T:Type) (n:nat) (x:T) (s:vector T n) := Vector.cons _ x _ s.
  Definition vfoldr (A B:Type) (f:A -> B -> B) (x0:B) (n:nat) (s:vector A n) :=
    Vector.fold_right f s x0.

  Lemma vector0nil (T:Type) : all_equal_to (vnil T).
  Proof.
    move => x. exact : (@Vector.case0 _ (fun x => x = vnil T)).
  Qed.
  Lemma vectorScons (T:Type) n (s:vector T n.+1) :
    exists x (s':vector T n), s = vcons x s'.
  Proof.
    apply :
      (@Vector.caseS
         _ (fun n (s:vector T n.+1) =>
              exists (x:T) (s':vector T n), s = vcons x s')) => x m s'.
      by exists x,s'.
  Qed.

  (**)

  Inductive basicInductive (s:seq (Type * nat)) : Type :=
  | BasicInductive
      of mkInd (fun tn => tn.1 * vector (basicInductive s) tn.2:Type) s.

  Definition basicInductiveCon (s:seq (Type * nat)) (n:nat) :
    eachcon (fun tn => tn.1 * vector (basicInductive s) tn.2:Type) s n ->
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

  Lemma my_basicInductive_ind
        (s:seq (Type * nat)) (P:basicInductive s -> Prop):
    let f : Type * nat -> Type :=
        fun tn => tn.1 * vector (basicInductive s) tn.2:Type in
    (forall t:mkInd f s,
        @mkIndProp _ f (fun tn (x:f tn) => vfoldr (and \o P) True x.2) s t ->
        P (BasicInductive t)) ->
    forall x, P x.
  Proof.
    move =>/= H.
    fix HP 1.
    case => m. apply /H. move : (basicInductive s) P HP m {H} => X P HP.
    apply : mymkInd_ind s =>[x s t|]//=. by elim : t.2.
  Qed.


  (* myseq *)

  Definition seqdef (T:Type) : seq (Type * nat) := [:: (unit:Type,0); (T,1)].

  Definition myseq (T:Type) := basicInductive (seqdef T).
  Definition mynil (T:Type) : myseq T :=
    @basicInductiveCon (seqdef T) 0 (tt,vnil _).
  Definition mycons (T:Type) (x:T) (s:myseq T) : myseq T :=
    @basicInductiveCon (seqdef T) 1 (x,vcons s (vnil _)).

  Lemma myseq_case (T:Type) (s:myseq T) :
    s = mynil T \/ exists x s', s = mycons x s'.
  Proof.
    case : s =>[m]. case : (mkcon_ex m) =>[[|[|n]]][_]//=[[a x]->].
    - left. case : a. by rewrite (vector0nil x).
    - right. case : (vectorScons x) =>[s' [s0 ->]]. exists a,s'.
        by rewrite (vector0nil s0).
  Qed.

  Variant myseq_or (T:Type) : myseq T -> Prop :=
  | MyseqOrNil : myseq_or (mynil T)
  | MyseqOrCons x s: myseq_or (mycons x s).

  Lemma myseqP (T:Type) (s:myseq T) : myseq_or s.
  Proof.
    case : (myseq_case s) =>[|[x][s']]->.
    - exact /MyseqOrNil.
    - exact /MyseqOrCons.
  Qed.
  
  (**)

  Lemma myseq_ind (T:Type) (P:myseq T -> Prop):
    P (mynil _) -> (forall x s, P s -> P (mycons x s)) -> forall s, P s.
  Proof.
    move => Hnil Hcons. elim /my_basicInductive_ind => t.
    case : (mkcon_recP t) =>[[|[|n]]][]//= a x _.
    - case : a. by rewrite (vector0nil x).
    - case : (vectorScons x) =>[h][s']->/=[Hh _]. rewrite (vector0nil s').
      exact : Hcons.
  Qed.

End Ind_Ind.


