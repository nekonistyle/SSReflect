From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ********************* *)

Section Transformer.
  Definition sumt (R:Type) : (Type -> Type) -> Type -> Type :=
    fun m A => m (R + A:Type).
  Definition mult (R:Type) (idx:R) (op:Monoid.law idx)
  : (Type -> Type) -> Type -> Type :=
    fun m A => m (R * A:Type).
  Definition appt (R:Type) : (Type -> Type) -> Type -> Type :=
    fun m A => R -> m A.
  Definition statet (R:Type) : (Type -> Type) -> Type -> Type :=
    fun m A => R -> m (R * A:Type).
End Transformer.

(* ********************* *)

Module Pure.
  Definition Eta (m:Type -> Type) := forall A, A -> m A.

  Record class_of (m:Type -> Type) :=
    Class {
        eta : Eta m;
      }.

  Section ClassDef.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
  End ClassDef.

  Module Exports.
    Coercion apply : map >-> Funclass.
    Notation pureMap := map.
    Notation Eta := Eta.
    Definition eta T := (eta (class T)).
  End Exports.
End Pure.
Import Pure.Exports.

Section Pure_lemma.
  Variable (m:pureMap).
  Let eta := eta m.
End Pure_lemma.

Definition eq_pureMap (m:Type -> Type) (c d:Pure.class_of m) :=
  forall A, @eta (Pure.Pack c) A =1 @eta (Pure.Pack d) _.

Section Pure_canonicals.
  (* id *)
  Definition id_pure_class_of : Pure.class_of id := Pure.Class (fun A x => x).
  Definition id_pureMap : pureMap :=
    Eval hnf in @Pure.Pack id id_pure_class_of.

  (* comp *)
  Definition comp_pure_class_of (m n:pureMap) :
    Pure.class_of (fun A => m (n A)) :=
    Pure.Class (fun _ => (@eta m _ \o @eta n _)).
  Definition comp_pureMap (m n:pureMap) : pureMap :=
    Eval hnf in @Pure.Pack (fun A => m (n A)) (comp_pure_class_of m n).

  Definition eta_comp m n :
    @eta (comp_pureMap m n) = fun _ => @eta m _ \o @eta n _ := erefl.

  (* option *)
  Definition option_pure_class_of : Pure.class_of option :=
    Pure.Class (@Some).
  Canonical option_pureMap : pureMap :=
    Eval hnf in @Pure.Pack option option_pure_class_of.

  Definition eta_option : @eta option_pureMap = @Some := erefl.

  (* seq *)
  Definition seq_pure_class_of : Pure.class_of seq :=
    Pure.Class (fun _ x => [:: x]).
  Canonical seq_pureMap : pureMap :=
    Eval hnf in @Pure.Pack seq seq_pure_class_of.

  Definition eta_seq : @eta seq_pureMap = (fun _ x => [:: x]) := erefl.

  (* sumt *)
  Definition sumt_pure_class_of R (m:pureMap) : Pure.class_of (sumt R m) :=
    Pure.Class (fun _ x => eta m (inr x)).
  Canonical sumt_pureMap R (m:pureMap) : pureMap :=
    Eval hnf in @Pure.Pack (sumt R m) (sumt_pure_class_of R m).

  Definition eta_sumt R (m:pureMap) :
    @eta (sumt_pureMap R m) = fun _ x => eta _ (inr x) := erefl.

  (* mult *)
  Definition mult_pure_class_of R (idx:R) (op:Monoid.law idx) (m:pureMap)
    : Pure.class_of (mult op m) :=
    Pure.Class (fun _ x => eta _ (idx,x)).
  Canonical mult_pureMap a (idx:a) (op:Monoid.law idx) (m:pureMap) : pureMap :=
    Eval hnf in @Pure.Pack (mult op m) (mult_pure_class_of op m).

  Definition eta_mult R (idx:R) (op:Monoid.law idx) (m:pureMap):
    @eta (mult_pureMap op m) = fun _ x => eta _ (idx,x) := erefl.

  (* appt *)
  Definition appt_pure_class_of R (m:pureMap) : Pure.class_of (appt R m) :=
    Pure.Class (fun _ x _ => eta _ x).
  Canonical appt_pureMap R (m:pureMap) : pureMap :=
    Eval hnf in @Pure.Pack (appt R m) (appt_pure_class_of R m).

  Definition eta_appt R (m:pureMap) :
    @eta (appt_pureMap R m) = fun _ x _ => eta _ x := erefl.

  (* statet *)
  Definition statet_pure_class_of R (m:pureMap) : Pure.class_of (statet R m) :=
    Pure.Class (fun _ x r => eta _ (r,x)).
  Canonical statet_pureMap R (m:pureMap) : pureMap :=
    Eval hnf in @Pure.Pack (statet R m) (statet_pure_class_of R m).

  Definition eta_statet R (m:pureMap) :
    @eta (statet_pureMap R m) = fun _ x r => eta _ (r,x) := erefl.
End Pure_canonicals.

(* ********************* *)

Module Functor.
  Definition Functor (m:Type -> Type) := forall A B, (A -> B) -> m A -> m B.

  Record class_of (m:Type -> Type) :=
    Class {
        functor : Functor m;
        _: forall A B (f g:A -> B), f =1 g -> functor f =1 functor g;
        _: forall A x, functor (@id A) x = x;
        _: forall A B C (f:B -> C) (g:A -> B) x,
            functor (f \o g) x = functor f (functor g x)
      }.

  Section ClassDef.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
  End ClassDef.

  Module Exports.
    Coercion apply : map >-> Funclass.
    Notation functorMap := map.
    Notation Functor := Functor.
    Definition functor T := (functor (class T)).
  End Exports.
End Functor.
Import Functor.Exports.

Section Functor_lemma.
  Variable (m : functorMap).

  Lemma eq_functor : forall A B (f g:A -> B),
      f =1 g -> @functor m _ _ f =1 functor g.
  Proof. by case : m => func []. Qed.

  Lemma functor_id : forall A (x:m A), functor (@id A) x = x.
  Proof. by case : m => func []. Qed.

  Lemma functorD : forall A B C (f:B -> C) (g:A -> B) (x:m A),
      functor (f \o g) x = functor f (functor g x).
  Proof. by case : m => func []. Qed.

  Lemma eq_functor_id A (f:A -> A) :
    f =1 id -> @functor m _ _ f =1 id.
  Proof. move /eq_functor => e x. by rewrite e functor_id. Qed.
End Functor_lemma.

Definition eq_functorMap (m:Type -> Type) (c d:Functor.class_of m) :=
  forall A B,
    @functor (Functor.Pack c) A B =2 @functor (Functor.Pack d) _ _.

Section Functor_canonicals.
  (* id *)
  Definition id_functor_class_of : Functor.class_of id.
  Proof. exact : (@Functor.Class _ (fun _ _ => id)). Defined.
  Definition id_functorMap : functorMap :=
    Eval hnf in @Functor.Pack id id_functor_class_of.

  (* comp *)
  Definition comp_functor_class_of (m n:functorMap) :
    Functor.class_of (fun A => m (n A)).
  Proof.
    apply : (@Functor.Class _ (fun _ _ => @functor m _ _ \o @functor n _ _))
    =>[A B f g fg|A x|A B C f g x]/=.
    - by do 2! apply : eq_functor.
    - apply : eq_functor_id. exact : functor_id.
    - rewrite -functorD. apply : eq_functor => y. exact : functorD.
  Defined.
  Definition comp_functorMap (m n:functorMap) : functorMap :=
    Eval hnf in @Functor.Pack (fun A => m (n A)) (comp_functor_class_of m n).

  Definition functor_comp m n :
    @functor (comp_functorMap m n) =
    fun _ _ => @functor m _ _ \o @functor n _ _ := erefl.

  (* option *)
  Definition option_functor_class_of : Functor.class_of option.
  Proof.
    apply : (@Functor.Class
               _ (fun _ _ f o => if o is Some x then Some (f x) else None))
    =>[A B f g fg [x|]|A [x|]|A B C f g [x|]]//.
      by rewrite fg.
  Defined.
  Canonical option_functorMap : functorMap :=
    Eval hnf in @Functor.Pack option option_functor_class_of.

  Lemma functor_option :
    @functor option_functorMap =
    fun _ _ f o => if o is Some x then Some (f x) else None.
  Proof. done. Qed.

  Lemma seq_functor_class_of : Functor.class_of seq.
  Proof.
    apply : (@Functor.Class _ (@map)).
    - exact : eq_map.
    - exact : map_id.
    - exact : map_comp.
  Defined.
  Canonical seq_functorMap : functorMap :=
    Eval hnf in @Functor.Pack seq seq_functor_class_of.

  Definition functor_seq : @functor seq_functorMap = @map := erefl.

  (* sumt *)
  Definition sumt_functor_class_of R (m:functorMap):
    Functor.class_of (sumt R m).
  Proof.
    apply : (@Functor.Class
               _ (fun _ _ f => functor (fun x => match x with
                                                 | inl a => inl a
                                                 | inr x => inr (f x)
                                                 end)))
    =>[A B f g fg|A x|A B C f g x]/=.
    - apply : eq_functor =>[[|x]]//. by rewrite fg.
    - by apply : eq_functor_id =>[[]].
    - rewrite -functorD. by apply : eq_functor =>[[]].
  Defined.
  Canonical sumt_functorMap R (m:functorMap) : functorMap :=
    Eval hnf in @Functor.Pack (sumt R m) (sumt_functor_class_of R m).

  Definition functor_sumt R m:
    @functor (sumt_functorMap R m) =
    fun _ _ f => functor (fun x => match x with
                                   | inl a => inl a
                                   | inr x => inr (f x)
                                   end) := erefl.

  (* mult *)
  Definition mult_functor_class_of R (idx:R) (op:Monoid.law idx) (m:functorMap):
    Functor.class_of (mult op m).
  Proof.
    apply : (@Functor.Class
               _ (fun _ _ f => functor (fun rx => match rx with
                                                    (r,x) => (r,f x)
                                                  end)))
    =>[A B f g fg|A x|A B C f g x].
    - apply : eq_functor =>[[r x]]. by rewrite fg.
    - by apply : eq_functor_id =>[[]].
    - rewrite -functorD. by apply : eq_functor =>[[]].
  Defined.
  Canonical mult_functorMap R (idx:R) (op:Monoid.law idx) (m:functorMap) :
    functorMap :=
    Eval hnf in @Functor.Pack (mult op m) (mult_functor_class_of op m).

  Definition functor_mult R (idx:R) (op:Monoid.law idx) m:
    @functor (mult_functorMap op m) =
    fun _ _ f => functor (fun rx => match rx with (r,x) => (r,f x) end)
  := erefl.

  (* appt *)
  (* needed functional extensionality *)
(*
  Definition appt_functor_class_of R (m:functorMap):
    Functor.class_of (appt R m).
  Proof.
    apply : (@Functor.Class _ (fun _ _ f xf x => functor f (xf x)))
    =>[A B f g fg xf||].
*)
End Functor_canonicals.

(* ********************* *)

Module WPFunctor.
  Section ClassDef.
    Record class_of (m:Type -> Type) :=
      Class {
          pBase : Pure.class_of m;
          fBase : Functor.class_of m
        }.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (pBase class).
    Definition functorMap := Functor.Pack (fBase class).
  End ClassDef.

  Module Exports.
    Coercion pBase : class_of >-> Pure.class_of.
    Coercion fBase : class_of >-> Functor.class_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Notation wpfunctorMap := map.
  End Exports.
End WPFunctor.
Import WPFunctor.Exports.

Section WPFunctor_lemma.
  Variable (m : wpfunctorMap).
End WPFunctor_lemma.

Definition eq_wpfunctorMap (m:Type -> Type) (c d:WPFunctor.class_of m) :=
  eq_pureMap c d /\ eq_functorMap c d.

Section WPFunctor_canonicals.
  (* id *)
  Definition id_wpfunctor_class_of : WPFunctor.class_of id :=
    WPFunctor.Class id_pure_class_of id_functor_class_of.
  Definition id_wpfunctorMap : wpfunctorMap :=
    Eval hnf in @WPFunctor.Pack id id_wpfunctor_class_of.

  (* comp *)
  Definition comp_wpfunctor_class_of (m n:wpfunctorMap) :
    WPFunctor.class_of (fun A => m (n A)) :=
    WPFunctor.Class (comp_pure_class_of m n) (comp_functor_class_of m n).
  Definition comp_wpfunctorMap (m n:wpfunctorMap) : wpfunctorMap :=
    Eval hnf in @WPFunctor.Pack (fun A => m (n A))
                                (comp_wpfunctor_class_of m n).

  (* option *)
  Definition option_wpfunctor_class_of : WPFunctor.class_of option :=
    WPFunctor.Class option_pure_class_of option_functor_class_of.
  Canonical option_wpfunctorMap : wpfunctorMap :=
    Eval hnf in @WPFunctor.Pack option option_wpfunctor_class_of.

  (* seq *)
  Definition seq_wpfunctor_class_of : WPFunctor.class_of seq :=
    WPFunctor.Class seq_pure_class_of seq_functor_class_of.
  Canonical seq_wpfunctorMap : wpfunctorMap :=
    Eval hnf in @WPFunctor.Pack seq seq_wpfunctor_class_of.

  (* sumt *)
  Definition sumt_wpfunctor_class_of R (m:wpfunctorMap) :
    WPFunctor.class_of (sumt R m) :=
    WPFunctor.Class (sumt_pure_class_of R m) (sumt_functor_class_of R m).
  Canonical sumt_wpfunctorMap R (m:wpfunctorMap): wpfunctorMap :=
    Eval hnf in @WPFunctor.Pack (sumt R m) (sumt_wpfunctor_class_of R m).

  (* mult *)
  Definition mult_wpfunctor_class_of R (idx:R) (op:Monoid.law idx)
             (m:wpfunctorMap) : WPFunctor.class_of (mult op m) :=
    WPFunctor.Class (mult_pure_class_of op m) (mult_functor_class_of op m).
  Definition mult_wpfunctorMap R (idx:R) (op:Monoid.law idx) (m:wpfunctorMap)
    : wpfunctorMap :=
    Eval hnf in @WPFunctor.Pack (mult op m) (mult_wpfunctor_class_of op m).
End WPFunctor_canonicals.

(* ********************* *)

Module PFunctor.
  Record mixin_of (m:wpfunctorMap) :=
    Mixin {
        _: forall A B (f:A -> B) x,
          functor f (eta m x) = eta _ (f x);        
      }.
  Section ClassDef.
    Record class_of (m:Type -> Type) :=
      Class {
          base : WPFunctor.class_of m;
          mixin : mixin_of (WPFunctor.Pack base)
        }.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> WPFunctor.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Notation pfunctorMap := map.
  End Exports.
End PFunctor.
Import PFunctor.Exports.

Section PFunctor_lemma.
  Variable (m:pfunctorMap).
  Let eta := eta m.

  Lemma functor_eta : forall A B (f:A -> B) x,
      functor f (eta x) = eta (f x).
  Proof. rewrite /eta. by case m => func [b []]. Qed.
End PFunctor_lemma.

Definition eq_pfunctorMap (m:Type -> Type) (c d:PFunctor.class_of m) :=
  eq_wpfunctorMap c d.

Section PFunctor_canonicals.
  (* id *)
  Definition id_pfunctor_mixin_of : PFunctor.mixin_of id_wpfunctorMap.
  Proof. exact : PFunctor.Mixin. Defined.
  Definition id_pfunctor_class_of : PFunctor.class_of id :=
    PFunctor.Class id_pfunctor_mixin_of.
  Definition id_pfunctorMap : pfunctorMap :=
    Eval hnf in @PFunctor.Pack id id_pfunctor_class_of.

  (* comp *)
  Definition comp_pfunctor_mixin_of (m n:pfunctorMap) :
    PFunctor.mixin_of (comp_wpfunctorMap m n).
  Proof.
    apply : PFunctor.Mixin =>[A B f x].
      by rewrite functor_comp /= !functor_eta.
  Defined.
  Definition comp_pfunctor_class_of (m n:pfunctorMap) :
    PFunctor.class_of (fun A => m (n A)) :=
    PFunctor.Class (comp_pfunctor_mixin_of m n).
  Definition comp_pfunctorMap (m n:pfunctorMap) : pfunctorMap :=
    Eval hnf in @PFunctor.Pack (fun A => m (n A)) (comp_pfunctor_class_of m n).

  (* option *)
  Definition option_pfunctor_mixin_of : PFunctor.mixin_of option_wpfunctorMap.
  Proof. exact : PFunctor.Mixin. Defined.
  Definition option_pfunctor_class_of : PFunctor.class_of option :=
    PFunctor.Class option_pfunctor_mixin_of.
  Canonical option_pfunctorMap : pfunctorMap :=
    Eval hnf in @PFunctor.Pack option option_pfunctor_class_of.

  (* seq *)
  Definition seq_pfunctor_mixin_of : PFunctor.mixin_of seq_wpfunctorMap.
  Proof. exact : PFunctor.Mixin. Defined.
  Definition seq_pfunctor_class_of : PFunctor.class_of seq :=
    PFunctor.Class seq_pfunctor_mixin_of.
  Canonical seq_pfunctorMap : pfunctorMap :=
    Eval hnf in @PFunctor.Pack seq seq_pfunctor_class_of.

  (* sumt *)
  Definition sumt_pfunctor_mixin_of R (m:pfunctorMap) :
    PFunctor.mixin_of (sumt_wpfunctorMap R m).
  Proof.
    apply : PFunctor.Mixin =>[A B f x].
      by rewrite functor_sumt functor_eta.
  Defined.
  Definition sumt_pfunctor_class_of R (m:pfunctorMap) :
    PFunctor.class_of (sumt R m) :=
    PFunctor.Class (sumt_pfunctor_mixin_of R m).
  Canonical sumt_pfunctorMap R (m:pfunctorMap): pfunctorMap :=
    Eval hnf in @PFunctor.Pack (sumt R m) (sumt_pfunctor_class_of R m).

  (* mult *)
  Definition mult_pfunctor_mixin_of R (idx:R) (op:Monoid.law idx)
             (m:pfunctorMap):
    PFunctor.mixin_of (mult_wpfunctorMap op m).
  Proof.
    apply : PFunctor.Mixin =>[A B f x].
      by rewrite functor_mult functor_eta.
  Defined.
  Definition mult_pfunctor_class_of R (idx:R) (op:Monoid.law idx)
             (m:pfunctorMap) : PFunctor.class_of (mult op m) :=
    PFunctor.Class (mult_pfunctor_mixin_of op m).
  Definition mult_pfunctorMap R (idx:R) (op:Monoid.law idx) (m:pfunctorMap)
    : pfunctorMap :=
    Eval hnf in @PFunctor.Pack (mult op m) (mult_pfunctor_class_of op m).
End PFunctor_canonicals.

(* ********************* *)

Module Functor2.
  Definition Functor2 (m:Type -> Type)
    := forall A B C, (A -> B -> C) -> m A -> m B -> m C.
  Definition Applicative (m:Type -> Type)
    := forall A B, m (A -> B) -> m A -> m B.
(*
  Record mixin_of (m:pfunctorMap) :=
    Mixin {
        applicative : Applicative m;
        _: forall A B (f:A -> B),
            applicative (eta _ f) =1 functor f;
        _: forall A B C (f g:A -> B -> C),
            f =2 g ->
            forall x, applicative (functor f x) =1 applicative (functor g x);
        _: forall A B C D (f g:A -> B -> C -> D),
            (forall x, f x =2 g x) ->
            forall x y, applicative (applicative (functor f x) y)
                        =1 applicative (applicative (functor g x) y);
        _: forall A B C (f:m (B -> C)) (g:m (A -> B)) x,
            applicative (applicative (applicative (eta _ comp) f) g) x =
            applicative f (applicative g x);
        _: forall A B (f:m (A -> B)) x,
            applicative f (eta _ x) = functor (@^~ x) f
      }.
*)
  Record mixin_of (m:pfunctorMap) :=
    Mixin {
        functor2:Functor2 m;
        _:forall A B C D (f g:A -> B -> C -> D),
            (forall x, f x =2 g x) ->
            forall x y, functor2 id (functor2 f x y)
                        =1 functor2 id (functor2 g x y);
        _:forall A B C (f:A -> B -> C) x,
            functor2 f (eta _ x) =1 functor (f x);
        _:forall A B C (f:A -> B -> C) x y,
            functor2 f x (eta _ y) = functor (f^~ y) x;
        _:forall A B C D (f:B -> C -> D) (g:A -> B) x,
            functor2 (f \o g) x =1 functor2 f (functor g x);
        _:forall A B C D E (f:C -> D -> E) (g:A -> B -> C) x y z,
            functor2 id (functor2 (fun x => f \o g x) x y) z
            = functor2 f (functor2 g x y) z;
        _:forall A B C D E (f:A -> D -> E) (g:B -> C -> D) x y z,
            functor2 id (functor2 (fun x y => f x \o g y) x y) z
            = functor2 f x (functor2 g y z)
      }.

  Section ClassDef.
    Record class_of (m:Type -> Type) :=
      Class {
          base : PFunctor.class_of m;
          mixin : mixin_of (PFunctor.Pack base)
        }.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> PFunctor.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Notation functor2Map := map.
    Notation Applicative := Applicative.
    Notation Functor2 := Functor2.
    Definition functor2 T := (functor2 (class T)).
  End Exports.
End Functor2.
Import Functor2.Exports.

Section Functor2_lemma.
  Variable (m:functor2Map).
  Let eta := eta m.

  Definition functor3 A B C D (f:A -> B -> C -> D)
             (x:m A) (y:m B) : m C -> m D := functor2 id (functor2 f x y).

  Lemma eq_functor3 A B C D (f g:A -> B -> C -> D):
    (forall x, f x =2 g x) -> forall (x:m A), functor3 f x =2 functor3 g x.
  Proof.
    rewrite /functor3 /functor2. case : m => func [b [F H e0 e1 e2 e3 e4]].
    exact : H.
  Qed.

  Lemma functor2_etal A B C (f:A -> B -> C):
    forall x, functor2 f (eta x) =1 functor (f x).
  Proof.
    rewrite /functor2 /eta. case : m => func [b [F e0 H e1 e2 e3 e4]].
    exact : H.
  Qed.

  Lemma functor2_etar A B C (f:A -> B -> C):
    forall x y, functor2 f x (eta y) = functor (f^~ y) x.
  Proof.
    rewrite /functor2 /eta. case : m => func [b [F e0 e1 H e2 e3 e4]].
    exact : H.
  Qed.

  Lemma functor2D A B C D (f:B -> C -> D) (g:A -> B):
     forall (x:m A), functor2 (f \o g) x =1 functor2 f (functor g x).
  Proof.
    rewrite /functor2. case : m => func [b [F e0 e1 e2 H e3 e4]].
    exact : H.
  Qed.

  Lemma functor3Dl A B C D E (f:C -> D -> E) (g:A -> B -> C):
    forall x y, functor3 (fun x => f \o g x) x y =1 functor2 f (functor2 g x y).
  Proof.
    rewrite /functor3 /functor2 /eta.
    case : m => func [b [F e0 e1 e2 e3 H e4]]. exact : H.
  Qed.

  Lemma functor3Dr A B C D E (f:A -> D -> E) (g:B -> C -> D):
    forall x y z,
      functor3 (fun x y => f x \o g y) x y z = functor2 f x (functor2 g y z).
  Proof.
    rewrite /functor3 /functor2 /eta.
    case : m => func [b [F e0 e1 e2 e3 e4 H]]. exact : H.
  Qed.

  Lemma functor_def A B (f:A -> B):
    functor f =1 functor2 (fun => f) (eta tt).
  Proof. move => x. by rewrite functor2_etal. Qed.

  Lemma functor3_eta1 A B C D (f:A -> B -> C -> D) x:
    functor3 f (eta x) =2 functor2 (f x).
  Proof. rewrite /functor3 => y z. by rewrite functor2_etal -functor2D. Qed.

  Lemma functor3_eta2 A B C D (f:A -> B -> C -> D) x y:
    functor3 f x (eta y) =1 functor2 (f^~ y) x.
  Proof. move => z. by rewrite /functor3 functor2_etar -functor2D. Qed.

  Lemma functor2_def A B C (f:A -> B -> C):
    functor2 f =2 functor3 (fun => f) (eta tt).
  Proof. move => x y. by rewrite functor3_eta1. Qed.

  Lemma eq_functor2 A B C (f g:A -> B -> C):
    f =2 g -> @functor2 m _ _ _ f =2 functor2 g.
  Proof.
    move => H x y. rewrite !functor2_def. exact : eq_functor3.
  Qed.
  
  Lemma functor2Dr A B C D (f:C -> D) (g:A -> B -> C) (x:m A) y:
    functor2 (fun x => f \o g x) x y = functor f (functor2 g x y).
  Proof. by rewrite functor_def -functor3Dr functor3_eta1. Qed.

  Lemma functor3_eta3 A B C D (f:A -> B -> C -> D) x y z:
    functor3 f x y (eta z) = functor2 (fun x y => f x y z) x y.
  Proof. by rewrite /functor3 functor2_etar -functor2Dr. Qed.

  Lemma functor2Dl A B C D (f:A -> C -> D) (g:B -> C) (x:m A) y:
    functor2 (fun x => f x \o g) x y = functor2 f x (functor g y).
  Proof. by rewrite functor_def -functor3Dr functor3_eta2. Qed.


  (* applicative *)
  Definition applicative : Applicative m := fun A B => functor2 (@id (A -> B)).

  Lemma applicative_etal A B (f:A -> B) : applicative (eta f) =1 functor f.
  Proof. exact : functor2_etal. Qed.

  Lemma applicative_etar A B (f:m (A -> B)) x:
      applicative f (eta x) = functor (@^~ x) f.
  Proof. exact : functor2_etar. Qed.

  Lemma applicativeA A B C (f:m (B -> C)) (g:m (A -> B)) x:
      applicative (applicative (applicative (eta comp) f) g) x =
      applicative f (applicative g x).
  Proof.
      by rewrite /applicative functor2_etal -functor2D -functor3Dl functor3Dr.
  Qed.
End Functor2_lemma.

Definition eq_functor2Map (m:Type -> Type) (c d:Functor2.class_of m) :=
  eq_pfunctorMap c d /\
  forall A B C f, @functor2 (Functor2.Pack c) A B C f
                =2 @functor2 (Functor2.Pack d) _ _ _ f.

Section Functor2_canonicals.
  (* id *)
  Definition id_functor2_mixin_of : Functor2.mixin_of id_pfunctorMap.
  Proof.
    exact : (@Functor2.Mixin
               _ ((fun _ _ _ => id) : Functor2 id_pfunctorMap)).
  Defined.
  Definition id_functor2_class_of : Functor2.class_of id :=
    Functor2.Class id_functor2_mixin_of.
  Definition id_functor2Map : functor2Map :=
    Eval hnf in @Functor2.Pack id id_functor2_class_of.

  (* comp *)
  Definition comp_functor2_mixin_of (m n:functor2Map) :
    Functor2.mixin_of (comp_pfunctorMap m n).
  Proof.
    apply : (@Functor2.Mixin
               _ ((fun _ _ _ f => functor2 (functor2 f))
                  : Functor2 (comp_pfunctorMap _ _)))
    =>[A B C D f g H x y z|A B C f x y|A B C f x y|A B C f g x y z|
       A B C D E f g x y z|A B C D E f g x y z].
    - rewrite -!functor3Dl. apply : eq_functor3. exact : (eq_functor3 H).
    - rewrite eta_comp functor2_etal /=. apply : eq_functor => z.
      exact : functor2_etal.
    - rewrite eta_comp functor2_etar /=. apply : eq_functor => z.
      exact : functor2_etar.
    - rewrite functor_comp -functor2D. apply : eq_functor2 => v w /=.
      exact : functor2D.
    - rewrite -!functor3Dl. apply : eq_functor3. exact : functor3Dl.
    - rewrite -functor3Dl -functor3Dr. apply : eq_functor3. exact : functor3Dr.
  Defined.
  Definition comp_functor2_class_of (m n:functor2Map) :
    Functor2.class_of (fun A => m (n A)) :=
    Functor2.Class (comp_functor2_mixin_of m n).
  Definition comp_functor2Map (m n:functor2Map) : functor2Map :=
    Eval hnf in @Functor2.Pack
                  (fun A => m (n A)) (comp_functor2_class_of m n).

  Definition functor2_comp (m n:functor2Map):
    @functor2 (comp_functor2Map m n) = fun _ _ _ f => functor2 (functor2 f)
    := erefl.
  Lemma functor3_comp (m n:functor2Map) A B C D f x:
    @functor3 (comp_functor2Map m n) A B C D f x =2 functor3 (functor3 f) x.
  Proof.
    move => y z. by rewrite /functor3 functor2_comp -!functor3Dl.
  Qed.
  Definition applicative_comp (m n:functor2Map):
    @applicative (comp_functor2Map m n) =
    fun _ _ => functor2 (@applicative _ _ _) := erefl.

  (* option *)
  Definition option_functor2_mixin_of: Functor2.mixin_of option_pfunctorMap.
  Proof.
    apply : (@Functor2.Mixin
               _ (fun _ _ _ f ox oy
                  => if ox is Some x then
                       if oy is Some y then Some (f x y) else None else None))
    =>[A B C D f g H [x|][y|][z|]|||A B C D f g [x|]|A B C D E f g [x|][y|]|
       A B C D E f g [x|][y|][z|]]//. by rewrite H.
  Defined.
  Definition option_functor2_class_of : @Functor2.class_of option :=
    Functor2.Class option_functor2_mixin_of.
  Canonical option_functor2Map : functor2Map :=
    Eval hnf in @Functor2.Pack option option_functor2_class_of.

  Definition functor2_option :
    @functor2 option_functor2Map =
    fun _ _ _ f ox oy
                  => if ox is Some x then
                       if oy is Some y then Some (f x y) else None else None
    := erefl.
  Lemma functor3_option A B C D f:
    @functor3 option_functor2Map A B C D f
    =2 fun ox oy oz => if ox is Some x
                    then if oy is Some y then if oz is Some z
                                              then Some (f x y z) else None
                         else None
                    else None.
  Proof. by case =>[x|][y|]. Qed.
  Definition applicative_option :
    @applicative option_functor2Map =
    fun _ _ oF ox => if oF is Some f
                     then if ox is Some x then Some (f x) else None
                     else None := erefl.

  (* seq *)
  Definition seq_hfunctor2_mixin_of: Functor2.mixin_of seq_pfunctorMap.
  Proof.
    apply : (@Functor2.Mixin
              _ (fun _ _ _ f s t => [seq f x y | x <- s, y <- t]))
    =>[A B C D f g H s t u|A B C f s t|A B C f s t|A B C D f g s t|
       A B C D E f g s t u|A B C D E f g s t u].
    - elim : s =>[|x s IH]//=. rewrite !allpairs_cat IH !allpairs_mapl.
        by rewrite (eq_allpairs _ _ (H x)).
    - exact : allpairs1l.
    - exact : allpairs1r.
    - by rewrite allpairs_mapl.
    - by rewrite -map_allpairs allpairs_mapl.
    - elim : s =>[|x s IH]//=. rewrite !allpairs_cat IH allpairs_mapl.
        by rewrite map_allpairs.
  Defined.
  Definition seq_hfunctor2_class_of : @Functor2.class_of seq :=
    Functor2.Class seq_hfunctor2_mixin_of.
  Definition seq_hfunctor2Map : functor2Map :=
    Eval hnf in @Functor2.Pack seq seq_hfunctor2_class_of.

  Definition hfunctor2_seq :
    @functor2 seq_hfunctor2Map =
    fun _ _ _ f s t => [seq f x y | x <- s, y <- t] := erefl.
  Definition hfunctor3_seq :
    @functor3 seq_hfunctor2Map =
    fun _ _ _ _ f s t u =>
      [seq g z | g <- [seq f x y | x <- s, y <- t], z <- u] := erefl.
  Definition happlicative_seq :
    @applicative seq_hfunctor2Map =
    fun _ _ s t => [seq f x | f <- s, x <- t] := erefl.

  Definition seq_vfunctor2_mixin_of: Functor2.mixin_of seq_pfunctorMap.
  Proof.
    apply : (@Functor2.Mixin
              _ (fun _ _ _ f s t => [seq f x y | y <- t, x <- s]))
    =>[A B C D f g H s t u|A B C f s t|A B C f s t|A B C D f g s t|
       A B C D E f g s t u|A B C D E f g s t u].
    - elim : u =>[|y u IH]//=. rewrite IH !map_allpairs.
        by rewrite (eq_allpairs _ _ (fun _ _ => H _ _ y)).
    - exact : allpairs1r.
    - exact : allpairs1l.
    - by rewrite allpairs_mapr.
    - by rewrite -map_allpairs allpairs_mapr.
    - elim : u =>[|y u IH]//=. rewrite allpairs_cat IH allpairs_mapl.
        by rewrite map_allpairs.
  Defined.
  Definition seq_vfunctor2_class_of : @Functor2.class_of seq :=
    Functor2.Class seq_vfunctor2_mixin_of.
  Definition seq_vfunctor2Map : functor2Map :=
    Eval hnf in @Functor2.Pack seq seq_vfunctor2_class_of.

  Definition vfunctor2_seq :
    @functor2 seq_vfunctor2Map =
    fun _ _ _ f s t => [seq f x y | y <- t, x <- s] := erefl.
  Definition vfunctor3_seq :
    @functor3 seq_vfunctor2Map =
    fun _ _ _ _ f s t u => [seq g z | z <- u, g <- [seq f x y | y <- t,x <- s]]
  := erefl.
  Definition vapplicative_seq :
    @applicative seq_vfunctor2Map =
    fun _ _ s t => [seq f x | x <- t, f <- s] := erefl.

  (* sumt *)
  Definition sumt_hfunctor2_mixin_of R (m:functor2Map):
    Functor2.mixin_of (sumt_pfunctorMap R m).
  Proof.
    apply : (@Functor2.Mixin
               _ ((fun _ _ _ f => functor2
                                   (fun rx ry =>
                                      match rx,ry with
                                      | inl a,_ => inl a
                                      | inr x,inl b => inl b
                                      | inr x,inr y => inr (f x y)
                                      end)) : Functor2 (sumt_pfunctorMap R m)))
    =>[A B C D f g H x y z|A B C f x y|A B C f x y|A B C D f g x y|
       A B C D E f g x y z|A B C D E f g x y z].
    - rewrite -!functor3Dl. apply : eq_functor3 =>[[a|r][b|t][c|s]]//=.
        by rewrite H.
    - by rewrite eta_sumt functor2_etal.
    - by rewrite eta_sumt functor2_etar.
    - rewrite -functor2D. by apply : eq_functor2 =>[[a|r]].
    - rewrite -!functor3Dl. by apply : eq_functor3 =>[[a|r][b|t]].
    - rewrite -functor3Dl -functor3Dr.
        by apply : eq_functor3 =>[[a|r][b|t][c|s]].
  Defined.
  Definition sumt_hfunctor2_class_of R (m:functor2Map) :
    @Functor2.class_of (sumt R m) :=
    Functor2.Class (sumt_hfunctor2_mixin_of R m).
  Definition sumt_hfunctor2Map R (m:functor2Map) : functor2Map :=
    Eval hnf in @Functor2.Pack (sumt R m) (sumt_hfunctor2_class_of R m).

  Definition hfunctor2_sumt R m :
    @functor2 (sumt_hfunctor2Map R m) =
    fun _ _ _ f => functor2
                     (fun rx ry =>
                        match rx,ry with
                        | inl a,_ => inl a
                        | inr x,inl b => inl b
                        | inr x,inr y => inr (f x y)
                        end) := erefl.
  Lemma hfunctor3_sumt R m A B C D f x:
    @functor3 (sumt_hfunctor2Map R m) A B C D f x =2
      functor3 (fun rx ry rz =>
                  match rx,ry,rz with
                  | inl a,_,_ => inl a
                  | inr x,inl b,_ => inl b
                  | inr x,inr y,inl c => inl c
                  | inr x,inr y,inr z => inr (f x y z)
                  end) x.
  Proof.
    move => y z. rewrite /functor3 hfunctor2_sumt -!functor3Dl /=.
      by apply : eq_functor3 =>[[a|xx][b|yy]]//.
  Qed.
  Definition happlicative_sumt R m :
    @applicative (sumt_hfunctor2Map R m) =
        fun _ _ => functor2
                     (fun rf rx =>
                        match rf,rx with
                        | inl a,_ => inl a
                        | inr f,inl b => inl b
                        | inr f,inr x => inr (f x)
                        end) := erefl.

  Definition sumt_vfunctor2_mixin_of R (m:functor2Map):
    Functor2.mixin_of (sumt_pfunctorMap R m).
  Proof.
    apply : (@Functor2.Mixin
               _ ((fun _ _ _ f => functor2
                                   (fun rx ry =>
                                      match rx,ry with
                                      | _,inl b => inl b
                                      | inl a,inr y => inl a
                                      | inr x,inr y => inr (f x y)
                                      end)) : Functor2 (sumt_pfunctorMap R m)))
    =>[A B C D f g H x y z|A B C f x y|A B C f x y|A B C D f g x y|
       A B C D E f g x y z|A B C D E f g x y z].
    - rewrite -!functor3Dl. apply : eq_functor3 =>[[a|r][b|t][c|s]]//=.
        by rewrite H.
    - by rewrite eta_sumt functor2_etal.
    - by rewrite eta_sumt functor2_etar.
    - rewrite -functor2D. by apply : eq_functor2 =>[[a|r]].
    - rewrite -!functor3Dl. by apply : eq_functor3 =>[[a|r][b|t]].
    - rewrite -functor3Dl -functor3Dr.
        by apply : eq_functor3 =>[[a|r][b|t][c|s]].
  Defined.
  Definition sumt_vfunctor2_class_of R (m:functor2Map) :
    @Functor2.class_of (sumt R m) :=
    Functor2.Class (sumt_vfunctor2_mixin_of R m).
  Definition sumt_vfunctor2Map R (m:functor2Map) : functor2Map :=
    Eval hnf in @Functor2.Pack (sumt R m) (sumt_vfunctor2_class_of R m).

  Definition vfunctor2_sumt R m :
    @functor2 (sumt_vfunctor2Map R m) =
    fun _ _ _ f => functor2
                     (fun rx ry =>
                        match rx,ry with
                        | _,inl b => inl b
                        | inl a,inr y => inl a
                        | inr x,inr y => inr (f x y)
                        end) := erefl.
  Lemma vfunctor3_sumt R m A B C D f x:
    @functor3 (sumt_vfunctor2Map R m) A B C D f x =2
      functor3 (fun rx ry rz =>
                  match rx,ry,rz with
                  | _,_,inl c => inl c
                  | _,inl b,inr z => inl b
                  | inl a,inr y,inr z => inl a
                  | inr x,inr y,inr z => inr (f x y z)
                  end) x.
  Proof.
    move => y z. rewrite /functor3 vfunctor2_sumt -!functor3Dl /=.
      by apply : eq_functor3 =>[[a|xx][b|yy]]//.
  Qed.
  Definition vapplicative_sumt R m :
    @applicative (sumt_vfunctor2Map R m) =
        fun _ _ => functor2
                     (fun rf rx =>
                        match rf,rx with
                        | _,inl b => inl b
                        | inl a,inr x => inl a
                        | inr f,inr x => inr (f x)
                        end) := erefl.

  (* mult *)
  Definition mult_hfunctor2_mixin_of
             R (idx:R) (op:Monoid.law idx)(m:functor2Map):
    Functor2.mixin_of (mult_pfunctorMap op m).
  Proof.
    apply : (@Functor2.Mixin
               _ ((fun _ _ _ f => functor2
                                   (fun rx ry =>
                                      match rx,ry with
                                        (a,x),(b,y) => (op a b,f x y)
                                      end)) : Functor2 (mult_pfunctorMap op m)))
    =>[A B C D f g H x y z|A B C f x y|A B C f x y|A B C D f g x y|
       A B C D E f g x y z|A B C D E f g x y z].
    - rewrite -!functor3Dl. apply : eq_functor3 =>[[a r][b s][c t]]/=.
        by rewrite H.
    - rewrite eta_mult functor2_etal. apply : (@eq_functor m) =>[[a r]].
        by rewrite Monoid.mul1m.
    - rewrite eta_mult functor2_etar. apply : (@eq_functor m) =>[[a r]].
        by rewrite Monoid.mulm1.
    - rewrite functor_mult -functor2D.
        by apply : (@eq_functor2 m) =>[[a r]].
    - rewrite -!functor3Dl. by apply : (@eq_functor3 m) =>[[a r][b s]].
    - rewrite -functor3Dl -functor3Dr.
      apply : (@eq_functor3 m) =>[[a r][b s][c t]]/=. by rewrite Monoid.mulmA.
  Defined.
  Definition mult_hfunctor2_class_of
             R (idx:R) (op:Monoid.law idx) (m:functor2Map) :
    @Functor2.class_of (mult op m) :=
    Functor2.Class (mult_hfunctor2_mixin_of op m).
  Definition mult_hfunctor2Map
             R (idx:R) (op:Monoid.law idx) (m:functor2Map) : functor2Map :=
    Eval hnf in @Functor2.Pack (mult op m) (mult_hfunctor2_class_of op m).

  Definition hfunctor2_mult R (idx:R) (op:Monoid.law idx) m :
    @functor2 (mult_hfunctor2Map op m) =
    fun _ _ _ f => functor2
                     (fun rx ry =>
                        match rx,ry with
                          (a,x),(b,y) => (op a b,f x y)
                        end) := erefl.
  Lemma hfunctor3_mult R (idx:R) (op:Monoid.law idx) m A B C D f x:
    @functor3 (mult_hfunctor2Map op m) A B C D f x =2
     functor3
     (fun rx ry rz =>
        match rx,ry,rz with
        | (a,x),(b,y),(c,z) => (op (op a b) c,f x y z)
        end) x.
  Proof.
    move => y z. rewrite /functor3 hfunctor2_mult -functor3Dl.
    by apply : (@eq_functor3 m) =>[[a r][b t]].
  Qed.
  Definition happlicative_mult R (idx:R) (op:Monoid.law idx) m:
    @applicative (mult_hfunctor2Map op m) =
    fun _ _ => functor2
                     (fun rf rx =>
                        match rf,rx with
                          (a,f),(b,x) => (op a b,f x)
                        end) := erefl.

  Definition mult_vfunctor2_mixin_of
             R (idx:R) (op:Monoid.law idx)(m:functor2Map):
    Functor2.mixin_of (mult_pfunctorMap op m).
  Proof.
    apply : (@Functor2.Mixin
               _ ((fun _ _ _ f => functor2
                                   (fun rx ry =>
                                      match rx,ry with
                                        (a,x),(b,y) => (op b a,f x y)
                                      end)) : Functor2 (mult_pfunctorMap op m)))
    =>[A B C D f g H x y z|A B C f x y|A B C f x y|A B C D f g x y|
       A B C D E f g x y z|A B C D E f g x y z].
    - rewrite -!functor3Dl. apply : eq_functor3 =>[[a r][b s][c t]]/=.
        by rewrite H.
    - rewrite eta_mult functor2_etal. apply : (@eq_functor m) =>[[a r]].
        by rewrite Monoid.mulm1.
    - rewrite eta_mult functor2_etar. apply : (@eq_functor m) =>[[a r]].
        by rewrite Monoid.mul1m.
    - rewrite functor_mult -functor2D.
        by apply : (@eq_functor2 m) =>[[a r]].
    - rewrite -!functor3Dl. by apply : (@eq_functor3 m) =>[[a r][b s]].
    - rewrite -functor3Dl -functor3Dr.
      apply : (@eq_functor3 m) =>[[a r][b s][c t]]/=. by rewrite Monoid.mulmA.
  Defined.
  Definition mult_vfunctor2_class_of
             R (idx:R) (op:Monoid.law idx) (m:functor2Map) :
    @Functor2.class_of (mult op m) :=
    Functor2.Class (mult_vfunctor2_mixin_of op m).
  Definition mult_vfunctor2Map
             R (idx:R) (op:Monoid.law idx) (m:functor2Map) : functor2Map :=
    Eval hnf in @Functor2.Pack (mult op m) (mult_vfunctor2_class_of op m).

  Definition vfunctor2_mult R (idx:R) (op:Monoid.law idx) m :
    @functor2 (mult_vfunctor2Map op m) =
    fun _ _ _ f => functor2
                     (fun rx ry =>
                        match rx,ry with
                          (a,x),(b,y) => (op b a,f x y)
                        end) := erefl.
  Lemma vfunctor3_mult R (idx:R) (op:Monoid.law idx) m A B C D f x:
    @functor3 (mult_vfunctor2Map op m) A B C D f x =2
     functor3
     (fun rx ry rz =>
        match rx,ry,rz with
        | (a,x),(b,y),(c,z) => (op c (op b a),f x y z)
        end) x.
  Proof.
    move => y z. rewrite /functor3 vfunctor2_mult -functor3Dl.
    by apply : (@eq_functor3 m) =>[[a r][b t]].
  Qed.
  Definition vapplicative_mult R (idx:R) (op:Monoid.law idx) m:
    @applicative (mult_vfunctor2Map op m) =
    fun _ _ => functor2
                     (fun rf rx =>
                        match rf,rx with
                          (a,f),(b,x) => (op b a,f x)
                        end) := erefl.
End Functor2_canonicals.

(* ********************* *)

Module Monad.
  Definition Mu (m:Type -> Type) := forall A, m (m A) -> m A.

  Record mixin_of (m:wpfunctorMap) :=
    Mixin {
        mu : Mu m;
        _: forall A (x:m A), mu (eta _ x) = x;
        _: forall A x,
            mu (functor (@eta _ A) x) = x;
        _: forall A x,
            mu (functor (@mu A) x) = mu (mu x)
      }.
  Section ClassDef.
    Record class_of (m:Type -> Type) :=
      Class {
          base : WPFunctor.class_of m;
          mixin : mixin_of (WPFunctor.Pack base)
        }.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> WPFunctor.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Notation monadMap := map.
    Notation Mu := Mu.
    Definition mu T := (mu (class T)).
  End Exports.
End Monad.
Import Monad.Exports.

Section Monad_lemma.
  Variable (m : monadMap).
  Let eta := eta m.

  Lemma mu_eta : forall A (x:m A), mu (eta x) = x.
  Proof. rewrite /eta. by case : m => func [b []]. Qed.

  Lemma mu_functor_eta : forall A x, mu (functor (@eta A) x) = x.
  Proof. rewrite /eta. by case : m => func [b []]. Qed.

  Lemma mu_functor_mu : forall A x, mu (functor (@mu m A) x) = mu (mu x).
  Proof. rewrite /eta. by case : m => func [b []]. Qed.
End Monad_lemma.

Definition eq_monadMap (m:Type -> Type) (c d:Monad.class_of m) :=
  [/\ eq_pureMap c d, eq_functorMap c d &
   forall A, @mu (Monad.Pack c) A =1 @mu (Monad.Pack d) _].

Section Monad_canonicals.
  (* id *)
  Definition id_monad_mixin_of : Monad.mixin_of id_wpfunctorMap.
  Proof.
    exact : (@Monad.Mixin _ ((fun _ => id) : Mu id_wpfunctorMap)).
  Defined.
  Definition id_monad_class_of : Monad.class_of id :=
    Monad.Class id_monad_mixin_of.
  Definition id_monadMap : monadMap :=
    Eval hnf in @Monad.Pack id id_monad_class_of.

  (* option *)
  Definition option_monad_mixin_of : Monad.mixin_of option_wpfunctorMap.
  Proof.
      by apply : (@Monad.Mixin _  (fun _ o => if o is Some x then x else None))
      =>[A [x|]|A [x|]|A [x|]].
  Defined.
  Definition option_monad_class_of : Monad.class_of option :=
    Monad.Class option_monad_mixin_of.
  Canonical option_monadMap : monadMap :=
    Eval hnf in @Monad.Pack option option_monad_class_of.

  Definition mu_option :
    @mu option_monadMap = fun _ o => if o is Some x then x else None := erefl.

  (* seq *)
  Lemma seq_monad_mixin_of : Monad.mixin_of seq_wpfunctorMap.
  Proof.
    apply : (@Monad.Mixin _ (@flatten))=>/=[||A].
    - exact : cats0.
    - exact : flatten_seq1.
    - elim =>[|x s IHs]//=. by rewrite flatten_cat -IHs.
  Defined.
  Definition seq_monad_class_of : Monad.class_of seq :=
    Monad.Class seq_monad_mixin_of.
  Canonical seq_monadMap : monadMap :=
    Eval hnf in @Monad.Pack seq seq_monad_class_of.

  Definition mu_seq : @mu seq_monadMap = @flatten := erefl.
End Monad_canonicals.

Section Monad_applicative.
  Variable (m:monadMap).
  Definition hfunctor2 : Functor2 m :=
    fun A B C f x y => mu (functor (fun x => functor (f x) y) x).
  Definition vfunctor2 : Functor2 m :=
    fun A B C f x y => mu (functor (fun y => functor (f^~ y) x) y).
  Definition happlicative : Applicative m :=
    fun A B f x => mu (functor ((@functor _ _ _)^~ x) f).
  Definition vapplicative : Applicative m :=
    fun A B f x => mu (functor (fun y => functor (@^~ y) f) x).
End Monad_applicative.

Eval compute in (hfunctor2 addn [:: 1; 2] [:: 10; 20]).
(* = [:: 11; 21; 12; 22] *)
Eval compute in (vfunctor2 addn [:: 1; 2] [:: 10; 20]).
(* = [:: 11; 12; 21; 22] *)
Eval compute in (happlicative [:: (fun x => x.+1); (fun x =>x.+2)] [:: 10; 20]).
(* = [:: 11; 21; 12; 22] *)
Eval compute in (vapplicative [:: (fun x => x.+1); (fun x =>x.+2)] [:: 10; 20]).
(* = [:: 11; 12; 21; 22] *)

Section Monad_applicative_lemma.
  Definition eq_hvfunctor2 m :=
    forall A B C f, @hfunctor2 m A B C f =2 @vfunctor2 _ _ _ _ f.
  Definition eq_hvapplicative m :=
    forall A B, @happlicative m A B =2 @vapplicative _ _ _.

  Lemma eq_hvfunctor2P m:
    eq_hvfunctor2 m <-> eq_hvapplicative m.
  Proof.
    split.
    - move => H A B f x. move : (H _ A B id).
      by rewrite /hfunctor2/happlicative =>->.
    - rewrite /eq_hvapplicative /happlicative/vapplicative => H A B C f x y.
      rewrite /hfunctor2/vfunctor2.
      have -> : functor (fun z => functor (f^~ z) x) y =
                functor (fun z => functor (@^~ z) (functor f x)) y
        by apply : eq_functor => z; rewrite -functorD.
        by rewrite -H -functorD.
  Qed.

  Lemma id_eq_hvfunctor2 : eq_hvfunctor2 id_monadMap.
  Proof. done. Qed.

  Lemma option_eq_hvfunctor2 : eq_hvfunctor2 option_monadMap.
  Proof. by move => A B C f [x|] [y|]. Qed.

End Monad_applicative_lemma.

(* ********************* *)

Module Kleisli.
  Record mixin_of (m:monadMap) :=
    Mixin {
        _: forall A B (f:A -> B) (x:m (m A)),
            functor f (mu x) = mu (functor (functor f) x)
      }.
  Section ClassDef.
    Record class_of (m:Type -> Type) :=
      Class {
          base : Monad.class_of m;
          pfMixin : PFunctor.mixin_of (WPFunctor.Pack base);
          mixin : mixin_of (Monad.Pack base)
        }.
    Definition base2 m (class:class_of m) : PFunctor.class_of m :=
      PFunctor.Class (pfMixin class).
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base2 class).
    Definition monadMap := Monad.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Monad.class_of.
    Coercion base2 : class_of >-> PFunctor.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Coercion monadMap : map >-> Monad.map.
    Canonical monadMap.
    Notation kleisliMap := map.
  End Exports.
End Kleisli.
Import Kleisli.Exports.

Section Kleisli_lemma.
  Variable (m:kleisliMap).
  Let eta := eta m.

  Lemma functor_mu : forall A B (f:A -> B) (x:m (m A)),
      functor f (mu x) = mu (functor (functor f) x).
  Proof. rewrite /eta. by case : m => func [b b2 []]. Qed.

  (* *)
  Definition Unit := Eta.
  Definition Bind (m:Type -> Type) := forall A B, m A -> (A -> m B) -> m B.

  Definition unit : Unit m := eta.
  Definition bind : Bind m := fun A B x f => mu (functor f x).

  Lemma eq_bind A B (f g:A -> m B) :
    f =1 g -> (@bind _ _)^~ f =1 (@bind _ _)^~ g.
  Proof. move => fg x. by rewrite /bind (eq_functor fg). Qed.

  Lemma bind_unitr A (x:m A) : bind x (@unit _) = x.
  Proof. exact : mu_functor_eta. Qed.

  Lemma bind_unitl A B x (f:A -> m B) : bind (unit x) f = f x.
  Proof. by rewrite /bind /unit functor_eta mu_eta. Qed.

  Lemma bindA A B C x (f:A -> m B) (g:B -> m C) :
    bind (bind x f) g = bind x (fun y => bind (f y) g).
  Proof. by rewrite /bind functor_mu -mu_functor_mu -!functorD. Qed.

  (* hfunctor2 *)
  Definition hfunctor2_mixin_of : Functor2.mixin_of m.
  Proof.
    apply : (@Functor2.Mixin _ (@hfunctor2 m))
    =>[A B C D f g H x y z|A B C f x y|A B C f x y|A B C D f g x y|
       A B C D E f g x y z|A B C D E f g x y z]; rewrite /hfunctor2 /=.
    - rewrite !functor_mu -!functorD. congr mu. congr mu.
      apply : eq_functor => a /=. rewrite -!functorD. apply : eq_functor => b.
      exact : (eq_functor (H a b)).
    - by rewrite functor_eta mu_eta.
    - have -> : functor (fun a => functor (f a) (eta y)) x =
                functor (@eta _ \o f^~ y) x
        by apply : eq_functor => a /=; rewrite functor_eta.
        by rewrite functorD mu_functor_eta.
    - by rewrite -functorD.
    - rewrite !functor_mu -!functorD. congr mu. congr mu.
      apply : eq_functor => a /=. by rewrite -!functorD.
    - rewrite functor_mu -mu_functor_mu -!functorD. congr mu.
      apply : eq_functor => a /=. rewrite functor_mu -!functorD. congr mu.
      apply : eq_functor => b /=. by rewrite -functorD.
  Defined.
  Definition hfunctor2_class_of : Functor2.class_of m :=
    Functor2.Class hfunctor2_mixin_of.
  Definition hfunctor2Map : functor2Map :=
    @Functor2.Pack m hfunctor2_class_of.
  Definition functor2_hfunctor2 :
    @functor2 hfunctor2Map = @hfunctor2 m := erefl.
  Definition functor2_happlicative A B C (f:A -> B -> C) :
    @applicative hfunctor2Map = @happlicative _ := erefl.

  (* vfunctor2 *)
  Definition vfunctor2_mixin_of : Functor2.mixin_of m.
  Proof.
    apply : (@Functor2.Mixin _ (@vfunctor2 m))
    =>[A B C D f g H x y z|A B C f x y|A B C f x y|A B C D f g x y|
       A B C D E f g x y z|A B C D E f g x y z]; rewrite /vfunctor2 /=.
    - congr mu. apply : eq_functor => c. rewrite !functor_mu -!functorD.
      congr mu. apply : eq_functor => b /=. rewrite -!functorD.
      apply : eq_functor => a /=. exact : H.
    - have -> : functor (fun b => functor (f^~ b) (eta x)) y =
                functor (@eta _ \o f x) y
        by apply : eq_functor => b /=; rewrite functor_eta.
        by rewrite functorD mu_functor_eta.
    - by rewrite functor_eta mu_eta.
    - congr mu. apply : eq_functor => b. by rewrite -!functorD.
    - congr mu. apply : eq_functor => c. rewrite !functor_mu -!functorD.
      congr mu. apply : eq_functor => b /=. by rewrite -!functorD.
    - rewrite functor_mu -mu_functor_mu -!functorD. congr mu.
      apply : eq_functor => a /=. rewrite functor_mu -!functorD. congr mu.
      apply : eq_functor => b /=. by rewrite -functorD.
  Defined.
  Definition vfunctor2_class_of : Functor2.class_of m :=
    Functor2.Class vfunctor2_mixin_of.
  Definition vfunctor2Map : functor2Map :=
    @Functor2.Pack m vfunctor2_class_of.
  Definition functor2_vfunctor2 :
    @functor2 vfunctor2Map = @vfunctor2 m := erefl.
  Definition functor2_vapplicative A B C (f:A -> B -> C) :
    @applicative vfunctor2Map = @vapplicative _ := erefl.
End Kleisli_lemma.

Definition eq_kleisliMap (m:Type -> Type) (c d:Kleisli.class_of m) :=
  eq_monadMap c d.

Section Kleisli_canonicals.
  (* id *)
  Definition id_kleisli_mixin_of : Kleisli.mixin_of id_monadMap.
  Proof. exact : Kleisli.Mixin. Defined. 
  Definition id_kleisli_class_of : Kleisli.class_of id :=
    @Kleisli.Class _ id_monad_class_of id_pfunctor_mixin_of id_kleisli_mixin_of.
  Definition id_kleisliMap : kleisliMap :=
    Eval hnf in @Kleisli.Pack id id_kleisli_class_of.

  (* option *)
  Definition option_kleisli_mixin_of : Kleisli.mixin_of option_monadMap.
  Proof.
      by apply : Kleisli.Mixin => A B f [x|].
  Defined.
  Definition option_kleisli_class_of : Kleisli.class_of option :=
    @Kleisli.Class
      _ option_monad_class_of option_pfunctor_mixin_of option_kleisli_mixin_of.
  Canonical option_kleisliMap : kleisliMap :=
    Eval hnf in @Kleisli.Pack option option_kleisli_class_of.

  (* seq *)
  Definition seq_kleisli_mixin_of : Kleisli.mixin_of seq_monadMap.
  Proof.
    apply : Kleisli.Mixin => A B. exact : map_flatten.
  Defined.
  Definition seq_kleisli_class_of : Kleisli.class_of seq :=
    @Kleisli.Class
      _ seq_monad_class_of seq_pfunctor_mixin_of seq_kleisli_mixin_of.
  Canonical seq_kleisliMap : kleisliMap :=
    Eval hnf in @Kleisli.Pack seq seq_kleisli_class_of.

  Lemma seq_eq_hfunctor2 :
    eq_functor2Map (@hfunctor2_class_of seq_kleisliMap) seq_hfunctor2_class_of.
  Proof. done. Qed.
  Lemma seq_eq_vfunctor2 :
    eq_functor2Map (@vfunctor2_class_of seq_kleisliMap) seq_vfunctor2_class_of.
  Proof. done. Qed.

  (* sumt *)
  Definition sumt_monad_mixin_of R (m:kleisliMap) :
    Monad.mixin_of (sumt_pfunctorMap R m).
  Proof.
    apply : (@Monad.Mixin
               _ ((fun _ x => mu (functor
                                  (fun x => match x with
                                            | inl r => eta _ (inl r)
                                            | inr x => x
                                            end) x)) : Mu (sumt R m)))
    =>[A x|A x|A x].
    - by rewrite functor_eta mu_eta.
    - rewrite /eta /= -functorD (eq_functor (g:=@eta _ _)) =>[|[r|y]]//.
        by rewrite mu_functor_eta.
    - rewrite functor_mu -mu_functor_mu -!functorD. congr(mu).
      apply : eq_functor =>{x} [[a|x]]//=.
        by rewrite functor_eta mu_eta.
  Defined.
  Definition sumt_monad_class_of R (m:kleisliMap) : Monad.class_of (sumt R m) :=
    Monad.Class (sumt_monad_mixin_of R m).
  Canonical sumt_monadMap R (m:kleisliMap) : monadMap :=
    Eval hnf in @Monad.Pack (sumt R m) (sumt_monad_class_of R m).

  Lemma mu_sumt R m :
    @mu (sumt_monadMap R m) =
    fun _ x => mu (functor (fun x => match x with
                                     | inl r => eta _ (inl r)
                                     | inr x => x
                                     end) x).
  Proof. done. Qed.

  Definition sumt_kleisli_mixin_of R (m:kleisliMap) :
    Kleisli.mixin_of (sumt_monadMap R m).
  Proof.
    apply : Kleisli.Mixin => A B f x /=.
    - rewrite [functor _ _]functor_mu functor_sumt /sumt. congr(mu).
      rewrite -!functorD. apply : eq_functor =>{x}[[a|x]]//=.
        by rewrite functor_eta.
  Defined.
  Definition sumt_kleisli_class_of R (m:kleisliMap) :
    Kleisli.class_of (sumt R m) :=
    @Kleisli.Class
      _ (sumt_monad_class_of R m)
      (sumt_pfunctor_class_of R m) (sumt_kleisli_mixin_of R m).
  Definition sumt_kleisliMap R (m:kleisliMap) : kleisliMap :=
    Eval hnf in @Kleisli.Pack (sumt R m) (sumt_kleisli_class_of R m).

  (* mult *)
  Definition mult_monad_mixin_of R (idx:R) (op:Monoid.law idx) (m:kleisliMap) :
    Monad.mixin_of (mult_pfunctorMap op m).
  Proof.
    apply : (@Monad.Mixin
               _ ((fun _ x =>
                    mu (functor (fun amx =>
                                   match amx with
                                   | (a,mx) =>
                                     functor (fun bx =>
                                                match bx with
                                                | (b,x) => (op a b,x)
                                                end) mx
                                   end) x)) : Mu (mult_pfunctorMap op m)))
              =>/=[A x|A x|A x].
    - rewrite [functor _ _]functor_eta mu_eta.
      rewrite (eq_functor (g:=id)) ?functor_id // =>[[r y]].
        by rewrite Monoid.mul1m.
    - rewrite -functorD (eq_functor (g:=@eta _ _)) ?mu_functor_eta
      =>[|[r y]]//=. by rewrite functor_eta Monoid.mulm1.
    - rewrite functor_mu -mu_functor_mu -!functorD. congr(mu).
      apply : eq_functor =>[[r y]]/=. rewrite functor_mu -!functorD. congr(mu).
      apply : eq_functor =>[[s z]]/=. rewrite -functorD.
      apply : eq_functor =>[[t w]]/=. by rewrite Monoid.mulmA.
  Defined.
  Definition mult_monad_class_of R (idx:R) (op:Monoid.law idx) (m:kleisliMap) :
    Monad.class_of (mult op m) := Monad.Class (mult_monad_mixin_of op m).
  Canonical mult_monadMap R (idx:R) (op:Monoid.law idx) (m:kleisliMap) :
    monadMap := Eval hnf in @Monad.Pack (mult op m) (mult_monad_class_of op m).

  Lemma mu_mult R (idx:R) (op:Monoid.law idx) (m:kleisliMap) :
    @mu (mult_monadMap op m) =
    (fun _ x =>
       mu (functor (fun amx =>
                      match amx with
                      | (a,mx) =>
                        functor (fun bx =>
                                   match bx with
                                   | (b,x) => (op a b,x)
                                   end) mx
                      end) x)).
  Proof. done. Qed.

  Definition mult_kleisli_mixin_of R (idx:R) (op:Monoid.law idx) (m:kleisliMap):
    Kleisli.mixin_of (mult_monadMap op m).
  Proof.
    apply : Kleisli.Mixin =>/= A B f x.
    - rewrite mu_mult functor_mult functor_mu -!functorD. congr(mu).
      apply : eq_functor =>[[r y]]/=. rewrite -!functorD.
        by apply : eq_functor =>[[]].
  Defined.
  Definition mult_kleisli_class_of R (idx:R) (op:Monoid.law idx) (m:kleisliMap):
    Kleisli.class_of (mult op m) :=
    @Kleisli.Class
      _ (mult_monad_class_of op m)
      (mult_pfunctor_mixin_of op m) (mult_kleisli_mixin_of op m).
  Canonical mult_kleisliMap R (idx:R) (op:Monoid.law idx) (m:kleisliMap) :
    kleisliMap :=
    Eval hnf in @Kleisli.Pack (mult op m) (mult_kleisli_class_of op m).
End Kleisli_canonicals.

(* ********************* *)

Module F2Kleisli.
  Record mixin_of (m:kleisliMap) (functor2:Functor2 m) :=
    Mixin {
        _: forall A B C f (x:m (m A)) (y:m (m B)),
          functor2 A B C f (mu x) (mu y) =
          mu (functor2 _ _ _ (functor2 _ _ _ f) x y)
      }.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : Kleisli.class_of t;
          aMixin : Functor2.mixin_of (PFunctor.Pack base);
          mixin : @mixin_of (Kleisli.Pack base) (Functor2.functor2 aMixin)
        }.
    Definition base2 t (class:class_of t) : Functor2.class_of t :=
      Functor2.Class (aMixin class).
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
    Definition monadMap := Monad.Pack (base class).
    Definition kleisliMap := Kleisli.Pack (base class).
    Definition functor2Map := Functor2.Pack (base2 class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Kleisli.class_of.
    Coercion base2 : class_of >-> Functor2.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Coercion monadMap : map >-> Monad.map.
    Canonical monadMap.
    Coercion kleisliMap : map >-> Kleisli.map.
    Canonical kleisliMap.
    Coercion functor2Map : map >-> Functor2.map.
    Canonical functor2Map.
    Notation f2kleisliMap := map.
  End Exports.
End F2Kleisli.
Import F2Kleisli.Exports.

Section F2Kleisli_lemma.
  Variable (m:f2kleisliMap).

  Lemma functor2_mu : forall A B C (f:A -> B -> C) (x:m (m A)) (y:m (m B)),
      functor2 f (mu x) (mu y) = mu (functor2 (functor2 f) x y).
  Proof. by case : m =>func [b b2 []]. Qed.
End F2Kleisli_lemma.

Definition eq_f2kleisliMap (m:Type -> Type) (c d:F2Kleisli.class_of m) :=
  eq_kleisliMap c d /\ eq_functor2Map c d.

Section VHkleisli_f2kleisli.
  Variable (m:kleisliMap).
End VHkleisli_f2kleisli.

Section F2Kleisli_canonicals.
  (* id *)
  Definition id_f2kleisli_mixin_of :
    @F2Kleisli.mixin_of id_kleisliMap
                      (Functor2.functor2 id_functor2_mixin_of).
  Proof. exact :F2Kleisli.Mixin. Defined. 
  Definition id_f2kleisli_class_of : F2Kleisli.class_of id :=
    F2Kleisli.Class id_f2kleisli_mixin_of.
  Definition id_f2kleisliMap : f2kleisliMap :=
    Eval hnf in @F2Kleisli.Pack id id_f2kleisli_class_of.

  (* option *)
  Definition option_f2kleisli_mixin_of :
    @F2Kleisli.mixin_of option_kleisliMap
                       (Functor2.functor2 option_functor2_mixin_of).
  Proof.
      by apply : F2Kleisli.Mixin =>/= A B C f [[x|]|] [y|].
  Defined.
  Definition option_f2kleisli_class_of : F2Kleisli.class_of option :=
    F2Kleisli.Class option_f2kleisli_mixin_of.
  Canonical option_f2kleisliMap : f2kleisliMap :=
    Eval hnf in @F2Kleisli.Pack option option_f2kleisli_class_of.

End F2Kleisli_canonicals.

(* ********************* *)
(*
Module MonadPlus.
  Definition MPlus (m:Type -> Type) := forall A, m A -> m A -> m A.

  Record mixin_of (m:wpfunctorMap) :=
    Mixin {
        mplus : MPlus m;

      }.
  Section ClassDef.
    Record class_of (m:Type -> Type) :=
      Class {
          base : WPFunctor.class_of m;
          mixin : mixin_of (WPFunctor.Pack base)
        }.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> WPFunctor.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Notation monadMap := map.
    Notation Mu := Mu.
    Definition mu T := (mu (class T)).
  End Exports.
End MonadPlus.
*)
(* ********************* *)

Module PureMorphism.
  Record class_of (pre pos:pureMap) (t:forall A, pre A -> pos A) :=
    Class {
        _: forall A x, t A (eta _ x) = eta _ x
      }.
  Section ClassDef.
    Structure map := Pack {pre; pos; apply; _: @class_of pre pos apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ _ _ c := cF return class_of (@apply cF) in c.
  End ClassDef.

  Module Exports.
    Coercion apply : map >-> Funclass.
    Notation pureMorphism := map.
    Notation mpre T := (pre T).
    Notation mpos T := (pos T).
  End Exports.
End PureMorphism.
Import PureMorphism.Exports.

Section PureMorphism_lemma.
  Variable (m:pureMorphism).

  Definition morph_eta : forall A x, m A (eta _ x) = eta _ x :=
    let: PureMorphism.Pack
           pre pos T (PureMorphism.Class H) := m in H.
End PureMorphism_lemma.

Definition eq_pureMorphism pre pos t
           (c d:@PureMorphism.class_of pre pos t) := True.

Section PureMorphism_canonicals.
  (* id *)
  Definition id_pureMorphism_class_of (m:pureMap) :
    @PureMorphism.class_of m _ (fun => id)
    := PureMorphism.Class (fun _ _ => erefl _).
  Definition id_pureMorphism (m:pureMap) : pureMorphism :=
    Eval hnf in @PureMorphism.Pack
                  _ _ (fun => id) (id_pureMorphism_class_of m).

  (* eta *)
  Definition eta_pureMorphism_class_of (m n:pureMap):
    @PureMorphism.class_of n (comp_pureMap _ _) (fun _ => @eta m _)
    := PureMorphism.Class (fun _ _ => erefl _).
  Definition eta_pureMorphism (m n:pureMap): pureMorphism :=
    Eval hnf in @PureMorphism.Pack
                  _ (comp_pureMap _ _) (fun _ => @eta m _)
                  (eta_pureMorphism_class_of m n).

  (* functor *)
  Definition functor_pureMorphism_class_of
             (m:pfunctorMap) (t:pureMorphism) :
    @PureMorphism.class_of
      (comp_pureMap m _) (comp_pureMap _ _) (fun _ => functor (t _)).
  Proof.
    apply : PureMorphism.Class => A x.
      by rewrite !eta_comp /= functor_eta morph_eta.
  Defined.
  Definition functor_pureMorphism
             (m:pfunctorMap) (t:pureMorphism) :
    pureMorphism :=
    Eval hnf in @PureMorphism.Pack
                  (comp_pureMap m _) (comp_pureMap _ _)
                  (fun _ => functor (t _)) (functor_pureMorphism_class_of m t).

  (* mu *)
  Definition mu_pureMorphism_class_of (m:monadMap) :
    @PureMorphism.class_of (comp_pureMap _ _) _ (@mu m).
  Proof.
    apply : PureMorphism.Class => A x.
      by rewrite eta_comp /= mu_eta.
  Defined.
  Definition mu_pureMorphism (m:monadMap) : pureMorphism :=
    Eval hnf in
      @PureMorphism.Pack
        (comp_pureMap _ _) _ (@mu m) (mu_pureMorphism_class_of m).
End PureMorphism_canonicals.

Module FunctorMorphism.
  Record class_of (pre pos:functorMap) (t:forall A, pre A -> pos A) :=
    Class {
        _: forall A B f x,
            t B (functor f x) = functor f (t A x)
      }.
  Section ClassDef.
    Structure map := Pack {pre; pos; apply; _: @class_of pre pos apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ _ _ c := cF return class_of (@apply cF) in c.
  End ClassDef.

  Module Exports.
    Coercion apply : map >-> Funclass.
    Notation functorMorphism := map.
  End Exports.
End FunctorMorphism.
Import FunctorMorphism.Exports.

Section FunctorMorphism_lemma.
  Variable (m:functorMorphism).

  Definition morph_functor : forall A B f x,
    m B (functor f x) = functor f (m A x) :=
        let: FunctorMorphism.Pack
           pre pos T (FunctorMorphism.Class H) := m in H.
End FunctorMorphism_lemma.

Definition eq_functorMorphism pre pos t
           (c d:@FunctorMorphism.class_of pre pos t) := True.

Section FunctorMorphism_canonicals.
  (* id *)
  Definition id_functorMorphism_class_of (m:functorMap) :
    @FunctorMorphism.class_of m _ (fun => id)
    := FunctorMorphism.Class (fun _ _ _ _ => erefl _).
  Definition id_functorMorphism (m:functorMap) : functorMorphism :=
    Eval hnf in @FunctorMorphism.Pack
                  _ _ (fun => id) (id_functorMorphism_class_of m).

  (* eta *)
  Definition eta_functorMorphism_class_of (m:pfunctorMap) (n:functorMap):
    @FunctorMorphism.class_of n (comp_functorMap _ _) (fun _ => @eta m _).
  Proof.
    apply : FunctorMorphism.Class => A B f x.
      by rewrite functor_comp /= functor_eta.
  Defined.

  (* functor *)
  Definition functor_functorMorphism_class_of
             (m:functorMap) (t:functorMorphism) :
    @FunctorMorphism.class_of
      (comp_functorMap m _) (comp_functorMap _ _) (fun _ => functor (t _)).
  Proof.
    apply : FunctorMorphism.Class => A B f x.
      by rewrite !functor_comp /= -!functorD (eq_functor (morph_functor _)).
  Defined.
  Definition functor_pfunctorTransformation (m:functorMap)
             (t:functorMorphism) : functorMorphism :=
    Eval hnf in @FunctorMorphism.Pack
                  (comp_functorMap _ _) (comp_functorMap _ _)
                  (fun _ => functor (t _))
                  (functor_functorMorphism_class_of m t).

  (* mu *)
  Definition mu_functorMorphism_class_of (m:kleisliMap) :
    @FunctorMorphism.class_of (comp_functorMap _ _) _ (@mu m).
  Proof.
    apply : FunctorMorphism.Class => A B f x.
      by rewrite functor_comp /= functor_mu.
  Defined.
  Definition mu_functorMorphism (m:kleisliMap) : functorMorphism :=
    Eval hnf in
      @FunctorMorphism.Pack
        (comp_functorMap _ _) _ (@mu m) (mu_functorMorphism_class_of m).
End FunctorMorphism_canonicals.

Module PFunctorMorphism.
  Section ClassDef.
    Record class_of (pre pos:pfunctorMap) (t:forall A, pre A -> pos A) :=
      Class {
          base : PureMorphism.class_of t;
          base2 : FunctorMorphism.class_of t
        }.
    Structure map := Pack {pre; pos; apply; _: @class_of pre pos apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ _ _ c := cF return class_of (@apply cF) in c.
    Definition pureMorphism := PureMorphism.Pack (base class).
    Definition functorMorphism := FunctorMorphism.Pack (base2 class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> PureMorphism.class_of.
    Coercion base2 : class_of >-> FunctorMorphism.class_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMorphism : map >-> PureMorphism.map.
    Canonical pureMorphism.
    Coercion functorMorphism : map >-> FunctorMorphism.map.
    Canonical functorMorphism.
    Notation pfunctorMorphism := map.
  End Exports.
End PFunctorMorphism.
Import PFunctorMorphism.Exports.

Section PFunctorMorphism_lemma.
  Variable (tf:pfunctorMorphism).
End PFunctorMorphism_lemma.

Definition eq_pfunctorMorphism pre pos t
           (c d:@PFunctorMorphism.class_of pre pos t) :=
  eq_pureMorphism c d /\ eq_functorMorphism c d.

Section PFunctorMorphism_canonicals.
  (* id *)
  Definition id_pfunctorMorphism_class_of (m:pfunctorMap) :
    @PFunctorMorphism.class_of m _ (fun => id) :=
    PFunctorMorphism.Class
      (id_pureMorphism_class_of _) (id_functorMorphism_class_of _).
  Definition id_pfunctorMorphism (m:pfunctorMap) : pfunctorMorphism :=
    Eval hnf in
      @PFunctorMorphism.Pack
        _ _ (fun => id) (id_pfunctorMorphism_class_of m).

  (* eta *)
  Definition eta_pfunctorMorphism_class_of (m n:pfunctorMap) :
    @PFunctorMorphism.class_of n (comp_pfunctorMap _ _) (fun _ => @eta m _).
  Proof.
    apply : PFunctorMorphism.Class.
    - exact : eta_pureMorphism_class_of.
    - exact : eta_functorMorphism_class_of.
  Defined.
  Definition eta_pfunctorMorphism (m n:pfunctorMap) : pfunctorMorphism :=
    Eval hnf in
      @PFunctorMorphism.Pack
        _ (comp_pfunctorMap _ _) (fun _ => @eta m _)
        (eta_pfunctorMorphism_class_of m n).

  (* functor *)
  Definition functor_pfunctorMorphism_class_of
             (m:pfunctorMap) (t:pfunctorMorphism):
    @PFunctorMorphism.class_of
      (comp_pfunctorMap m _) (comp_pfunctorMap _ _) (fun _ => functor (t _)).
  Proof.
    apply : PFunctorMorphism.Class.
    - exact : functor_pureMorphism_class_of.
    - exact : functor_functorMorphism_class_of.
  Defined.
  Definition functor_pfunctorMorphism
             (m:pfunctorMap) (t:pfunctorMorphism): pfunctorMorphism :=
    Eval hnf in
      @PFunctorMorphism.Pack
        (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
        (fun _ => functor (t _)) (functor_pfunctorMorphism_class_of m t).

  (* mu *)
  Definition mu_pfunctorMorphism_class_of (m:kleisliMap) :
    @PFunctorMorphism.class_of (comp_pfunctorMap _ _) _ (@mu m).
  Proof.
    apply : PFunctorMorphism.Class.
    - exact : mu_pureMorphism_class_of.
    - exact : mu_functorMorphism_class_of.
  Defined.
  Definition mu_pfunctorMorphism (m:kleisliMap) : pfunctorMorphism :=
    Eval hnf in
      @PFunctorMorphism.Pack
        (comp_pfunctorMap _ _) _ (@mu m) (mu_pfunctorMorphism_class_of m).
End PFunctorMorphism_canonicals.

(* ********************* *)

Module Functor2Morphism.
  Record mixin_of (pre pos:functor2Map) (t:forall A, pre A -> pos A) :=
    Mixin {
        _: forall A B C f x y,
            t C (functor2 f x y) = functor2 f (t A x) (t B y)
      }.
  Section ClassDef.
    Record class_of (pre pos:functor2Map) (t:forall A, pre A -> pos A) :=
      Class {
          base : PFunctorMorphism.class_of t;
          mixin : mixin_of t
        }.
    Structure map := Pack {pre; pos; apply; _: @class_of pre pos apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ _ _ c := cF return class_of (@apply cF) in c.
    Definition pureMorphism := PureMorphism.Pack (base class).
    Definition functorMorphism := FunctorMorphism.Pack (base class).
    Definition pfunctorMorphism := PFunctorMorphism.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> PFunctorMorphism.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMorphism : map >-> PureMorphism.map.
    Canonical pureMorphism.
    Coercion functorMorphism : map >-> FunctorMorphism.map.
    Canonical functorMorphism.
    Coercion pfunctorMorphism : map >-> PFunctorMorphism.map.
    Canonical pfunctorMorphism.
    Notation functor2Morphism := map.
  End Exports.
End Functor2Morphism.
Import Functor2Morphism.Exports.

Section Functor2Morphism_lemma.
  Variable (m:functor2Morphism).

  Definition morph_functor2 : forall A B C f x y,
      m C (functor2 f x y) = functor2 f (m A x) (m B y) :=
    let: (Functor2Morphism.Mixin H)
       := (Functor2Morphism.mixin (Functor2Morphism.class m)) in H.

  Lemma morph_applicative A B f x:
    m B (applicative f x) = applicative (m _ f) (m A x).
  Proof. exact : morph_functor2. Qed.

  Lemma morph_functor3 A B C D f x y z:
    m D (functor3 f x y z) = functor3 f (m A x) (m B y) (m C z).
  Proof. by rewrite /functor3 !morph_functor2. Qed.
End Functor2Morphism_lemma.

Section Functor2Morphism_canonicals.
  (* id *)
  Definition id_functor2Morphism_mixin_of (m:functor2Map) :
    @Functor2Morphism.mixin_of m _ (fun => id)
    := Functor2Morphism.Mixin (fun _ _ _ _ _ _ => erefl _).
  Definition id_functor2Morphism_class_of (m:functor2Map) :
    @Functor2Morphism.class_of m _ (fun => id).
  Proof.
    apply : Functor2Morphism.Class.
    - exact : id_pfunctorMorphism_class_of.
    - exact : id_functor2Morphism_mixin_of.
  Defined.
  Definition id_functor2Morphism (m:functor2Map) : functor2Morphism :=
    Eval hnf in
      @Functor2Morphism.Pack
        _ _ (fun => id) (id_functor2Morphism_class_of m).

  (* eta *)
  Definition eta_functor2Morphism_mixin_of (m n:functor2Map):
    @Functor2Morphism.mixin_of
      n (comp_functor2Map _ _) (fun _ => @eta m _).
  Proof.
    apply : Functor2Morphism.Mixin => A B C f x y.
      by rewrite functor2_comp functor2_etar functor_eta.
  Defined.
  Definition eta_functor2Morphism_class_of (m n:functor2Map) :
    @Functor2Morphism.class_of
      n (comp_functor2Map _ _) (fun _ => @eta m _).
  Proof.
    apply : Functor2Morphism.Class.
    - exact : eta_pfunctorMorphism_class_of.
    - exact : eta_functor2Morphism_mixin_of.
  Defined.
  Definition eta_functor2Morphism (m n:functor2Map): functor2Morphism :=
    Eval hnf in @Functor2Morphism.Pack
                  _ (comp_functor2Map _ _) (fun _ => @eta m _)
                  (eta_functor2Morphism_class_of m n).

  (* functor *)
  Definition functor_functor2Morphism_mixin_of
             (m:functor2Map) (t:functor2Morphism) :
    @Functor2Morphism.mixin_of
      (comp_functor2Map m _) (comp_functor2Map _ _) (fun _ => functor (t _)).
  Proof.
    apply : Functor2Morphism.Mixin => A B C f x y.
    rewrite !functor2_comp -functor2Dr -functor2D -functor2Dl.
    apply : (@eq_functor2 m) => a b. exact : morph_functor2.
  Defined.
  Definition functor_functor2Morphism_class_of
             (m:functor2Map) (t:functor2Morphism) :
    @Functor2Morphism.class_of
      (comp_functor2Map m _) (comp_functor2Map _ _) (fun _ => functor (t _)).
  Proof.
    apply : Functor2Morphism.Class.
    - exact : functor_pfunctorMorphism_class_of.
    - exact : functor_functor2Morphism_mixin_of.
  Defined.
  Definition functor_functor2Morphism
             (m:functor2Map) (t:functor2Morphism) : functor2Morphism :=
    Eval hnf in @Functor2Morphism.Pack
                  (comp_functor2Map m _) (comp_functor2Map _ _)
                  (fun _ => functor (t _))
                  (functor_functor2Morphism_class_of m t).

  (* mu *)
  Definition mu_functor2Morphism_mixin_of (m:f2kleisliMap) :
    @Functor2Morphism.mixin_of (comp_functor2Map _ _) _ (@mu m).
  Proof.
    apply : Functor2Morphism.Mixin => A B C f x y.
      by rewrite functor2_comp functor2_mu.
  Defined.
  Definition mu_functor2Morphism_class_of (m:f2kleisliMap) :
    @Functor2Morphism.class_of (comp_functor2Map _ _) _ (@mu m).
  Proof.
    apply : Functor2Morphism.Class.
    - exact : mu_pfunctorMorphism_class_of.
    - exact : mu_functor2Morphism_mixin_of.
  Defined.
  Definition mu_functor2Morphism (m:f2kleisliMap) : functor2Morphism :=
    Eval hnf in @Functor2Morphism.Pack
                  (comp_functor2Map m _) _ (@mu m)
                  (mu_functor2Morphism_class_of m).
End Functor2Morphism_canonicals.

(* ********************* *)

Module FF2Sequence.
  Definition F2Sequence (t:Type -> Type) :=
    forall (m:functor2Map) A, t (m A) -> m (t A).
  Definition F2Traverse (t:Type -> Type) :=
    forall (m:functor2Map) A B, (A -> m B) -> t A -> m (t B).
  Definition F2Consume (t:Type -> Type) :=
    forall (m:functor2Map) A B, (t A -> B) -> t (m A) -> m B.

  Record mixin_of (t:functorMap) :=
    Mixin {
        f2sequence:F2Sequence t;
        _:forall (m:functor2Map) A B (f:A -> B) (x:t (m A)),
            f2sequence (functor (functor f) x) =
            functor (functor f) (f2sequence x);
        _:forall (m:functor2Morphism) A x,
            m _ (f2sequence x) = f2sequence (functor (m A) x);
        _:forall A, @f2sequence id_functor2Map A =1 id;
        _:forall (m n:functor2Map) A x,
            @f2sequence (comp_functor2Map m n) A x
            = functor (@f2sequence _ _) (@f2sequence m _ x)
      }.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : Functor.class_of t;
          mixin : mixin_of (Functor.Pack base)
        }.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition functorMap := Functor.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Functor.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Notation ff2sequenceMap := map.
    Notation F2Sequence := F2Sequence.
    Notation F2Traverse := F2Traverse.
    Notation F2Consume := F2Consume.
    Definition f2sequence T := f2sequence (class T).
  End Exports.
End FF2Sequence.
Import FF2Sequence.Exports.

Section FF2Sequence_lemma.
  Variable (t:ff2sequenceMap).

  Lemma f2sequence_functor_functor :
    forall (m:functor2Map) A B (f:A -> B) (x:t (m A)),
      f2sequence (functor (functor f) x) = functor (functor f) (f2sequence x).
  Proof. by case : t => func [b []]. Qed.

  Lemma morph_f2sequence_def : forall (m:functor2Morphism) A x,
      m _ (@f2sequence t _ _ x) = f2sequence (functor (m A) x).
  Proof. by case : t => func [b []]. Qed.

  Lemma f2sequence_idMap : forall A, @f2sequence t id_functor2Map A =1 id.
  Proof. by case : t => func [b []]. Qed.

  Lemma f2sequence_compMap :forall (m n:functor2Map) A x,
            @f2sequence t (comp_functor2Map m n) A x
            = functor (@f2sequence _ _ _) (@f2sequence _ m _ x).
  Proof. by case : t => func [b []]. Qed.

  Lemma morph_f2sequence (m n:functor2Map) (f:forall A, m A -> n A):
    Functor2Morphism.class_of f ->
    forall A x, f _ (@f2sequence t _ _ x) = f2sequence (functor (f A) x).
  Proof.
    move => c. exact : (@morph_f2sequence_def (Functor2Morphism.Pack c)).
  Qed.

  Lemma f2sequence_functor_eta (m:functor2Map) A (x:t A) :
      f2sequence (functor (@eta m _) x) = eta m x.
  Proof.
    move : (@morph_f2sequence_def (eta_functor2Morphism m id_functor2Map) _ x).
    rewrite f2sequence_idMap /==>->. rewrite f2sequence_compMap.
      by rewrite (eq_functor_id (@f2sequence_idMap _)).
  Qed.

  Lemma f2sequence_functor_mu (m:f2kleisliMap) A (x:t (m (m A))) :
      f2sequence (functor (@mu _ _) x) =
      mu (functor (@f2sequence _ _ _) (f2sequence x)).
  Proof.
    rewrite -(morph_f2sequence (mu_functor2Morphism_class_of m)).
      by rewrite f2sequence_compMap.
  Qed.

  Definition f2traverse : F2Traverse t :=
    fun _ _ _ f x => f2sequence (functor f x).
  Definition f2consume : F2Consume t :=
    fun _ _ _ f x => functor f (f2traverse id x).

  Lemma f2sequence_def : forall m A, @f2sequence _ m A =1 f2consume id.
  Proof. move => m A x. by rewrite /f2consume /f2traverse !functor_id. Qed.

  Lemma f2traverseD (m:functor2Map) A B C (f:B -> m C) (g:A -> B) x:
    f2traverse (f \o g) x = f2traverse f (functor g x).
  Proof. by rewrite /f2traverse functorD. Qed.

  Lemma f2traverse_functorD (m:functor2Map) A B C (f:B -> C) (g:A -> m B) x:
    f2traverse (functor f \o g) x = functor (functor f) (f2traverse g x).
  Proof. by rewrite /f2traverse functorD f2sequence_functor_functor. Qed.

  (* morphism *)
  (* functor *)
  Definition f2sequence_functorMorphism_class_of (m:functor2Map) :
    @FunctorMorphism.class_of (comp_functorMap _ _) (comp_functorMap _ _)
                              (@f2sequence t m).
  Proof.
    apply : FunctorMorphism.Class => A B f x.
    exact : f2sequence_functor_functor.
  Defined.
  Definition f2sequnece_functorMorphism (m:functor2Map) : functorMorphism :=
    Eval hnf in
      @FunctorMorphism.Pack
        (comp_functorMap _ _) (comp_functorMap _ _)
        (@f2sequence t m) (f2sequence_functorMorphism_class_of m).
End FF2Sequence_lemma.

Definition eq_ff2sequenceMap (t:Type -> Type) (c d:FF2Sequence.class_of t) :=
  eq_functorMap c d /\
  forall m A,
    @f2sequence (FF2Sequence.Pack c) m A
    =1 @f2sequence (FF2Sequence.Pack d) m _.

Section FF2Sequence_canonicals.
  (* id *)
  Definition id_ff2sequence_mixin_of : FF2Sequence.mixin_of id_functorMap.
  Proof.
    apply : (@FF2Sequence.Mixin _ ((fun _ _ => id) : F2Sequence id_functorMap))
    =>[|||m n A x]//. by rewrite functor_id.
  Defined.
  Definition id_ff2sequence_class_of : FF2Sequence.class_of id :=
    FF2Sequence.Class id_ff2sequence_mixin_of.
  Definition id_ff2sequenceMap : ff2sequenceMap :=
    Eval hnf in @FF2Sequence.Pack id id_ff2sequence_class_of.

  (* comp *)
  Definition comp_ff2sequence_mixin_of (t s:ff2sequenceMap) :
    FF2Sequence.mixin_of (comp_functorMap t s).
  Proof.
    apply : (@FF2Sequence.Mixin
               _ ((fun _ _ => @f2sequence _ _ _ \o functor (@f2sequence _ _ _))
                  : F2Sequence (comp_functorMap t s)))
    =>[m A B f x|m A x|A x|m n A x]/=.
    - rewrite -f2sequence_functor_functor -!functorD.
        by rewrite (eq_functor (f2sequence_functor_functor _)).
    - rewrite morph_f2sequence_def -!functorD. congr f2sequence.
      apply : eq_functor. exact : morph_f2sequence_def.
    - by rewrite f2sequence_idMap (eq_functor_id (@f2sequence_idMap _ _)).
    - rewrite f2sequence_compMap functorD -f2sequence_functor_functor -functorD.
        by rewrite (eq_functor (@f2sequence_compMap _ _ _ _)).
  Defined.
  Definition comp_ff2sequence_class_of (t s:ff2sequenceMap) :
    FF2Sequence.class_of (fun A => t (s A)) :=
    FF2Sequence.Class (comp_ff2sequence_mixin_of t s).
  Definition comp_ff2sequenceMap (t s:ff2sequenceMap) : ff2sequenceMap :=
    Eval hnf in
      @FF2Sequence.Pack (fun A => t (s A)) (comp_ff2sequence_class_of t s).

  Definition f2sequence_comp t s :
    @f2sequence (comp_ff2sequenceMap t s) =
    fun _ _ => @f2sequence _ _ _ \o functor (@f2sequence _ _ _) := erefl.

  (* option *)
  Definition option_ff2sequence_mixin_of :
    FF2Sequence.mixin_of option_functorMap.
  Proof.
    apply : (@FF2Sequence.Mixin
               _ (fun _ _ o =>
                    if o is Some x then functor (@Some _) x else eta _ None))
    =>[m A B f [x|]|m A [x|]|A [x|]|m n A [x|]]//=.
    - by rewrite -!functorD.
    - by rewrite functor_eta.
    - by rewrite morph_functor.
    - by rewrite morph_eta.
    - by rewrite -functorD.
    - by rewrite functor_eta.
  Defined.
  Definition option_ff2sequence_class_of : FF2Sequence.class_of option :=
    FF2Sequence.Class option_ff2sequence_mixin_of.
  Canonical option_ff2sequenceMap : ff2sequenceMap :=
    Eval hnf in @FF2Sequence.Pack option option_ff2sequence_class_of.

  Definition f2sequence_option :
    @f2sequence option_ff2sequenceMap =
    fun _ _ o => if o is Some x then functor (@Some _) x else eta _ None
    := erefl.

  (* seq *)
  Definition seq_ff2sequence_mixin_of : FF2Sequence.mixin_of seq_functorMap.
  Proof.
    apply : (@FF2Sequence.Mixin
               _ (fun _ _ => foldr (functor2 cons) (eta _ [::])))
    =>[m A B f|m A|A|m n A].
    - elim =>[|x s /=->]; [by rewrite functor_eta|].
        by rewrite -functor2D -functor2Dl -functor2Dr.
    - elim =>[|x s /=<-]; [by rewrite morph_eta| by rewrite morph_functor2].
    - by elim =>[|x s /=->].
    - elim =>[|x s /=->]; [by rewrite functor_eta|].
        by rewrite -functor2Dr functor2_comp -functor2Dl.
  Defined.
  Definition seq_ff2sequence_class_of : FF2Sequence.class_of seq :=
    FF2Sequence.Class seq_ff2sequence_mixin_of.
  Canonical seq_ff2sequenceMap : ff2sequenceMap :=
    Eval hnf in @FF2Sequence.Pack seq seq_ff2sequence_class_of.

  Definition f2sequence_seq :
    @f2sequence seq_ff2sequenceMap =
    fun _ _ => foldr (functor2 cons) (eta _ [::]) := erefl.

  (* sumt *)
  Definition sumt_ff2sequence_mixin_of R (t:ff2sequenceMap):
    FF2Sequence.mixin_of (sumt_functorMap R t).
  Proof.
    apply : (@FF2Sequence.Mixin
               _ ((fun m _ =>
                     @f2sequence _ _ _ \o functor (fun rma =>
                                          match rma with
                                          | inl r => eta _ (inl r)
                                          | inr ma => @functor m _ _ inr ma
                                          end))
                  : F2Sequence (sumt_functorMap R t)))
    =>[m A B f x|m A x|A x|m n A x]/=.
    - rewrite -f2sequence_functor_functor -!functorD. congr f2sequence.
      apply : eq_functor =>[[r|a]]/=; [by rewrite functor_eta|].
        by rewrite -!functorD.
    - rewrite morph_f2sequence_def -!functorD. congr f2sequence.
      apply : eq_functor =>[[r|a]]/=; [by rewrite morph_eta|].
        by rewrite morph_functor.
    - by rewrite eq_functor_id ?f2sequence_idMap // =>[[r|a]].
    - rewrite functorD -f2sequence_functor_functor -functorD f2sequence_compMap.
      congr (functor (@f2sequence _ _ _) (f2sequence _)).
      apply : eq_functor =>[[r|a]]/=; [by rewrite functor_eta|].
        by rewrite -functorD.
  Defined.
  Definition sumt_ff2sequence_class_of R (t:ff2sequenceMap) :
    FF2Sequence.class_of (sumt R t) :=
    FF2Sequence.Class (sumt_ff2sequence_mixin_of R t).
  Canonical sumt_ff2sequenceMap R (t:ff2sequenceMap) : ff2sequenceMap :=
    Eval hnf in @FF2Sequence.Pack (sumt R t) (sumt_ff2sequence_class_of R t).

  Definition f2sequence_sumt R (t:ff2sequenceMap) :
    @f2sequence (sumt_ff2sequenceMap R t) =
    fun m _ f => f2sequence (functor
                              (fun rma => match rma with
                                          | inl r => eta _ (inl r)
                                          | inr ma => @functor m _ _ inr ma
                                          end) f)
    := erefl.

  (* mult *)
  Definition mult_ff2sequence_mixin_of R (idx:R) (op:Monoid.law idx)
             (t:ff2sequenceMap): FF2Sequence.mixin_of (mult_functorMap op t).
  Proof.
    apply : (@FF2Sequence.Mixin
               _ ((fun _ _ =>
                     @f2sequence _ _ _ \o
                                 functor (fun rma =>
                                            match rma with
                                            | (r,ma) => functor (pair r) ma
                                            end)) : F2Sequence (mult op t)))
    =>[m A B f x|m A x|A x|m n A x]/=.
    - rewrite -f2sequence_functor_functor -!functorD. congr f2sequence.
      apply : eq_functor =>[[r ma]]/=. by rewrite -!functorD.
    - rewrite morph_f2sequence_def -!functorD. congr f2sequence.
      apply : eq_functor =>[[r ma]]/=. by rewrite morph_functor.
    - by rewrite f2sequence_idMap eq_functor_id // =>[[]].
    - rewrite functorD -f2sequence_functor_functor -functorD f2sequence_compMap.
      congr (functor (@f2sequence _ _ _) (f2sequence _)).
      apply : eq_functor =>[[r ma]]/=. by rewrite -functorD.
  Defined.
  Definition mult_ff2sequence_class_of R (idx:R) (op:Monoid.law idx)
             (t:ff2sequenceMap) : FF2Sequence.class_of (mult op t) :=
    FF2Sequence.Class (mult_ff2sequence_mixin_of op t).
  Canonical mult_ff2sequenceMap R (idx:R) (op:Monoid.law idx)
            (t:ff2sequenceMap): ff2sequenceMap :=
    Eval hnf in @FF2Sequence.Pack (mult op t) (mult_ff2sequence_class_of op t).

  Definition f2sequence_mult R (idx:R) (op:Monoid.law idx) (t:ff2sequenceMap) :
    @f2sequence (mult_ff2sequenceMap op t) =
    fun _ _ f => f2sequence (functor (fun rma =>
                                      match rma with
                                      | (r,ma) => functor (pair r) ma
                                      end) f)
  := erefl.
End FF2Sequence_canonicals.

(* ********************* *)

Module FPFSequence.
  Definition PFSequence (t:Type -> Type) :=
    forall (m:pfunctorMap) A, t (m A) -> m (t A).
  Definition PFTraverse (t:Type -> Type) :=
    forall (m:pfunctorMap) A B, (A -> m B) -> t A -> m (t B).
  Definition PFConsume (t:Type -> Type) :=
    forall (m:pfunctorMap) A B, (t A -> B) -> t (m A) -> m B.

  Record mixin_of (t:functorMap) :=
    Mixin {
        pfsequence:PFSequence t;
        _:forall (m:pfunctorMap) A B (f:A -> B) (x:t (m A)),
            pfsequence (functor (functor f) x) =
            functor (functor f) (pfsequence x);
        _:forall (m:pfunctorMorphism) A x,
            m _ (pfsequence x) = pfsequence (functor (m A) x);
        _:forall A, @pfsequence id_pfunctorMap A =1 id;
        _:forall (m n:pfunctorMap) A x,
            @pfsequence (comp_pfunctorMap m n) A x
            = functor (@pfsequence _ _) (@pfsequence m _ x)
      }.
  Definition ff2sequence_mixin_of t (mixin:mixin_of t) :=
    let: Mixin _ H1 H2 H3 H4 := mixin in FF2Sequence.Mixin H1 H2 H3 H4.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : Functor.class_of t;
          mixin : mixin_of (Functor.Pack base)
        }.
    Definition ff2sequence_mixin t (class:class_of t) :
      FF2Sequence.mixin_of (Functor.Pack (base class)) :=
      let: Class _ mixin := class in ff2sequence_mixin_of mixin.
    Definition ff2sequence_class t (class:class_of t) :=
      FF2Sequence.Class (ff2sequence_mixin class).
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition functorMap := Functor.Pack (base class).
    Definition ff2sequenceMap := FF2Sequence.Pack (ff2sequence_class class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Functor.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion ff2sequence_mixin : class_of >-> FF2Sequence.mixin_of.
    Coercion ff2sequence_class : class_of >-> FF2Sequence.class_of.
    Coercion apply : map >-> Funclass.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion ff2sequenceMap : map >-> FF2Sequence.map.
    Canonical ff2sequenceMap.
    Notation fpfsequenceMap := map.
    Notation PFSequence := PFSequence.
    Notation PFTraverse := PFTraverse.
    Notation PFConsume := PFConsume.
    Definition pfsequence T := pfsequence (class T).
  End Exports.
End FPFSequence.
Import FPFSequence.Exports.

Section FPFSequence_lemma.
  Variable (t:fpfsequenceMap).

  Lemma pfsequence_functor_functor :
    forall (m:pfunctorMap) A B (f:A -> B) (x:t (m A)),
      pfsequence (functor (functor f) x) = functor (functor f) (pfsequence x).
  Proof. by case : t => func [b []]. Qed.

  Lemma morph_pfsequence_def : forall (m:pfunctorMorphism) A x,
      m _ (@pfsequence t _ _ x) = pfsequence (functor (m A) x).
  Proof. by case : t => func [b []]. Qed.

  Lemma pfsequence_idMap : forall A, @pfsequence t id_pfunctorMap A =1 id.
  Proof. by case : t => func [b []]. Qed.

  Lemma pfsequence_compMap :forall (m n:pfunctorMap) A x,
            @pfsequence t (comp_pfunctorMap m n) A x
            = functor (@pfsequence _ _ _) (@pfsequence _ m _ x).
  Proof. by case : t => func [b []]. Qed.

  Lemma morph_pfsequence (m n:pfunctorMap) (f:forall A, m A -> n A):
    PFunctorMorphism.class_of f ->
    forall A x, f _ (@pfsequence t _ _ x) = pfsequence (functor (f A) x).
  Proof.
    move => c. exact : (@morph_pfsequence_def (PFunctorMorphism.Pack c)).
  Qed.

  Lemma pfsequence_functor_eta (m:pfunctorMap) A (x:t A) :
      pfsequence (functor (@eta m _) x) = eta m x.
  Proof.
    move : (@morph_pfsequence_def (eta_pfunctorMorphism m id_pfunctorMap) _ x).
    rewrite pfsequence_idMap /==>->. rewrite pfsequence_compMap.
      by rewrite (eq_functor_id (@pfsequence_idMap _)).
  Qed.

  Lemma pfsequence_functor_mu (m:kleisliMap) A (x:t (m (m A))) :
      pfsequence (functor (@mu _ _) x) =
      mu (functor (@pfsequence _ _ _) (pfsequence x)).
  Proof.
    rewrite -(morph_pfsequence (mu_pfunctorMorphism_class_of m)).
      by rewrite pfsequence_compMap.
  Qed.

  Lemma f2sequenceW :
    forall (m:functor2Map), @f2sequence t m = @pfsequence _ m.
  Proof. by case : t => func [b []]. Qed.

  Definition pftraverse : PFTraverse t :=
    fun _ _ _ f x => pfsequence (functor f x).
  Definition pfconsume : PFConsume t :=
    fun _ _ _ f x => functor f (pftraverse id x).

  Lemma pfsequence_def : forall m A, @pfsequence _ m A =1 pfconsume id.
  Proof. move => m A x. by rewrite /pfconsume /pftraverse !functor_id. Qed.

  Lemma pftraverseD (m:pfunctorMap) A B C (f:B -> m C) (g:A -> B) x:
    pftraverse (f \o g) x = pftraverse f (functor g x).
  Proof. by rewrite /pftraverse functorD. Qed.

  Lemma pftraverse_functorD (m:pfunctorMap) A B C (f:B -> C) (g:A -> m B) x:
    pftraverse (functor f \o g) x = functor (functor f) (pftraverse g x).
  Proof. by rewrite /pftraverse functorD pfsequence_functor_functor. Qed.

  (* morphism *)
  (* functor *)
  Definition pfsequence_functorMorphism_class_of (m:pfunctorMap) :
    @FunctorMorphism.class_of (comp_functorMap _ _) (comp_functorMap _ _)
                              (@pfsequence t m).
  Proof.
    apply : FunctorMorphism.Class => A B f x.
    exact : pfsequence_functor_functor.
  Defined.
  Definition pfsequnece_functorMorphism (m:pfunctorMap) : functorMorphism :=
    Eval hnf in
      @FunctorMorphism.Pack
        (comp_functorMap _ _) (comp_functorMap _ _)
        (@pfsequence t m) (pfsequence_functorMorphism_class_of m).
End FPFSequence_lemma.

Definition eq_fpfsequenceMap (t:Type -> Type) (c d:FPFSequence.class_of t) :=
  eq_functorMap c d /\
  forall m A,
    @pfsequence (FPFSequence.Pack c) m A
    =1 @pfsequence (FPFSequence.Pack d) m _.

Section FPFSequence_canonicals.
  (* id *)
  Definition id_fpfsequence_mixin_of : FPFSequence.mixin_of id_functorMap.
  Proof.
    apply : (@FPFSequence.Mixin _ ((fun _ _ => id) : PFSequence id_functorMap))
    =>[|||m n A x]//. by rewrite functor_id.
  Defined.
  Definition id_fpfsequence_class_of : FPFSequence.class_of id :=
    FPFSequence.Class id_fpfsequence_mixin_of.
  Definition id_fpfsequenceMap : fpfsequenceMap :=
    Eval hnf in @FPFSequence.Pack id id_fpfsequence_class_of.

  (* comp *)
  Definition comp_fpfsequence_mixin_of (t s:fpfsequenceMap) :
    FPFSequence.mixin_of (comp_functorMap t s).
  Proof.
    apply : (@FPFSequence.Mixin
               _ ((fun _ _ => @pfsequence _ _ _ \o functor (@pfsequence _ _ _))
                  : PFSequence (comp_functorMap t s)))
    =>[m A B f x|m A x|A x|m n A x]/=.
    - rewrite -pfsequence_functor_functor -!functorD.
        by rewrite (eq_functor (pfsequence_functor_functor _)).
    - rewrite morph_pfsequence_def -!functorD. congr pfsequence.
      apply : eq_functor. exact : morph_pfsequence_def.
    - by rewrite pfsequence_idMap (eq_functor_id (@pfsequence_idMap _ _)).
    - rewrite pfsequence_compMap functorD -pfsequence_functor_functor -functorD.
        by rewrite (eq_functor (@pfsequence_compMap _ _ _ _)).
  Defined.
  Definition comp_fpfsequence_class_of (t s:fpfsequenceMap) :
    FPFSequence.class_of (fun A => t (s A)) :=
    FPFSequence.Class (comp_fpfsequence_mixin_of t s).
  Definition comp_fpfsequenceMap (t s:fpfsequenceMap) : fpfsequenceMap :=
    Eval hnf in
      @FPFSequence.Pack (fun A => t (s A)) (comp_fpfsequence_class_of t s).

  Definition pfsequence_comp t s :
    @pfsequence (comp_fpfsequenceMap t s) =
    fun _ _ => @pfsequence _ _ _ \o functor (@pfsequence _ _ _) := erefl.

  (* option *)
  Definition option_fpfsequence_mixin_of :
    FPFSequence.mixin_of option_functorMap.
  Proof.
    apply : (@FPFSequence.Mixin
               _ (fun _ _ o =>
                    if o is Some x then functor (@Some _) x else eta _ None))
    =>[m A B f [x|]|m A [x|]|A [x|]|m n A [x|]]//=.
    - by rewrite -!functorD.
    - by rewrite functor_eta.
    - by rewrite morph_functor.
    - by rewrite morph_eta.
    - by rewrite -functorD.
    - by rewrite functor_eta.
  Defined.
  Definition option_fpfsequence_class_of : FPFSequence.class_of option :=
    FPFSequence.Class option_fpfsequence_mixin_of.
  Canonical option_fpfsequenceMap : fpfsequenceMap :=
    Eval hnf in @FPFSequence.Pack option option_fpfsequence_class_of.

  Definition pfsequence_option :
    @pfsequence option_fpfsequenceMap =
    fun _ _ o => if o is Some x then functor (@Some _) x else eta _ None
    := erefl.

  (* sumt *)
  Definition sumt_fpfsequence_mixin_of R (t:fpfsequenceMap):
    FPFSequence.mixin_of (sumt_functorMap R t).
  Proof.
    apply : (@FPFSequence.Mixin
               _ ((fun m _ =>
                     @pfsequence _ _ _ \o functor (fun rma =>
                                          match rma with
                                          | inl r => eta _ (inl r)
                                          | inr ma => @functor m _ _ inr ma
                                          end))
                  : PFSequence (sumt_functorMap R t)))
    =>[m A B f x|m A x|A x|m n A x]/=.
    - rewrite -pfsequence_functor_functor -!functorD. congr pfsequence.
      apply : eq_functor =>[[r|a]]/=; [by rewrite functor_eta|].
        by rewrite -!functorD.
    - rewrite morph_pfsequence_def -!functorD. congr pfsequence.
      apply : eq_functor =>[[r|a]]/=; [by rewrite morph_eta|].
        by rewrite morph_functor.
    - by rewrite eq_functor_id ?pfsequence_idMap // =>[[r|a]].
    - rewrite functorD -pfsequence_functor_functor -functorD pfsequence_compMap.
      congr (functor (@pfsequence _ _ _) (pfsequence _)).
      apply : eq_functor =>[[r|a]]/=; [by rewrite functor_eta|].
        by rewrite -functorD.
  Defined.
  Definition sumt_fpfsequence_class_of R (t:fpfsequenceMap) :
    FPFSequence.class_of (sumt R t) :=
    FPFSequence.Class (sumt_fpfsequence_mixin_of R t).
  Canonical sumt_fpfsequenceMap R (t:fpfsequenceMap) : fpfsequenceMap :=
    Eval hnf in @FPFSequence.Pack (sumt R t) (sumt_fpfsequence_class_of R t).

  Definition pfsequence_sumt R (t:fpfsequenceMap) :
    @pfsequence (sumt_fpfsequenceMap R t) =
    fun m _ f => pfsequence (functor
                              (fun rma => match rma with
                                          | inl r => eta _ (inl r)
                                          | inr ma => @functor m _ _ inr ma
                                          end) f)
    := erefl.

  (* mult *)
  Definition mult_fpfsequence_mixin_of R (idx:R) (op:Monoid.law idx)
             (t:fpfsequenceMap): FPFSequence.mixin_of (mult_functorMap op t).
  Proof.
    apply : (@FPFSequence.Mixin
               _ ((fun _ _ =>
                     @pfsequence _ _ _ \o
                                 functor (fun rma =>
                                            match rma with
                                            | (r,ma) => functor (pair r) ma
                                            end)) : PFSequence (mult op t)))
    =>[m A B f x|m A x|A x|m n A x]/=.
    - rewrite -pfsequence_functor_functor -!functorD. congr pfsequence.
      apply : eq_functor =>[[r ma]]/=. by rewrite -!functorD.
    - rewrite morph_pfsequence_def -!functorD. congr pfsequence.
      apply : eq_functor =>[[r ma]]/=. by rewrite morph_functor.
    - by rewrite pfsequence_idMap eq_functor_id // =>[[]].
    - rewrite functorD -pfsequence_functor_functor -functorD pfsequence_compMap.
      congr (functor (@pfsequence _ _ _) (pfsequence _)).
      apply : eq_functor =>[[r ma]]/=. by rewrite -functorD.
  Defined.
  Definition mult_fpfsequence_class_of R (idx:R) (op:Monoid.law idx)
             (t:fpfsequenceMap) : FPFSequence.class_of (mult op t) :=
    FPFSequence.Class (mult_fpfsequence_mixin_of op t).
  Canonical mult_fpfsequenceMap R (idx:R) (op:Monoid.law idx)
            (t:fpfsequenceMap): fpfsequenceMap :=
    Eval hnf in @FPFSequence.Pack (mult op t) (mult_fpfsequence_class_of op t).

  Definition pfsequence_mult R (idx:R) (op:Monoid.law idx) (t:fpfsequenceMap) :
    @pfsequence (mult_fpfsequenceMap op t) =
    fun _ _ f => pfsequence (functor (fun rma =>
                                      match rma with
                                      | (r,ma) => functor (pair r) ma
                                      end) f)
  := erefl.

End FPFSequence_canonicals.

(* ********************* *)

Module FFSequence.
  Definition FSequence (t:Type -> Type) :=
    forall (m:functorMap) A, t (m A) -> m (t A).
  Definition FTraverse (t:Type -> Type) :=
    forall (m:functorMap) A B, (A -> m B) -> t A -> m (t B).
  Definition FConsume (t:Type -> Type) :=
    forall (m:functorMap) A B, (t A -> B) -> t (m A) -> m B.

  Record mixin_of (t:functorMap) :=
    Mixin {
        fsequence:FSequence t;
        _:forall (m:functorMap) A B (f:A -> B) (x:t (m A)),
            fsequence (functor (functor f) x) =
            functor (functor f) (fsequence x);
        _:forall (m:functorMorphism) A x,
            m _ (fsequence x) = fsequence (functor (m A) x);
        _:forall A, @fsequence id_functorMap A =1 id;
        _:forall (m n:functorMap) A x,
            @fsequence (comp_functorMap m n) A x
            = functor (@fsequence _ _) (@fsequence m _ x)
      }.
  Definition fpfsequence_mixin_of t (mixin:mixin_of t) :=
    let: Mixin _ H1 H2 H3 H4 := mixin in FPFSequence.Mixin H1 H2 H3 H4.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : Functor.class_of t;
          mixin : mixin_of (Functor.Pack base)
        }.
    Definition fpfsequence_mixin t (class:class_of t) :
      FPFSequence.mixin_of (Functor.Pack (base class)) :=
      let: Class _ mixin := class in fpfsequence_mixin_of mixin.
    Definition fpfsequence_class t (class:class_of t) :=
      FPFSequence.Class (fpfsequence_mixin class).
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF:map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition functorMap := Functor.Pack (base class).
    Definition ff2sequenceMap := FF2Sequence.Pack (fpfsequence_class class).
    Definition fpfsequenceMap := FPFSequence.Pack (fpfsequence_class class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Functor.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion fpfsequence_mixin : class_of >-> FPFSequence.mixin_of.
    Coercion fpfsequence_class : class_of >-> FPFSequence.class_of.
    Coercion apply : map >-> Funclass.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion ff2sequenceMap : map >-> FF2Sequence.map.
    Canonical ff2sequenceMap.
    Coercion fpfsequenceMap : map >-> FPFSequence.map.
    Canonical fpfsequenceMap.
    Notation ffsequenceMap := map.
    Notation FSequence := FSequence.
    Notation FTraverse := FTraverse.
    Notation FConsume := FConsume.
    Definition fsequence T := fsequence (class T).
  End Exports.
End FFSequence.
Import FFSequence.Exports.

Section FFSequence_lemma.
  Variable (t:ffsequenceMap).

  Lemma fsequence_functor_functor :
    forall (m:functorMap) A B (f:A -> B) (x:t (m A)),
      fsequence (functor (functor f) x) = functor (functor f) (fsequence x).
  Proof. by case : t => func [b []]. Qed.

  Lemma morph_fsequence_def : forall (m:functorMorphism) A x,
      m _ (@fsequence t _ _ x) = fsequence (functor (m A) x).
  Proof. by case : t => func [b []]. Qed.

  Lemma fsequence_idMap : forall A, @fsequence t id_functorMap A =1 id.
  Proof. by case : t => func [b []]. Qed.

  Lemma fsequence_compMap :forall (m n:functorMap) A x,
            @fsequence t (comp_functorMap m n) A x
            = functor (@fsequence _ _ _) (@fsequence _ m _ x).
  Proof. by case : t => func [b []]. Qed.

  Lemma morph_fsequence (m n:functorMap) (f:forall A, m A -> n A):
    FunctorMorphism.class_of f ->
    forall A x, f _ (@fsequence t _ _ x) = fsequence (functor (f A) x).
  Proof.
    move => c. exact : (@morph_fsequence_def (FunctorMorphism.Pack c)).
  Qed.
    
  Lemma fsequence_functor_eta (m:pfunctorMap) A (x:t A) :
      fsequence (functor (@eta m _) x) = eta m x.
  Proof.
    move : (@morph_fsequence_def (eta_pfunctorMorphism m id_pfunctorMap) _ x).
    rewrite fsequence_idMap /==>->. rewrite fsequence_compMap.
      by rewrite (eq_functor_id (@fsequence_idMap _)).
  Qed.

  Lemma fsequence_functor_mu (m:kleisliMap) A (x:t (m (m A))) :
      fsequence (functor (@mu _ _) x) =
      mu (functor (@fsequence _ _ _) (fsequence x)).
  Proof.
    rewrite -(morph_fsequence (mu_functorMorphism_class_of m)).
      by rewrite fsequence_compMap.
  Qed.

  Lemma pfsequenceW :
    forall (m:functor2Map), @pfsequence t m = @fsequence _ m.
  Proof. by case : t => func [b []]. Qed.

  Definition ftraverse : FTraverse t :=
    fun _ _ _ f x => fsequence (functor f x).
  Definition fconsume : FConsume t :=
    fun _ _ _ f x => functor f (ftraverse id x).

  Lemma fsequence_def : forall m A, @fsequence _ m A =1 fconsume id.
  Proof. move => m A x. by rewrite /fconsume /ftraverse !functor_id. Qed.

  Lemma ftraverseD (m:pfunctorMap) A B C (f:B -> m C) (g:A -> B) x:
    ftraverse (f \o g) x = ftraverse f (functor g x).
  Proof. by rewrite /ftraverse functorD. Qed.

  Lemma ftraverse_functorD (m:pfunctorMap) A B C (f:B -> C) (g:A -> m B) x:
    ftraverse (functor f \o g) x = functor (functor f) (ftraverse g x).
  Proof. by rewrite /ftraverse functorD fsequence_functor_functor. Qed.

  (* morphism *)
  (* functor *)
  Definition fsequence_functorMorphism_class_of (m:functorMap) :
    @FunctorMorphism.class_of (comp_functorMap _ _) (comp_functorMap _ _)
                              (@fsequence t m).
  Proof.
    apply : FunctorMorphism.Class => A B f x.
    exact : fsequence_functor_functor.
  Defined.
  Definition fsequnece_functorMorphism (m:functorMap) : functorMorphism :=
    Eval hnf in
      @FunctorMorphism.Pack
        (comp_functorMap _ _) (comp_functorMap _ _)
        (@fsequence t m) (fsequence_functorMorphism_class_of m).
End FFSequence_lemma.

Definition eq_ffsequenceMap (t:Type -> Type) (c d:FFSequence.class_of t) :=
  eq_functorMap c d /\
  forall m A,
      @fsequence (FFSequence.Pack c) m A =1 @fsequence (FFSequence.Pack d) m _.

Section FFSequence_canonicals.
  (* id *)
  Definition id_ffsequence_mixin_of : FFSequence.mixin_of id_functorMap.
  Proof.
    apply : (@FFSequence.Mixin _ ((fun _ _ => id) : FSequence id_functorMap))
    =>[|||m n A x]//. by rewrite functor_id.
  Defined.
  Definition id_ffsequence_class_of : FFSequence.class_of id :=
    FFSequence.Class id_ffsequence_mixin_of.
  Definition id_ffsequenceMap : ffsequenceMap :=
    Eval hnf in @FFSequence.Pack id id_ffsequence_class_of.

  (* comp *)
  Definition comp_ffsequence_mixin_of (t s:ffsequenceMap) :
    FFSequence.mixin_of (comp_functorMap t s).
  Proof.
    apply : (@FFSequence.Mixin
               _ ((fun _ _ => @fsequence _ _ _ \o functor (@fsequence _ _ _))
                  : FSequence (comp_functorMap t s)))
    =>[m A B f x|m A x|A x|m n A x]/=.
    - rewrite -fsequence_functor_functor -!functorD.
        by rewrite (eq_functor (fsequence_functor_functor _)).
    - rewrite morph_fsequence_def -!functorD. congr fsequence.
      apply : eq_functor. exact : morph_fsequence_def.
    - by rewrite fsequence_idMap (eq_functor_id (@fsequence_idMap _ _)).
    - rewrite fsequence_compMap functorD -fsequence_functor_functor -functorD.
      congr (functor (@fsequence _ _ _) (fsequence _)).
      apply : eq_functor => y. exact : fsequence_compMap.
  Defined.
  Definition comp_ffsequence_class_of (t s:ffsequenceMap) :
    FFSequence.class_of (fun A => t (s A)) :=
    FFSequence.Class (comp_ffsequence_mixin_of t s).
  Definition comp_ffsequenceMap (t s:ffsequenceMap) : ffsequenceMap :=
    Eval hnf in
      @FFSequence.Pack (fun A => t (s A)) (comp_ffsequence_class_of t s).

  Definition fsequence_comp t s :
    @fsequence (comp_ffsequenceMap t s) =
    fun _ _ => @fsequence _ _ _ \o functor (@fsequence _ _ _) := erefl.

  (* mult *)
  Definition mult_ffsequence_mixin_of R (idx:R) (op:Monoid.law idx)
             (t:ffsequenceMap): FFSequence.mixin_of (mult_functorMap op t).
  Proof.
    apply : (@FFSequence.Mixin
               _ ((fun _ _ =>
                     @fsequence _ _ _ \o
                                 functor (fun rma =>
                                            match rma with
                                            | (r,ma) => functor (pair r) ma
                                            end)) : FSequence (mult op t)))
    =>[m A B f x|m A x|A x|m n A x]/=.
    - rewrite -fsequence_functor_functor -!functorD. congr fsequence.
      apply : eq_functor =>[[r ma]]/=. by rewrite -!functorD.
    - rewrite morph_fsequence_def -!functorD. congr fsequence.
      apply : eq_functor =>[[r ma]]/=. by rewrite morph_functor.
    - by rewrite fsequence_idMap eq_functor_id // =>[[]].
    - rewrite functorD -fsequence_functor_functor -functorD fsequence_compMap.
      congr (functor (@fsequence _ _ _) (fsequence _)).
      apply : eq_functor =>[[r ma]]/=. by rewrite -functorD.
  Defined.
  Definition mult_ffsequence_class_of R (idx:R) (op:Monoid.law idx)
             (t:ffsequenceMap) : FFSequence.class_of (mult op t) :=
    FFSequence.Class (mult_ffsequence_mixin_of op t).
  Canonical mult_ffsequenceMap R (idx:R) (op:Monoid.law idx)
            (t:ffsequenceMap): ffsequenceMap :=
    Eval hnf in @FFSequence.Pack (mult op t) (mult_ffsequence_class_of op t).

  Definition fsequence_mult R (idx:R) (op:Monoid.law idx) (t:ffsequenceMap) :
    @fsequence (mult_ffsequenceMap op t) =
    fun _ _ f => fsequence (functor (fun rma =>
                                      match rma with
                                      | (r,ma) => functor (pair r) ma
                                      end) f)
  := erefl.
End FFSequence_canonicals.

(* ********************* *)

Module PF2Sequence.
  Record mixin_of (t:pfunctorMap) (f2sequence:F2Sequence t) :=
    Mixin {
        _: forall (m:functor2Map) A (x:m A),
          f2sequence _ _ (eta _ x) = functor (@eta _ _) x
      }.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : PFunctor.class_of t;
          mixin : FF2Sequence.mixin_of (Functor.Pack base);
          mixin2 : @mixin_of (PFunctor.Pack base)
                             (FF2Sequence.f2sequence mixin)
        }.
    Definition base2 t (c:class_of t): FF2Sequence.class_of t :=
      FF2Sequence.Class (mixin c).
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
    Definition ff2sequenceMap := FF2Sequence.Pack (base2 class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> PFunctor.class_of.
    Coercion base2 : class_of >-> FF2Sequence.class_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Coercion ff2sequenceMap : map >-> FF2Sequence.map.
    Canonical ff2sequenceMap.
    Notation pf2sequenceMap := map.
  End Exports.
End PF2Sequence.
Import PF2Sequence.Exports.

Section PF2Sequence_lemma.
  Variable (t:pf2sequenceMap).

  Lemma f2sequence_eta : forall (m:functor2Map) A (x:m A),
    f2sequence (eta t x) = functor (@eta _ _) x.
  Proof. rewrite /f2sequence. by case : t => func [b sm []]. Qed.

  (* morphism *)
  (* pure *)
  Definition f2sequence_pureMorphism_class_of (m:functor2Map) :
    @PureMorphism.class_of (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
                           (@f2sequence t m).
  Proof.
    apply : PureMorphism.Class => A x.
    by rewrite !eta_comp /= f2sequence_eta functor_eta.
  Defined.
  Definition f2sequnece_pureMorphism (m:functor2Map) : pureMorphism :=
    Eval hnf in
      @PureMorphism.Pack
        (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
        (@f2sequence t m) (f2sequence_pureMorphism_class_of m).

  (* pfunctor *)
  Definition f2sequence_pfunctorMorphism_class_of (m:functor2Map) :
    @PFunctorMorphism.class_of (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
                               (@f2sequence t m)
    := PFunctorMorphism.Class
         (f2sequence_pureMorphism_class_of m)
         (f2sequence_functorMorphism_class_of _ m).
  Definition f2sequnece_pfunctorMorphism (m:functor2Map) : pfunctorMorphism :=
    Eval hnf in
      @PFunctorMorphism.Pack
        (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
        (@f2sequence t m) (f2sequence_pfunctorMorphism_class_of m).
End PF2Sequence_lemma.

Definition eq_pf2sequenceMap (t:Type -> Type) (c d:PF2Sequence.class_of t) :=
  eq_pfunctorMap c d /\ eq_ff2sequenceMap c d.

Section PF2Sequence_canonicals.
  (* id *)
  Definition id_pf2sequence_mixin_of :
    @PF2Sequence.mixin_of
      id_pfunctorMap (FF2Sequence.f2sequence id_ff2sequence_mixin_of).
  Proof.
    apply : (@PF2Sequence.Mixin
               _ ((fun _ _ => id) : F2Sequence id_pfunctorMap))
    => m A x //. by rewrite functor_id.
  Defined.
  Definition id_pf2sequence_class_of : PF2Sequence.class_of id :=
    PF2Sequence.Class id_pf2sequence_mixin_of.
  Definition id_pf2sequenceMap : pf2sequenceMap :=
    Eval hnf in @PF2Sequence.Pack id id_pf2sequence_class_of.

  (* comp *)
  Definition comp_pf2sequnece_mixin_of (t s:pf2sequenceMap) :
    @PF2Sequence.mixin_of
      (comp_pfunctorMap t s)
      (FF2Sequence.f2sequence (comp_ff2sequence_mixin_of t s)).
  Proof.
    apply : (@PF2Sequence.Mixin
               _ ((fun _ _ => @f2sequence _ _ _ \o functor (@f2sequence _ _ _))
                  : F2Sequence (comp_pfunctorMap t s))) => m A x /=.
      by rewrite functor_eta !f2sequence_eta -functorD.
  Defined.
  Definition comp_pf2sequence_class_of (t s:pf2sequenceMap) :
    PF2Sequence.class_of (fun A => t (s A)) :=
    PF2Sequence.Class (comp_pf2sequnece_mixin_of t s).
  Definition comp_pf2sequenceMap (t s:pf2sequenceMap) : pf2sequenceMap :=
    Eval hnf in
      @PF2Sequence.Pack (fun A => t (s A)) (comp_pf2sequence_class_of t s).

  (* option *)
  Definition option_pf2sequence_mixin_of :
    @PF2Sequence.mixin_of option_pfunctorMap
                          (FF2Sequence.f2sequence option_ff2sequence_mixin_of).
  Proof.
    exact : (@PF2Sequence.Mixin
               _ (fun _ _ o =>
                    if o is Some x then functor (@Some _) x else eta _ None)).
  Defined.
  Definition option_pf2sequence_class_of : PF2Sequence.class_of option :=
    PF2Sequence.Class option_pf2sequence_mixin_of.
  Canonical option_f2sequenceMap : pf2sequenceMap :=
    Eval hnf in @PF2Sequence.Pack option option_pf2sequence_class_of.

  (* seq *)
  Definition seq_pf2sequence_mixin_of :
    @PF2Sequence.mixin_of seq_pfunctorMap
                          (FF2Sequence.f2sequence seq_ff2sequence_mixin_of).
  Proof.
    apply : (@PF2Sequence.Mixin
               _ (fun _ _ => foldr (functor2 cons) (eta _ [::]))) => m A x /=.
      by rewrite functor2_etar.
  Defined.
  Definition seq_pf2sequence_class_of : PF2Sequence.class_of seq :=
    PF2Sequence.Class seq_pf2sequence_mixin_of.
  Canonical seq_pf2sequenceMap : pf2sequenceMap :=
    Eval hnf in @PF2Sequence.Pack seq seq_pf2sequence_class_of.

  (* sumt *)
  Definition sumt_pf2sequence_mixin_of R (t:pf2sequenceMap):
    @PF2Sequence.mixin_of
      (sumt_pfunctorMap R t)
      (FF2Sequence.f2sequence (sumt_ff2sequence_mixin_of R t)).
  Proof.
    apply : (@PF2Sequence.Mixin
               _ ((fun m _ =>
                     @f2sequence _ _ _ \o functor (fun rma =>
                                          match rma with
                                          | inl r => eta _ (inl r)
                                          | inr ma => @functor m _ _ inr ma
                                          end))
                  : F2Sequence (sumt_pfunctorMap R t))) => m A x /=.
      by rewrite functor_eta eta_sumt f2sequence_eta -functorD.
  Defined.
  Definition sumt_pf2sequence_class_of R (t:pf2sequenceMap) :
    PF2Sequence.class_of (sumt R t) :=
    PF2Sequence.Class (sumt_pf2sequence_mixin_of R t).
  Canonical sumt_pf2sequenceMap R (t:pf2sequenceMap) : pf2sequenceMap :=
    Eval hnf in @PF2Sequence.Pack (sumt R t) (sumt_pf2sequence_class_of R t).

  (* mult *)
  Definition mult_pf2sequence_mixin_of R (idx:R) (op:Monoid.law idx)
             (t:pf2sequenceMap):
    @PF2Sequence.mixin_of (mult_pfunctorMap op t)
        (FF2Sequence.f2sequence (mult_ff2sequence_mixin_of op t)).
  Proof.
    apply : (@PF2Sequence.Mixin
               _ ((fun _ _ =>
                     @f2sequence _ _ _ \o
                                 functor (fun rma =>
                                            match rma with
                                            | (r,ma) => functor (pair r) ma
                                            end)) :
                    F2Sequence (mult_pfunctorMap op t))) => m A x /=.
      by rewrite !eta_mult functor_eta f2sequence_eta -functorD.
  Defined.
  Definition mult_pf2sequence_class_of R (idx:R) (op:Monoid.law idx)
             (t:pf2sequenceMap) : PF2Sequence.class_of (mult op t) :=
    PF2Sequence.Class (mult_pf2sequence_mixin_of op t).
  Canonical mult_pf2sequenceMap R (idx:R) (op:Monoid.law idx)
            (t:pf2sequenceMap): pf2sequenceMap :=
    Eval hnf in @PF2Sequence.Pack (mult op t) (mult_pf2sequence_class_of op t).
End PF2Sequence_canonicals.

(* ********************* *)

Module PPFSequence.
  Record mixin_of (t:pfunctorMap) (pfsequence:PFSequence t) :=
    Mixin {
        _: forall (m:pfunctorMap) A (x:m A),
          pfsequence _ _ (eta _ x) = functor (@eta _ _) x
      }.
  Definition pf2sequence_mixin_of t pfsequence (mixin:@mixin_of t pfsequence) :
    @PF2Sequence.mixin_of t pfsequence :=
    let: Mixin H := mixin in PF2Sequence.Mixin H.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : PFunctor.class_of t;
          mixin : FPFSequence.mixin_of (Functor.Pack base);
          mixin2 : @mixin_of (PFunctor.Pack base)
                             (FPFSequence.pfsequence mixin)
        }.
    Definition base2 t (class:class_of t): FPFSequence.class_of t :=
      FPFSequence.Class (mixin class).
    Definition pf2sequence_mixin t (class:class_of t):
      @PF2Sequence.mixin_of
        (PFunctor.Pack (base class))
        (FF2Sequence.f2sequence
           (FPFSequence.ff2sequence_mixin_of (mixin class))) :=
      let: Class _ (FPFSequence.Mixin _ _ _ _ _) m := class
      in pf2sequence_mixin_of m.
    Definition pf2sequence_class t (class:class_of t):
      @PF2Sequence.class_of t := PF2Sequence.Class (pf2sequence_mixin class).
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
    Definition ff2sequenceMap := FF2Sequence.Pack (base2 class).
    Definition fpfsequenceMap := FPFSequence.Pack (base2 class).
    Definition pf2sequenceMap := PF2Sequence.Pack (pf2sequence_class class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> PFunctor.class_of.
    Coercion base2 : class_of >-> FPFSequence.class_of.
    Coercion pf2sequence_class : class_of >-> PF2Sequence.class_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Coercion ff2sequenceMap : map >-> FF2Sequence.map.
    Canonical ff2sequenceMap.
    Coercion fpfsequenceMap : map >-> FPFSequence.map.
    Canonical fpfsequenceMap.
    Coercion pf2sequenceMap : map >-> PF2Sequence.map.
    Canonical pf2sequenceMap.
    Notation ppfsequenceMap := map.
  End Exports.
End PPFSequence.
Import PPFSequence.Exports.

Section PPFSequence_lemma.
  Variable (t:ppfsequenceMap).

  Lemma pfsequence_eta : forall (m:pfunctorMap) A (x:m A),
    pfsequence (eta t x) = functor (@eta _ _) x.
  Proof. rewrite /pfsequence. by case : t => func [b sm []]. Qed.

  (* morphism *)
  (* pure *)
  Definition pfsequence_pureMorphism_class_of (m:pfunctorMap) :
    @PureMorphism.class_of (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
                           (@pfsequence t m).
  Proof.
    apply : PureMorphism.Class => A x.
    by rewrite !eta_comp /= pfsequence_eta functor_eta.
  Defined.
  Definition pfsequnece_pureMorphism (m:pfunctorMap) : pureMorphism :=
    Eval hnf in
      @PureMorphism.Pack
        (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
        (@pfsequence t m) (pfsequence_pureMorphism_class_of m).

  (* pfunctor *)
  Definition pfsequence_pfunctorMorphism_class_of (m:pfunctorMap) :
    @PFunctorMorphism.class_of (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
                               (@pfsequence t m)
    := PFunctorMorphism.Class
         (pfsequence_pureMorphism_class_of m)
         (pfsequence_functorMorphism_class_of _ m).
  Definition pfsequence_pfunctorMorphism (m:pfunctorMap) : pfunctorMorphism :=
    Eval hnf in
      @PFunctorMorphism.Pack
        (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
        (@pfsequence t m) (pfsequence_pfunctorMorphism_class_of m).
End PPFSequence_lemma.

Definition eq_ppfsequenceMap (t:Type -> Type) (c d:PPFSequence.class_of t) :=
  eq_pfunctorMap c d /\ eq_fpfsequenceMap c d.

Section PPFSequence_canonicals.
  (* id *)
  Definition id_ppfsequence_mixin_of :
    @PPFSequence.mixin_of
      id_pfunctorMap (FPFSequence.pfsequence id_fpfsequence_mixin_of).
  Proof.
    apply : (@PPFSequence.Mixin
               _ ((fun _ _ => id) : PFSequence id_pfunctorMap))
    => m A x //. by rewrite functor_id.
  Defined.
  Definition id_ppfsequence_class_of : PPFSequence.class_of id :=
    PPFSequence.Class id_ppfsequence_mixin_of.
  Definition id_ppfsequenceMap : ppfsequenceMap :=
    Eval hnf in @PPFSequence.Pack id id_ppfsequence_class_of.

  (* comp *)
  Definition comp_ppfsequence_mixin_of (t s:ppfsequenceMap) :
    @PPFSequence.mixin_of
      (comp_pfunctorMap t s)
      (FPFSequence.pfsequence (comp_fpfsequence_mixin_of t s)).
  Proof.
    apply : (@PPFSequence.Mixin
               _ ((fun _ _ => @pfsequence _ _ _ \o functor (@pfsequence _ _ _))
                  : PFSequence (comp_pfunctorMap t s))) => m A x /=.
      by rewrite functor_eta !pfsequence_eta -functorD.
  Defined.
  Definition comp_ppfsequence_class_of (t s:ppfsequenceMap) :
    PPFSequence.class_of (fun A => t (s A)) :=
    PPFSequence.Class (comp_ppfsequence_mixin_of t s).
  Definition comp_ppfsequenceMap (t s:ppfsequenceMap) : ppfsequenceMap :=
    Eval hnf in
      @PPFSequence.Pack (fun A => t (s A)) (comp_ppfsequence_class_of t s).

  (* option *)
  Definition option_ppfsequence_mixin_of :
    @PPFSequence.mixin_of option_pfunctorMap
                          (FPFSequence.pfsequence option_fpfsequence_mixin_of).
  Proof.
    exact : (@PPFSequence.Mixin
               _ (fun _ _ o =>
                    if o is Some x then functor (@Some _) x else eta _ None)).
  Defined.
  Definition option_ppfsequence_class_of : PPFSequence.class_of option :=
    PPFSequence.Class option_ppfsequence_mixin_of.
  Canonical option_pfsequenceMap : ppfsequenceMap :=
    Eval hnf in @PPFSequence.Pack option option_ppfsequence_class_of.

  (* sumt *)
  Definition sumt_ppfsequence_mixin_of R (t:ppfsequenceMap):
    @PPFSequence.mixin_of
      (sumt_pfunctorMap R t)
      (FPFSequence.pfsequence (sumt_fpfsequence_mixin_of R t)).
  Proof.
    apply : (@PPFSequence.Mixin
               _ ((fun m _ =>
                     @pfsequence _ _ _ \o functor (fun rma =>
                                          match rma with
                                          | inl r => eta _ (inl r)
                                          | inr ma => @functor m _ _ inr ma
                                          end))
                  : PFSequence (sumt_pfunctorMap R t))) => m A x /=.
      by rewrite functor_eta eta_sumt pfsequence_eta -functorD.
  Defined.
  Definition sumt_ppfsequence_class_of R (t:ppfsequenceMap) :
    PPFSequence.class_of (sumt R t) :=
    PPFSequence.Class (sumt_ppfsequence_mixin_of R t).
  Canonical sumt_ppfsequenceMap R (t:ppfsequenceMap) : ppfsequenceMap :=
    Eval hnf in @PPFSequence.Pack (sumt R t) (sumt_ppfsequence_class_of R t).

  (* mult *)
  Definition mult_ppfsequence_mixin_of R (idx:R) (op:Monoid.law idx)
             (t:ppfsequenceMap):
    @PPFSequence.mixin_of (mult_pfunctorMap op t)
        (FPFSequence.pfsequence (mult_fpfsequence_mixin_of op t)).
  Proof.
    apply : (@PPFSequence.Mixin
               _ ((fun _ _ =>
                     @pfsequence _ _ _ \o
                                 functor (fun rma =>
                                            match rma with
                                            | (r,ma) => functor (pair r) ma
                                            end)) :
                    PFSequence (mult_pfunctorMap op t))) => m A x /=.
      by rewrite !eta_mult functor_eta pfsequence_eta -functorD.
  Defined.
  Definition mult_ppfsequence_class_of R (idx:R) (op:Monoid.law idx)
             (t:ppfsequenceMap) : PPFSequence.class_of (mult op t) :=
    PPFSequence.Class (mult_ppfsequence_mixin_of op t).
  Canonical mult_ppfsequenceMap R (idx:R) (op:Monoid.law idx)
            (t:ppfsequenceMap): ppfsequenceMap :=
    Eval hnf in @PPFSequence.Pack (mult op t) (mult_ppfsequence_class_of op t).
End PPFSequence_canonicals.

(* ********************* *)

Module PFSequence.
  Record mixin_of (t:pfunctorMap) (fsequence:FSequence t) :=
    Mixin {
        _: forall (m:pfunctorMap) A (x:m A),
          fsequence _ _ (eta _ x) = functor (@eta _ _) x
      }.
  Definition ppfsequence_mixin_of t fsequence (mixin:@mixin_of t fsequence) :
    @PPFSequence.mixin_of t fsequence :=
    let: Mixin H := mixin in PPFSequence.Mixin H.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : PFunctor.class_of t;
          mixin : FFSequence.mixin_of (Functor.Pack base);
          mixin2 : @mixin_of (PFunctor.Pack base)
                             (FFSequence.fsequence mixin)
        }.
    Definition base2 t (class:class_of t): FFSequence.class_of t :=
      FFSequence.Class (mixin class).
    Definition ppfsequence_mixin t (class:class_of t):
      @PPFSequence.mixin_of
        (PFunctor.Pack (base class))
        (FPFSequence.pfsequence
           (FFSequence.fpfsequence_mixin_of (mixin class))) :=
      let: Class _ (FFSequence.Mixin _ _ _ _ _) m := class
      in ppfsequence_mixin_of m.
    Definition ppfsequence_class t (class:class_of t) :
      @PPFSequence.class_of t := PPFSequence.Class (ppfsequence_mixin class).
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
    Definition ff2sequenceMap := FF2Sequence.Pack (base2 class).
    Definition fpfsequenceMap := FPFSequence.Pack (base2 class).
    Definition ffsequenceMap := FFSequence.Pack (base2 class).
    Definition pf2sequenceMap := PF2Sequence.Pack (ppfsequence_class class).
    Definition ppfsequenceMap := PPFSequence.Pack (ppfsequence_class class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> PFunctor.class_of.
    Coercion base2 : class_of >-> FFSequence.class_of.
    Coercion ppfsequence_class : class_of >-> PPFSequence.class_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Coercion ff2sequenceMap : map >-> FF2Sequence.map.
    Canonical ff2sequenceMap.
    Coercion ffsequenceMap : map >-> FFSequence.map.
    Canonical ffsequenceMap.
    Coercion pf2sequenceMap : map >-> PF2Sequence.map.
    Canonical pf2sequenceMap.
    Coercion ppfsequenceMap : map >-> PPFSequence.map.
    Canonical ppfsequenceMap.
    Notation pfsequenceMap := map.
  End Exports.
End PFSequence.
Import PFSequence.Exports.

Section PFSequence_lemma.
  Variable (t:pfsequenceMap).

  Lemma fsequence_eta : forall (m:pfunctorMap) A (x:m A),
    fsequence (eta t x) = functor (@eta _ _) x.
  Proof. rewrite /fsequence. by case : t => func [b sm []]. Qed.

  (* morphism *)
  (* pure *)
  Definition fsequence_pureMorphism_class_of (m:pfunctorMap) :
    @PureMorphism.class_of (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
                           (@fsequence t m).
  Proof.
    apply : PureMorphism.Class => A x.
    by rewrite !eta_comp /= fsequence_eta functor_eta.
  Defined.
  Definition fsequnece_pureMorphism (m:pfunctorMap) : pureMorphism :=
    Eval hnf in
      @PureMorphism.Pack
        (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
        (@fsequence t m) (fsequence_pureMorphism_class_of m).

  (* pfunctor *)
  Definition fsequence_pfunctorMorphism_class_of (m:pfunctorMap) :
    @PFunctorMorphism.class_of (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
                               (@fsequence t m)
    := PFunctorMorphism.Class
         (fsequence_pureMorphism_class_of m)
         (fsequence_functorMorphism_class_of _ m).
  Definition fsequnece_pfunctorMorphism (m:pfunctorMap) : pfunctorMorphism :=
    Eval hnf in
      @PFunctorMorphism.Pack
        (comp_pfunctorMap _ _) (comp_pfunctorMap _ _)
        (@fsequence t m) (fsequence_pfunctorMorphism_class_of m).
End PFSequence_lemma.

Definition eq_pfsequenceMap (t:Type -> Type) (c d:PFSequence.class_of t) :=
  eq_pfunctorMap c d /\ eq_ffsequenceMap c d.

Section PFSequence_canonicals.
  (* id *)
  Definition id_pfsequence_mixin_of :
    @PFSequence.mixin_of
      id_pfunctorMap (FFSequence.fsequence id_ffsequence_mixin_of).
  Proof.
    apply : (@PFSequence.Mixin
               _ ((fun _ _ => id) : FSequence id_pfunctorMap))
    => m A x //. by rewrite functor_id.
  Defined.
  Definition id_pfsequence_class_of : PFSequence.class_of id :=
    PFSequence.Class id_pfsequence_mixin_of.
  Definition id_pfsequenceMap : pfsequenceMap :=
    Eval hnf in @PFSequence.Pack id id_pfsequence_class_of.

  (* comp *)
  Definition comp_pfsequence_mixin_of (t s:pfsequenceMap) :
    @PFSequence.mixin_of
      (comp_pfunctorMap t s)
      (FFSequence.fsequence (comp_ffsequence_mixin_of t s)).
  Proof.
    apply : (@PFSequence.Mixin
               _ ((fun _ _ => @fsequence _ _ _ \o functor (@fsequence _ _ _))
                  : FSequence (comp_pfunctorMap t s))) => m A x /=.
      by rewrite functor_eta !fsequence_eta -functorD.
  Defined.
  Definition comp_pfsequence_class_of (t s:pfsequenceMap) :
    PFSequence.class_of (fun A => t (s A)) :=
    PFSequence.Class (comp_pfsequence_mixin_of t s).
  Definition comp_pfsequenceMap (t s:pfsequenceMap) : pfsequenceMap :=
    Eval hnf in
      @PFSequence.Pack (fun A => t (s A)) (comp_pfsequence_class_of t s).

  (* mult *)
  Definition mult_pfsequence_mixin_of R (idx:R) (op:Monoid.law idx)
             (t:pfsequenceMap):
    @PFSequence.mixin_of (mult_pfunctorMap op t)
        (FFSequence.fsequence (mult_ffsequence_mixin_of op t)).
  Proof.
    apply : (@PFSequence.Mixin
               _ ((fun _ _ =>
                     @fsequence _ _ _ \o
                                 functor (fun rma =>
                                            match rma with
                                            | (r,ma) => functor (pair r) ma
                                            end)) :
                    FSequence (mult_pfunctorMap op t))) => m A x /=.
      by rewrite !eta_mult functor_eta fsequence_eta -functorD.
  Defined.
  Definition mult_pfsequence_class_of R (idx:R) (op:Monoid.law idx)
             (t:pfsequenceMap) : PFSequence.class_of (mult op t) :=
    PFSequence.Class (mult_pfsequence_mixin_of op t).
  Canonical mult_pfsequenceMap R (idx:R) (op:Monoid.law idx)
            (t:pfsequenceMap): pfsequenceMap :=
    Eval hnf in @PFSequence.Pack (mult op t) (mult_pfsequence_class_of op t).
End PFSequence_canonicals.

(* ********************* *)

Module KF2Sequence.
  Record mixin_of (t:kleisliMap) (f2sequence:F2Sequence t) :=
    Mixin {
        _: forall (m:f2kleisliMap) A (x:t (t (m A))),
            f2sequence _ _ (mu x) =
            functor (@mu _ _) (f2sequence _ _ (functor (f2sequence _ _) x))
      }.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : Kleisli.class_of t;
          sMixin : FF2Sequence.mixin_of (Functor.Pack base);
          s2Mixin : @PF2Sequence.mixin_of
                      (PFunctor.Pack base) (FF2Sequence.f2sequence sMixin);
          mixin : @mixin_of (Kleisli.Pack base) (FF2Sequence.f2sequence sMixin)
        }.
    Definition base2 t (class:class_of t) : PF2Sequence.class_of t :=
      PF2Sequence.Class (s2Mixin class).
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
    Definition monadMap := Monad.Pack (base class).
    Definition kleisliMap := Kleisli.Pack (base class).
    Definition ff2sequenceMap := FF2Sequence.Pack (base2 class).
    Definition pf2sequenceMap := PF2Sequence.Pack (base2 class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Kleisli.class_of.
    Coercion base2 : class_of >-> PF2Sequence.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Coercion monadMap : map >-> Monad.map.
    Canonical monadMap.
    Coercion kleisliMap : map >-> Kleisli.map.
    Canonical kleisliMap.
    Coercion ff2sequenceMap : map >-> FF2Sequence.map.
    Canonical ff2sequenceMap.
    Coercion pf2sequenceMap : map >-> PF2Sequence.map.
    Canonical pf2sequenceMap.
    Notation kf2sequenceMap := map.
  End Exports.
End KF2Sequence.
Import KF2Sequence.Exports.

Section KF2Sequence_lemma.
  Variable (t:kf2sequenceMap).
  Let f2sequence := @f2sequence t.

  Lemma f2sequence_mu : forall (m:f2kleisliMap) A (x:t (t (m A))),
      f2sequence (@mu t _ x) =
      functor (@mu t _) (f2sequence (functor (@f2sequence _ _) x)).
  Proof. rewrite /f2sequence. by case : t => func [b sm s2m []]. Qed.
End KF2Sequence_lemma.

Definition eq_kf2sequenceMap
           (t:Type -> Type) (c d:KF2Sequence.class_of t) :=
  eq_kleisliMap c d /\ eq_pf2sequenceMap c d.

Definition f2comp_monad_class_of (t:kf2sequenceMap) (m:f2kleisliMap) :
  Monad.class_of (fun A => m (t A)).
Proof.
  apply : (@Monad.Class _ (comp_pfunctor_class_of m t)).
  apply : (@Monad.Mixin
             _ ((fun _ => functor (@mu _ _) \o (@mu _ _) \o
                                  functor (@f2sequence t m _)) :
                  Mu (comp_pfunctorMap m t)))
            =>/=[A x|A x|A x].
  - rewrite eta_comp /= functor_eta mu_eta f2sequence_eta -functorD.
    exact : (eq_functor_id (@mu_eta _ _)).
  - rewrite functor_comp eta_comp /= -functorD.
    rewrite (eq_functor (g:= @eta m _ \o functor (@eta t _)))=>[|y]/=.
    + rewrite functorD mu_functor_eta -functorD.
      exact : (eq_functor_id (@mu_functor_eta _ _)).
    + by rewrite functorD f2sequence_functor_eta.
  - rewrite !functor_mu -!functorD -mu_functor_mu -functorD. congr mu.
    apply : eq_functor => y /=. rewrite 2!functorD.
    rewrite f2sequence_functor_functor f2sequence_functor_mu !functor_mu.
    rewrite f2sequence_functor_functor -!functorD. congr mu.
    apply : eq_functor => z /=. rewrite f2sequence_mu -!functorD.
    exact : (eq_functor (@mu_functor_mu _ _)).
Defined.

Definition f2comp_kleisli_class_of (t:kf2sequenceMap) (m:f2kleisliMap) :
  Kleisli.class_of (fun A => m (t A)).
Proof.
  apply : (@Kleisli.Class
             _ (f2comp_monad_class_of t m) (comp_pfunctor_mixin_of _ _)).
  - apply : Kleisli.Mixin =>/= A B f x.
    rewrite !functor_comp /mu /= -!functorD.
    rewrite (eq_functor (g:= @mu t _ \o functor (functor f)))
    =>[|y]/=; [|by rewrite functor_mu].
    rewrite (eq_functor
               (g:=functor (functor (functor f)) \o @f2sequence t m _))
    =>[|y]/=; [|by rewrite f2sequence_functor_functor].
    rewrite 2!functorD. congr functor. by rewrite functor_mu.
Defined.
Definition f2comp_kleisliMap  (t:kf2sequenceMap) (m:f2kleisliMap) :=
  Eval hnf in @Kleisli.Pack (fun A => m (t A)) (f2comp_kleisli_class_of t m).

Definition mu_f2comp (t:kf2sequenceMap) (m:f2kleisliMap) :
  @mu (f2comp_kleisliMap t m) =
  (fun _ => functor (@mu _ _) \o (@mu _ _) \o functor (@f2sequence t m _))
  := erefl.
(*
Definition rcomp_hkleisliMap (m:kleisliMap) (t:f2KleisliMap) :=
  rcomp_kleisliMap (hkleisli m) t.
Definition rcomp_vkleisliMap (m:kleisliMap) (t:f2KleisliMap) :=
  rcomp_kleisliMap (vkleisli m) t.
*)
Section KF2Sequence_canonicals.
  (* id *)
  Definition id_kf2sequence_mixin_of :
    @KF2Sequence.mixin_of
      id_kleisliMap (FF2Sequence.f2sequence id_ff2sequence_mixin_of).
  Proof.
    apply : KF2Sequence.Mixin =>/= m A x. by rewrite !functor_id.
  Defined.
  Definition id_kf2sequence_class_of : KF2Sequence.class_of id.
  Proof.
    apply : KF2Sequence.Class id_kf2sequence_mixin_of.
    exact : id_pf2sequence_mixin_of.
  Defined.
  Definition id_kf2sequenceMap : kf2sequenceMap :=
    Eval hnf in @KF2Sequence.Pack id id_kf2sequence_class_of.

  (* option *)
  Definition option_kf2sequence_mixin_of :
    @KF2Sequence.mixin_of
      option_kleisliMap (FF2Sequence.f2sequence option_ff2sequence_mixin_of).
  Proof.
    apply : KF2Sequence.Mixin => m A [[x|]|]/=.
    - rewrite -!functorD. exact : eq_functor.
    - by rewrite -functorD functor_eta.
    - by rewrite functor_eta.
  Defined.
  Definition option_kf2sequence_class_of : KF2Sequence.class_of option.
  Proof.
    apply : KF2Sequence.Class option_kf2sequence_mixin_of.
    exact : option_pf2sequence_mixin_of.
  Defined.
  Definition option_kf2sequenceMap : kf2sequenceMap :=
    Eval hnf in @KF2Sequence.Pack option option_kf2sequence_class_of.
(*
  (* comp *)
*)
  (* seq *)
  Definition seq_kf2sequence_mixin_of :
    @KF2Sequence.mixin_of
      seq_kleisliMap (FF2Sequence.f2sequence seq_ff2sequence_mixin_of).
  Proof.
    apply : KF2Sequence.Mixin =>/= m A.
    elim =>[|s ss IH]; [by rewrite functor_eta|]. rewrite mu_seq /= foldr_cat.
    rewrite IH foldr_map -functor2Dr.
    elim : s =>[|x s /=->]//=; [by rewrite functor2_etal|].
        by rewrite -functor3Dr -functor3Dl.
  Defined.
  Definition seq_kf2sequence_class_of : KF2Sequence.class_of seq.
  Proof.
    apply : KF2Sequence.Class seq_kf2sequence_mixin_of.
    exact : seq_pf2sequence_mixin_of.
  Defined.
  Definition seq_kf2sequenceMap : kf2sequenceMap :=
    Eval hnf in @KF2Sequence.Pack seq seq_kf2sequence_class_of.

  (* sumt *)
  Definition sumt_kf2sequence_mixin_of R (t:kf2sequenceMap):
    @KF2Sequence.mixin_of
      (sumt_kleisliMap R t)
      (FF2Sequence.f2sequence (sumt_ff2sequence_mixin_of R t)).
  Proof.
    apply : KF2Sequence.Mixin => m A x /=.
    - rewrite functor_mu f2sequence_mu [in RHS]functorD.
      rewrite -(@f2sequence_functor_functor t) -!functorD. congr functor.
      congr f2sequence. apply : eq_functor =>[[r|y]]/=.
      + by rewrite functor_eta f2sequence_eta !functor_eta.
      + by rewrite -functorD eq_functor_id.
  Defined.
  Definition sumt_kf2sequence_class_of R (t:kf2sequenceMap) :
    KF2Sequence.class_of (sumt R t).
  Proof.
    apply : KF2Sequence.Class (sumt_kf2sequence_mixin_of R t).
    exact : sumt_pf2sequence_mixin_of.
  Defined.
  Definition sumt_kf2sequenceMap R (t:kf2sequenceMap) : kf2sequenceMap :=
    Eval hnf in
      @KF2Sequence.Pack (sumt R t) (sumt_kf2sequence_class_of R t).

  (* mult *)
  Definition mult_kf2sequence_mixin_of R (idx:R) (op:Monoid.law idx)
             (t:kf2sequenceMap):
    @KF2Sequence.mixin_of
      (mult_kleisliMap op t)
      (FF2Sequence.f2sequence (mult_ff2sequence_mixin_of op t)).
  Proof.
    apply : KF2Sequence.Mixin => m A x /=.
    - rewrite functor_mu f2sequence_mu [in RHS]functorD. congr functor.
      rewrite -(@f2sequence_functor_functor t) -!functorD. congr f2sequence.
      apply : eq_functor =>[[r ma]]/=. rewrite -!functorD.
      rewrite (eq_functor
                 (g:=functor
                       (fun bx : _ * _ => let (b,x) := bx in (op r b,x))))=>//.
      rewrite -f2sequence_functor_functor -functorD. congr f2sequence.
      apply : eq_functor =>[[s a]]/=. by rewrite -functorD.
  Defined.
  Definition mult_kf2sequence_class_of R (idx:R) (op:Monoid.law idx)
             (t:kf2sequenceMap) : KF2Sequence.class_of (mult op t).
  Proof.
    apply : KF2Sequence.Class (mult_kf2sequence_mixin_of op t).
    exact : mult_pf2sequence_mixin_of.
  Defined.
  Definition mult_kf2sequenceMap R (idx:R) (op:Monoid.law idx)
             (t:kf2sequenceMap) : kf2sequenceMap :=
    Eval hnf in
      @KF2Sequence.Pack (mult op t) (mult_kf2sequence_class_of op t).  
End KF2Sequence_canonicals.

(* ********************* *)

Module KPFSequence.
  Record mixin_of (t:kleisliMap) (pfsequence:PFSequence t) :=
    Mixin {
        _: forall (m:kleisliMap) A (x:t (t (m A))),
            pfsequence _ _ (mu x) =
            functor (@mu _ _) (pfsequence _ _ (functor (pfsequence _ _) x))
      }.
  Definition kf2sequence_mixin_of t pfsequence (mixin:@mixin_of t pfsequence) :
    @KF2Sequence.mixin_of t pfsequence :=
    let: Mixin H := mixin in KF2Sequence.Mixin H.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : Kleisli.class_of t;
          sMixin : FPFSequence.mixin_of (Functor.Pack base);
          s2Mixin : @PPFSequence.mixin_of
                      (PFunctor.Pack base) (FPFSequence.pfsequence sMixin);
          mixin : @mixin_of (Kleisli.Pack base) (FPFSequence.pfsequence sMixin)
        }.
    Definition base2 t (class:class_of t) : PPFSequence.class_of t :=
      PPFSequence.Class (s2Mixin class).
    Definition kf2sequence_mixin t (class:class_of t) :
      @KF2Sequence.mixin_of
        (Kleisli.Pack (base class))
        (FF2Sequence.f2sequence
           (FPFSequence.ff2sequence_mixin_of (sMixin class))) :=
      let: Class _ (FPFSequence.Mixin _ _ _ _ _)
                 (PPFSequence.Mixin _) m := class
      in kf2sequence_mixin_of m.
    Definition kf2sequence_class t (c:class_of t): KF2Sequence.class_of t.
    Proof.
      apply : KF2Sequence.Class (kf2sequence_mixin c).
      move : (PPFSequence.pf2sequence_mixin_of (s2Mixin c)).
        by case : (sMixin c).
    Defined.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
    Definition monadMap := Monad.Pack (base class).
    Definition kleisliMap := Kleisli.Pack (base class).
    Definition ff2sequenceMap := FF2Sequence.Pack (kf2sequence_class class).
    Definition fpfsequenceMap := FPFSequence.Pack (base2 class).
    Definition pf2sequenceMap := PF2Sequence.Pack (kf2sequence_class class).
    Definition ppfsequenceMap := PPFSequence.Pack (base2 class).
    Definition kf2sequenceMap := KF2Sequence.Pack (kf2sequence_class class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Kleisli.class_of.
    Coercion base2 : class_of >-> PPFSequence.class_of.
    Coercion kf2sequence_class : class_of >-> KF2Sequence.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Coercion monadMap : map >-> Monad.map.
    Canonical monadMap.
    Coercion kleisliMap : map >-> Kleisli.map.
    Canonical kleisliMap.
    Coercion ff2sequenceMap : map >-> FF2Sequence.map.
    Canonical ff2sequenceMap.
    Coercion fpfsequenceMap : map >-> FPFSequence.map.
    Canonical fpfsequenceMap.
    Coercion pf2sequenceMap : map >-> PF2Sequence.map.
    Canonical pf2sequenceMap.
    Coercion ppfsequenceMap : map >-> PPFSequence.map.
    Canonical ppfsequenceMap.
    Coercion kf2sequenceMap : map >-> KF2Sequence.map.
    Canonical kf2sequenceMap.
    Notation kpfsequenceMap := map.
  End Exports.
End KPFSequence.
Import KPFSequence.Exports.

Section KPFSequence_lemma.
  Variable (t:kpfsequenceMap).
  Let pfsequence := @pfsequence t.

  Lemma pfsequence_mu : forall (m:kleisliMap) A (x:t (t (m A))),
      pfsequence (@mu t _ x) =
      functor (@mu t _) (pfsequence (functor (@pfsequence _ _) x)).
  Proof. rewrite /pfsequence. by case : t => func [b sm s2m []]. Qed.
End KPFSequence_lemma.

Definition eq_kpfsequenceMap
           (t:Type -> Type) (c d:KPFSequence.class_of t) :=
  eq_kleisliMap c d /\ eq_ppfsequenceMap c d.

Definition pfcomp_monad_class_of (t:kpfsequenceMap) (m:kleisliMap) :
  Monad.class_of (fun A => m (t A)).
Proof.
  apply : (@Monad.Class _ (comp_pfunctor_class_of m t)).
  apply : (@Monad.Mixin
             _ ((fun _ => functor (@mu _ _) \o (@mu _ _) \o
                                  functor (@pfsequence t m _)) :
                  Mu (comp_pfunctorMap m t)))
            =>/=[A x|A x|A x].
  - rewrite eta_comp /= functor_eta mu_eta pfsequence_eta -functorD.
    exact : (eq_functor_id (@mu_eta _ _)).
  - rewrite functor_comp eta_comp /= -functorD.
    rewrite (eq_functor (g:= @eta m _ \o functor (@eta t _)))=>[|y]/=.
    + rewrite functorD mu_functor_eta -functorD.
      exact : (eq_functor_id (@mu_functor_eta _ _)).
    + by rewrite functorD pfsequence_functor_eta.
  - rewrite !functor_mu -!functorD -mu_functor_mu -functorD. congr mu.
    apply : eq_functor => y /=. rewrite 2!functorD.
    rewrite pfsequence_functor_functor pfsequence_functor_mu !functor_mu.
    rewrite pfsequence_functor_functor -!functorD. congr mu.
    apply : eq_functor => z /=. rewrite pfsequence_mu -!functorD.
    exact : (eq_functor (@mu_functor_mu _ _)).
Defined.

Definition pfcomp_kleisli_class_of (t:kpfsequenceMap) (m:kleisliMap) :
  Kleisli.class_of (fun A => m (t A)).
Proof.
  apply : (@Kleisli.Class
             _ (pfcomp_monad_class_of t m) (comp_pfunctor_mixin_of _ _)).
  - apply : Kleisli.Mixin =>/= A B f x.
    rewrite !functor_comp /mu /= -!functorD.
    rewrite (eq_functor (g:= @mu t _ \o functor (functor f)))
    =>[|y]/=; [|by rewrite functor_mu].
    rewrite (eq_functor
               (g:=functor (functor (functor f)) \o @pfsequence t m _))
    =>[|y]/=; [|by rewrite pfsequence_functor_functor].
    rewrite 2!functorD. congr functor. by rewrite functor_mu.
Defined.
Definition pfcomp_kleisliMap  (t:kpfsequenceMap) (m:kleisliMap) :=
  Eval hnf in @Kleisli.Pack (fun A => m (t A)) (pfcomp_kleisli_class_of t m).

Definition mu_pfcomp (t:kpfsequenceMap) (m:kleisliMap) :
  @mu (pfcomp_kleisliMap t m) =
  (fun _ => functor (@mu _ _) \o (@mu _ _) \o functor (@pfsequence t m _))
  := erefl.
(*
Definition rcomp_hkleisliMap (m:kleisliMap) (t:f2KleisliMap) :=
  rcomp_kleisliMap (hkleisli m) t.
Definition rcomp_vkleisliMap (m:kleisliMap) (t:f2KleisliMap) :=
  rcomp_kleisliMap (vkleisli m) t.
*)
Section KPFSequence_canonicals.
  (* id *)
  Definition id_kpfsequence_mixin_of :
    @KPFSequence.mixin_of
      id_kleisliMap (FPFSequence.pfsequence id_fpfsequence_mixin_of).
  Proof.
    apply : KPFSequence.Mixin =>/= m A x. by rewrite !functor_id.
  Defined.
  Definition id_kpfsequence_class_of : KPFSequence.class_of id.
  Proof.
    apply : KPFSequence.Class id_kpfsequence_mixin_of.
    exact : id_ppfsequence_mixin_of.
  Defined.
  Definition id_kpfsequenceMap : kpfsequenceMap :=
    Eval hnf in @KPFSequence.Pack id id_kpfsequence_class_of.

  (* option *)
  Definition option_kpfsequence_mixin_of :
    @KPFSequence.mixin_of
      option_kleisliMap (FPFSequence.pfsequence option_fpfsequence_mixin_of).
  Proof.
    apply : KPFSequence.Mixin => m A [[x|]|]/=.
    - rewrite -!functorD. exact : eq_functor.
    - by rewrite -functorD functor_eta.
    - by rewrite functor_eta.
  Defined.
  Definition option_kpfsequence_class_of : KPFSequence.class_of option.
  Proof.
    apply : KPFSequence.Class option_kpfsequence_mixin_of.
    exact : option_ppfsequence_mixin_of.
  Defined.
  Definition option_kpfsequenceMap : kpfsequenceMap :=
    Eval hnf in @KPFSequence.Pack option option_kpfsequence_class_of.

  (* comp *)
  Definition comp_kpfsequence_mixin_of (t s:kpfsequenceMap) :
    @KPFSequence.mixin_of
      (pfcomp_kleisliMap s t)
      (FPFSequence.pfsequence (comp_fpfsequence_mixin_of t s)).
  Proof.
    apply : KPFSequence.Mixin => m A x /=.
    rewrite functor_comp mu_pfcomp -functorD functor_mu pfsequence_mu.
    have -> : forall f x,
        functor (functor (@mu s A) \o @mu t _ \o functor f) x =
        functor (@mu _ _ \o (functor (functor (@mu _ _) \o f))) x
    =>[B F f y|];
        [by apply : eq_functor => z /=; rewrite functor_mu -functorD|].
    rewrite [in RHS]functorD -pfsequence_functor_functor. congr functor.
    congr pfsequence. rewrite -!functorD. apply : eq_functor => y /=.
    rewrite (eq_functor
               (g:= functor (@mu _ _) \o
                            (@pfsequence s _ _ \o
                                         functor (@pfsequence _ _ _))));
      [|exact : pfsequence_mu].
    rewrite functorD pfsequence_functor_functor [in RHS]functorD. congr functor.
    rewrite 2!functorD -pfsequence_functor_functor -!pfsequence_compMap.
    by rewrite -(morph_pfsequence (pfsequence_pfunctorMorphism_class_of _ _)).
  Defined.
  Definition comp_kpfsequence_class_of (t s:kpfsequenceMap) :
    KPFSequence.class_of (fun A => t (s A)).
  Proof.
    apply : KPFSequence.Class (comp_kpfsequence_mixin_of t s).
    exact : comp_ppfsequence_mixin_of.
  Defined.
  Definition comp_kpfsequenceMap (t s:kpfsequenceMap) : kpfsequenceMap :=
    Eval hnf in @KPFSequence.Pack (fun A => t (s A))
                                  (comp_kpfsequence_class_of t s).

  (* sumt *)
  Definition sumt_kpfsequence_mixin_of R (t:kpfsequenceMap):
    @KPFSequence.mixin_of
      (sumt_kleisliMap R t)
      (FPFSequence.pfsequence (sumt_fpfsequence_mixin_of R t)).
  Proof.
    apply : KPFSequence.Mixin => m A x /=.
    - rewrite functor_mu pfsequence_mu [in RHS]functorD.
      rewrite -(@pfsequence_functor_functor t) -!functorD. congr functor.
      congr pfsequence. apply : eq_functor =>[[r|y]]/=.
      + by rewrite !functor_eta pfsequence_eta !functor_eta.
      + by rewrite -functorD eq_functor_id.
  Defined.
  Definition sumt_kpfsequence_class_of R (t:kpfsequenceMap) :
    KPFSequence.class_of (sumt R t).
  Proof.
    apply : KPFSequence.Class (sumt_kpfsequence_mixin_of R t).
    exact : sumt_ppfsequence_mixin_of.
  Defined.
  Definition sumt_kpfsequenceMap R (t:kpfsequenceMap) : kpfsequenceMap :=
    Eval hnf in
      @KPFSequence.Pack (sumt R t) (sumt_kpfsequence_class_of R t).

  (* mult *)
  Definition mult_kpfsequence_mixin_of R (idx:R) (op:Monoid.law idx)
             (t:kpfsequenceMap):
    @KPFSequence.mixin_of
      (mult_kleisliMap op t)
      (FPFSequence.pfsequence (mult_fpfsequence_mixin_of op t)).
  Proof.
    apply : KPFSequence.Mixin => m A x /=.
    - rewrite functor_mu pfsequence_mu [in RHS]functorD. congr functor.
      rewrite -(@pfsequence_functor_functor t) -!functorD. congr pfsequence.
      apply : eq_functor =>[[r ma]]/=. rewrite -!functorD.
      rewrite (eq_functor
                 (g:=functor
                       (fun bx : _ * _ => let (b,x) := bx in (op r b,x))))=>//.
      rewrite -pfsequence_functor_functor -functorD. congr pfsequence.
      apply : eq_functor =>[[s a]]/=. by rewrite -functorD.
  Defined.
  Definition mult_kpfsequence_class_of R (idx:R) (op:Monoid.law idx)
             (t:kpfsequenceMap) : KPFSequence.class_of (mult op t).
  Proof.
    apply : KPFSequence.Class (mult_kpfsequence_mixin_of op t).
    exact : mult_ppfsequence_mixin_of.
  Defined.
  Definition mult_kpfsequenceMap R (idx:R) (op:Monoid.law idx)
             (t:kpfsequenceMap) : kpfsequenceMap :=
    Eval hnf in
      @KPFSequence.Pack (mult op t) (mult_kpfsequence_class_of op t).  
End KPFSequence_canonicals.

(* ********************* *)

Module KFSequence.
  Record mixin_of (t:kleisliMap) (fsequence:FSequence t) :=
    Mixin {
        _: forall (m:kleisliMap) A (x:t (t (m A))),
            fsequence _ _ (mu x) =
            functor (@mu _ _) (fsequence _ _ (functor (fsequence _ _) x))
      }.
  Definition kpfsequence_mixin_of t fsequence (mixin:@mixin_of t fsequence) :
    @KPFSequence.mixin_of t fsequence :=
    let: Mixin H := mixin in KPFSequence.Mixin H.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : Kleisli.class_of t;
          sMixin : FFSequence.mixin_of (Functor.Pack base);
          s2Mixin : @PFSequence.mixin_of
                      (PFunctor.Pack base) (FFSequence.fsequence sMixin);
          mixin : @mixin_of (Kleisli.Pack base) (FFSequence.fsequence sMixin)
        }.
    Definition base2 t (class:class_of t) : PFSequence.class_of t :=
      PFSequence.Class (s2Mixin class).
    Definition kpfsequence_mixin t (class:class_of t) :
      @KPFSequence.mixin_of
        (Kleisli.Pack (base class))
        (FPFSequence.pfsequence
           (FFSequence.fpfsequence_mixin_of (sMixin class))) :=
      let: Class _ (FFSequence.Mixin _ _ _ _ _)
                 (PFSequence.Mixin _) m := class
      in kpfsequence_mixin_of m.
    Definition kpfsequence_class t (c:class_of t): KPFSequence.class_of t.
    Proof.
      apply : KPFSequence.Class (kpfsequence_mixin c).
      move : (PFSequence.ppfsequence_mixin_of (s2Mixin c)).
        by case : (sMixin c).
    Defined.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
    Definition monadMap := Monad.Pack (base class).
    Definition kleisliMap := Kleisli.Pack (base class).
    Definition ff2sequenceMap := FF2Sequence.Pack (kpfsequence_class class).
    Definition fpfsequenceMap := FPFSequence.Pack (kpfsequence_class class).
    Definition ffsequenceMap := FFSequence.Pack (base2 class).
    Definition pf2sequenceMap := PF2Sequence.Pack (kpfsequence_class class).
    Definition ppfsequenceMap := PPFSequence.Pack (kpfsequence_class class).
    Definition pfsequenceMap := PFSequence.Pack (base2 class).
    Definition kf2sequenceMap := KF2Sequence.Pack (kpfsequence_class class).
    Definition kpfsequenceMap := KPFSequence.Pack (kpfsequence_class class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> Kleisli.class_of.
    Coercion base2 : class_of >-> PFSequence.class_of.
    Coercion kpfsequence_class : class_of >-> KPFSequence.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Coercion monadMap : map >-> Monad.map.
    Canonical monadMap.
    Coercion kleisliMap : map >-> Kleisli.map.
    Canonical kleisliMap.
    Coercion ff2sequenceMap : map >-> FF2Sequence.map.
    Canonical ff2sequenceMap.
    Coercion fpfsequenceMap : map >-> FPFSequence.map.
    Canonical fpfsequenceMap.
    Coercion ffsequenceMap : map >-> FFSequence.map.
    Canonical ffsequenceMap.
    Coercion pf2sequenceMap : map >-> PF2Sequence.map.
    Canonical pf2sequenceMap.
    Coercion ppfsequenceMap : map >-> PPFSequence.map.
    Canonical ppfsequenceMap.
    Coercion pfsequenceMap : map >-> PFSequence.map.
    Canonical pfsequenceMap.
    Coercion kf2sequenceMap : map >-> KF2Sequence.map.
    Canonical kf2sequenceMap.
    Coercion kpfsequenceMap : map >-> KPFSequence.map.
    Canonical kpfsequenceMap.
    Notation kfsequenceMap := map.
  End Exports.
End KFSequence.
Import KFSequence.Exports.

Section KFSequence_lemma.
  Variable (t:kfsequenceMap).
  Let fsequence := @fsequence t.

  Lemma fsequence_mu : forall (m:kleisliMap) A (x:t (t (m A))),
      fsequence (@mu t _ x) =
      functor (@mu t _) (fsequence (functor (@fsequence _ _) x)).
  Proof. rewrite /fsequence. by case : t => func [b sm s2m []]. Qed.
End KFSequence_lemma.

Definition eq_kfsequenceMap
           (t:Type -> Type) (c d:KFSequence.class_of t) :=
  eq_kleisliMap c d /\ eq_pfsequenceMap c d.

Definition fcomp_monad_class_of (t:kfsequenceMap) (m:kleisliMap) :
  Monad.class_of (fun A => m (t A)).
Proof.
  apply : (@Monad.Class _ (comp_pfunctor_class_of m t)).
  apply : (@Monad.Mixin
             _ ((fun _ => functor (@mu _ _) \o (@mu _ _) \o
                                  functor (@fsequence t m _)) :
                  Mu (comp_pfunctorMap m t)))
            =>/=[A x|A x|A x].
  - rewrite eta_comp /= functor_eta mu_eta fsequence_eta -functorD.
    exact : (eq_functor_id (@mu_eta _ _)).
  - rewrite functor_comp eta_comp /= -functorD.
    rewrite (eq_functor (g:= @eta m _ \o functor (@eta t _)))=>[|y]/=.
    + rewrite functorD mu_functor_eta -functorD.
      exact : (eq_functor_id (@mu_functor_eta _ _)).
    + by rewrite functorD fsequence_functor_eta.
  - rewrite !functor_mu -!functorD -mu_functor_mu -functorD. congr mu.
    apply : eq_functor => y /=. rewrite 2!functorD.
    rewrite fsequence_functor_functor fsequence_functor_mu !functor_mu.
    rewrite fsequence_functor_functor -!functorD. congr mu.
    apply : eq_functor => z /=. rewrite fsequence_mu -!functorD.
    exact : (eq_functor (@mu_functor_mu _ _)).
Defined.

Definition fcomp_kleisli_class_of (t:kfsequenceMap) (m:kleisliMap) :
  Kleisli.class_of (fun A => m (t A)).
Proof.
  apply : (@Kleisli.Class
             _ (fcomp_monad_class_of t m) (comp_pfunctor_mixin_of _ _)).
  - apply : Kleisli.Mixin =>/= A B f x.
    rewrite !functor_comp /mu /= -!functorD.
    rewrite (eq_functor (g:= @mu t _ \o functor (functor f)))
    =>[|y]/=; [|by rewrite functor_mu].
    rewrite (eq_functor
               (g:=functor (functor (functor f)) \o @fsequence t m _))
    =>[|y]/=; [|by rewrite fsequence_functor_functor].
    rewrite 2!functorD. congr functor. by rewrite functor_mu.
Defined.
Definition fcomp_kleisliMap  (t:kfsequenceMap) (m:kleisliMap) :=
  Eval hnf in @Kleisli.Pack (fun A => m (t A)) (fcomp_kleisli_class_of t m).

Definition mu_fcomp (t:kfsequenceMap) (m:kleisliMap) :
  @mu (fcomp_kleisliMap t m) =
  (fun _ => functor (@mu _ _) \o (@mu _ _) \o functor (@fsequence t m _))
  := erefl.
(*
Definition rcomp_hkleisliMap (m:kleisliMap) (t:f2KleisliMap) :=
  rcomp_kleisliMap (hkleisli m) t.
Definition rcomp_vkleisliMap (m:kleisliMap) (t:f2KleisliMap) :=
  rcomp_kleisliMap (vkleisli m) t.
*)
Section KFSequence_canonicals.
  (* id *)
  Definition id_kfsequence_mixin_of :
    @KFSequence.mixin_of
      id_kleisliMap (FFSequence.fsequence id_ffsequence_mixin_of).
  Proof.
    apply : KFSequence.Mixin =>/= m A x. by rewrite !functor_id.
  Defined.
  Definition id_kfsequence_class_of : KFSequence.class_of id.
  Proof.
    apply : KFSequence.Class id_kfsequence_mixin_of.
    exact : id_pfsequence_mixin_of.
  Defined.
  Definition id_kfsequenceMap : kfsequenceMap :=
    Eval hnf in @KFSequence.Pack id id_kfsequence_class_of.

  (* comp *)
  Definition comp_kfsequence_mixin_of (t s:kfsequenceMap) :
    @KFSequence.mixin_of
      (fcomp_kleisliMap s t)
      (FFSequence.fsequence (comp_ffsequence_mixin_of t s)).
  Proof.
    apply : KFSequence.Mixin => m A x /=.
    rewrite functor_comp mu_fcomp -functorD functor_mu fsequence_mu.
    have -> : forall f x,
        functor (functor (@mu s A) \o @mu t _ \o functor f) x =
        functor (@mu _ _ \o (functor (functor (@mu _ _) \o f))) x
    =>[B F f y|];
        [by apply : eq_functor => z /=; rewrite functor_mu -functorD|].
    rewrite [in RHS]functorD -fsequence_functor_functor. congr functor.
    congr fsequence. rewrite -!functorD. apply : eq_functor => y /=.
    rewrite (eq_functor
               (g:= functor (@mu _ _) \o
                            (@fsequence s _ _ \o
                                         functor (@fsequence _ _ _))));
      [|exact : fsequence_mu].
    rewrite functorD fsequence_functor_functor [in RHS]functorD. congr functor.
    rewrite 2!functorD -fsequence_functor_functor -!fsequence_compMap.
    by rewrite -(morph_fsequence (fsequence_pfunctorMorphism_class_of _ _)).
  Defined.
  Definition comp_kfsequence_class_of (t s:kfsequenceMap) :
    KFSequence.class_of (fun A => t (s A)).
  Proof.
    apply : KFSequence.Class (comp_kfsequence_mixin_of t s).
    exact : comp_pfsequence_mixin_of.
  Defined.
  Definition comp_kfsequenceMap (t s:kfsequenceMap) : kfsequenceMap :=
    Eval hnf in @KFSequence.Pack (fun A => t (s A))
                                  (comp_kfsequence_class_of t s).

  (* mult *)
  Definition mult_kfsequence_mixin_of R (idx:R) (op:Monoid.law idx)
             (t:kfsequenceMap):
    @KFSequence.mixin_of
      (mult_kleisliMap op t)
      (FFSequence.fsequence (mult_ffsequence_mixin_of op t)).
  Proof.
    apply : KFSequence.Mixin => m A x /=.
    - rewrite functor_mu fsequence_mu [in RHS]functorD. congr functor.
      rewrite -(@fsequence_functor_functor t) -!functorD. congr fsequence.
      apply : eq_functor =>[[r ma]]/=. rewrite -!functorD.
      rewrite (eq_functor
                 (g:=functor
                       (fun bx : _ * _ => let (b,x) := bx in (op r b,x))))=>//.
      rewrite -fsequence_functor_functor -functorD. congr fsequence.
      apply : eq_functor =>[[s a]]/=. by rewrite -functorD.
  Defined.
  Definition mult_kfsequence_class_of R (idx:R) (op:Monoid.law idx)
             (t:kfsequenceMap) : KFSequence.class_of (mult op t).
  Proof.
    apply : KFSequence.Class (mult_kfsequence_mixin_of op t).
    exact : mult_pfsequence_mixin_of.
  Defined.
  Definition mult_kfsequenceMap R (idx:R) (op:Monoid.law idx)
             (t:kfsequenceMap) : kfsequenceMap :=
    Eval hnf in
      @KFSequence.Pack (mult op t) (mult_kfsequence_class_of op t).  
End KFSequence_canonicals.

(* ********************* *)

Module F2KF2Sequence.
  Record mixin_of (t:f2kleisliMap) (f2sequence:F2Sequence t) :=
    Mixin {
        _: forall (m:f2kleisliMap) A B C (f:A -> B -> C) x y,
            f2sequence m _ (functor2 (functor2 f) x y) =
            functor2 (functor2 f) (f2sequence _ _ x) (f2sequence _ _ y)
      }.
  Section ClassDef.
    Record class_of (t:Type -> Type) :=
      Class {
          base : F2Kleisli.class_of t;
          sMixin : FF2Sequence.mixin_of (Functor.Pack base);
          s2Mixin : @PF2Sequence.mixin_of
                      (PFunctor.Pack base) (FF2Sequence.f2sequence sMixin);
          s3Mixin : @KF2Sequence.mixin_of
                      (Kleisli.Pack base) (FF2Sequence.f2sequence sMixin);
          mixin : @mixin_of (F2Kleisli.Pack base)
                           (FF2Sequence.f2sequence sMixin)
        }.
    Definition base2 t (class:class_of t) : KF2Sequence.class_of t :=
      KF2Sequence.Class (s2Mixin class) (s3Mixin class).
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition pureMap := Pure.Pack (base class).
    Definition functorMap := Functor.Pack (base class).
    Definition wpfunctorMap := WPFunctor.Pack (base class).
    Definition pfunctorMap := PFunctor.Pack (base class).
    Definition functor2Map := Functor2.Pack (base class).
    Definition monadMap := Monad.Pack (base class).
    Definition kleisliMap := Kleisli.Pack (base class).
    Definition f2kleisliMap := F2Kleisli.Pack (base class).
    Definition ff2sequenceMap := FF2Sequence.Pack (base2 class).
    Definition pf2sequenceMap := PF2Sequence.Pack (base2 class).
    Definition kf2sequenceMap := KF2Sequence.Pack (base2 class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> F2Kleisli.class_of.
    Coercion base2 : class_of >-> KF2Sequence.class_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMap : map >-> Pure.map.
    Canonical pureMap.
    Coercion functorMap : map >-> Functor.map.
    Canonical functorMap.
    Coercion wpfunctorMap : map >-> WPFunctor.map.
    Canonical wpfunctorMap.
    Coercion pfunctorMap : map >-> PFunctor.map.
    Canonical pfunctorMap.
    Coercion functor2Map : map >-> Functor2.map.
    Canonical functor2Map.
    Coercion monadMap : map >-> Monad.map.
    Canonical monadMap.
    Coercion kleisliMap : map >-> Kleisli.map.
    Canonical kleisliMap.
    Coercion f2kleisliMap : map >-> F2Kleisli.map.
    Canonical f2kleisliMap.
    Coercion ff2sequenceMap : map >-> FF2Sequence.map.
    Canonical ff2sequenceMap.
    Coercion pf2sequenceMap : map >-> PF2Sequence.map.
    Canonical pf2sequenceMap.
    Coercion kf2sequenceMap : map >-> KF2Sequence.map.
    Canonical kf2sequenceMap.
    Notation f2kf2sequenceMap := map.
  End Exports.
End F2KF2Sequence.
Import F2KF2Sequence.Exports.

Section F2KF2Sequence_lemma.
  Variable (t:f2kf2sequenceMap).
  Let f2sequence := @f2sequence t.

  Lemma f2sequence_functor2_functor2 :
    forall (m:f2kleisliMap) A B C (f:A -> B -> C) x y,
      @f2sequence m _ (functor2 (functor2 f) x y) =
      functor2 (functor2 f) (f2sequence x) (f2sequence y).
  Proof. rewrite /f2sequence. by case : t => func [b sm s2m s3m []]. Qed.
End F2KF2Sequence_lemma.

Definition eq_f2kf2sequenceMap
           (t:Type -> Type) (c d:F2KF2Sequence.class_of t) :=
  eq_f2kleisliMap c d /\ eq_kf2sequenceMap c d.

Definition f2comp_f2kleisli_class_of (t:f2kf2sequenceMap) (m:f2kleisliMap) :
  F2Kleisli.class_of (fun A => m (t A)).
Proof.
  apply : (@F2Kleisli.Class
             _ (f2comp_kleisli_class_of t m) (comp_functor2_mixin_of _ _)).
  - apply : F2Kleisli.Mixin =>/= A B C f x y.
    rewrite mu_f2comp /= -functor2D -functor2Dl functor2_mu functor_mu.
    rewrite -functor2D -functor2Dl -!functor2Dr. congr mu.
    apply : eq_functor2 => z w /=. rewrite f2sequence_functor2_functor2.
    rewrite -functor2Dr. exact : (eq_functor2 (functor2_mu _)).
Defined.
Definition f2comp_f2kleisliMap  (t:f2kf2sequenceMap) (m:f2kleisliMap) :=
  Eval hnf in @Kleisli.Pack (fun A => m (t A)) (f2comp_f2kleisli_class_of t m).

(*
Definition rcomp_hkleisliMap (m:kleisliMap) (t:f2KleisliMap) :=
  rcomp_kleisliMap (hkleisli m) t.
Definition rcomp_vkleisliMap (m:kleisliMap) (t:f2KleisliMap) :=
  rcomp_kleisliMap (vkleisli m) t.
*)
Section F2KF2Sequence_canonicals.
  (* id *)
  Definition id_f2kf2sequence_mixin_of :
    @F2KF2Sequence.mixin_of
      id_f2kleisliMap (FF2Sequence.f2sequence id_ff2sequence_mixin_of).
  Proof. exact : F2KF2Sequence.Mixin. Defined.
  Definition id_f2kf2sequence_class_of : F2KF2Sequence.class_of id.
  Proof.
    apply : F2KF2Sequence.Class id_f2kf2sequence_mixin_of.
    - exact : id_pf2sequence_mixin_of.
    - exact : id_kf2sequence_mixin_of.
  Defined.
  Definition id_f2kf2sequenceMap : f2kf2sequenceMap :=
    Eval hnf in @F2KF2Sequence.Pack id id_f2kf2sequence_class_of.
(*
  (* option *)
  Definition option_f2kf2sequence_mixin_of :
    @F2KF2Sequence.mixin_of
      option_f2kleisliMap (FF2Sequence.f2sequence option_ff2sequence_mixin_of).
  Proof.
    apply : F2KF2Sequence.Mixin => m A B C f [x|][y|]//=.
    - by rewrite -functor2Dr -functor2Dl -functor2D.
    - rewrite functor2_etar.

    - by rewrite functor_eta.
  Defined.
  Definition option_kf2sequence_class_of : KF2Sequence.class_of option.
  Proof.
    apply : KF2Sequence.Class option_kf2sequence_mixin_of.
    exact : option_pf2sequence_mixin_of.
  Defined.
  Definition option_kf2sequenceMap : kf2sequenceMap :=
    Eval hnf in @KF2Sequence.Pack option option_kf2sequence_class_of.
*)
End F2KF2Sequence_canonicals.

(* ********************* *)

Module KleisliMorphism.
  Record mixin_of (pre pos:kleisliMap) (t:forall A, pre A -> pos A) :=
    Mixin {
        _: forall A x, t A (mu x) = mu (functor (t _) (t _ x))
      }.
  Section ClassDef.
    Record class_of (pre pos:kleisliMap) (t:forall A, pre A -> pos A) :=
      Class {
          base : PFunctorMorphism.class_of t;
          mixin : mixin_of t
        }.
    Structure map := Pack {pre; pos; apply; _: @class_of pre pos apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ _ _ c := cF return class_of (@apply cF) in c.
    Definition pureMorphism := PureMorphism.Pack (base class).
    Definition functorMorphism := FunctorMorphism.Pack (base class).
    Definition pfunctorMorphism := PFunctorMorphism.Pack (base class).
  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> PFunctorMorphism.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion apply : map >-> Funclass.
    Coercion pureMorphism : map >-> PureMorphism.map.
    Canonical pureMorphism.
    Coercion functorMorphism : map >-> FunctorMorphism.map.
    Canonical functorMorphism.
    Coercion pfunctorMorphism : map >-> PFunctorMorphism.map.
    Canonical pfunctorMorphism.
    Notation kleisliMorphism := map.
  End Exports.
End KleisliMorphism.
Import KleisliMorphism.Exports.

Section KleisliMorphism_lemma.
  Variable (m:kleisliMorphism).

  Definition morph_mu : forall A x,
    m A (mu x) = mu (functor (m _) (m _ x)) :=
    let: (KleisliMorphism.Mixin H)
       := (KleisliMorphism.mixin (KleisliMorphism.class m)) in H.
End KleisliMorphism_lemma.

Section KleisliMorphism_canonicals.
  (* id *)
  Definition id_kleisliMorphism_mixin_of (m:kleisliMap) :
    @KleisliMorphism.mixin_of m _ (fun => id).
  Proof.
    apply : KleisliMorphism.Mixin => A x. by rewrite functor_id.
  Defined.
  Definition id_kleisliMorphism_class_of (m:kleisliMap) :
    @KleisliMorphism.class_of m _ (fun => id).
  Proof.
    apply : KleisliMorphism.Class.
    - exact : id_pfunctorMorphism_class_of.
    - exact : id_kleisliMorphism_mixin_of.
  Defined.
  Definition id_kleisliMorphism (m:kleisliMap) : kleisliMorphism :=
    Eval hnf in
      @KleisliMorphism.Pack
        _ _ (fun => id) (id_kleisliMorphism_class_of m).
(*
  (* eta *)
  Definition eta_kleisliMorphism_mixin_of (m n:kleisliMap):
    @KleisliMorphism.mixin_of
      n (comp_applicativeMap _ _) (fun _ => @eta m _).
  Proof.
    apply : ApplicativeTransformation.Mixin => A B f x.
      by rewrite applicative_comp functor2_eta functor_eta.
  Defined.
  Definition eta_applicativeTransformation_class_of (m n:applicativeMap) :
    @ApplicativeTransformation.class_of
      n (comp_applicativeMap _ _) (fun _ => @eta m _).
  Proof.
    apply : ApplicativeTransformation.Class.
    - exact : eta_pureTransformation_class_of.
    - exact : eta_applicativeTransformation_mixin_of.
  Defined.
  Definition eta_applicativeTransformation (m n:applicativeMap):
    applicativeTransformation :=
    Eval hnf in @ApplicativeTransformation.Pack
                  _ (comp_applicativeMap _ _) (fun _ => @eta m _)
                  (eta_applicativeTransformation_class_of m n).

  (* functor *)
  Definition functor_applicativeTransformation_mixin_of
             (m:applicativeMap) (t:applicativeTransformation) :
    @ApplicativeTransformation.mixin_of
      (comp_applicativeMap m _) (comp_applicativeMap _ _)
      (fun _ => functor (t _)).
  Proof.
    apply : ApplicativeTransformation.Mixin => A B f x.
    - rewrite !applicative_comp /functor2 -!applicative_etal -!applicativeA.
      rewrite !applicative_eta_eta /= applicative_etar !applicative_etal.
      rewrite -!functorD. apply : eq_functor2 => y z /=.
      exact : tf_applicative.
  Defined.
  Definition functor_applicativeTransformation_class_of
             (m:applicativeMap) (t:applicativeTransformation) :
    @ApplicativeTransformation.class_of
      (comp_applicativeMap m _) (comp_applicativeMap _ _)
      (fun _ => functor (t _)).
  Proof.
    apply : ApplicativeTransformation.Class.
    - exact : functor_pureTransformation_class_of.
    - exact : functor_applicativeTransformation_mixin_of.
  Defined.
  Definition functor_applicativeTransformation
             (m:applicativeMap) (t:applicativeTransformation) :
    applicativeTransformation :=
    Eval hnf in @ApplicativeTransformation.Pack
                  (comp_applicativeMap m _) (comp_applicativeMap _ _)
                  (fun _ => functor (t _))
                  (functor_applicativeTransformation_class_of m t).

  (* mu *)
  Definition mu_applicativeTransformation_mixin_of (m:akleisliMap) :
    @ApplicativeTransformation.mixin_of (comp_applicativeMap _ _) _ (@mu m).
  Proof.
    apply : ApplicativeTransformation.Mixin => A B f x.
    - rewrite applicative_comp !applicative_def functor2_mu /functor2. congr mu.
      congr applicative. apply : eq_functor => y. by rewrite functor_id.
  Defined.
  Definition mu_applicativeTransformation_class_of (m:akleisliMap) :
    @ApplicativeTransformation.class_of (comp_applicativeMap _ _) _ (@mu m).
  Proof.
    apply : ApplicativeTransformation.Class.
    - exact : mu_pureTransformation_class_of.
    - exact : mu_applicativeTransformation_mixin_of.
  Defined.
  Definition mu_applicativeTransformation (m:akleisliMap) :
    pfunctorTransformation :=
    Eval hnf in
      @PFunctorTransformation.Pack
        (comp_pfunctorMap _ _) _ (@mu m) (mu_applicativeTransformation_class_of m).
*)
End KleisliMorphism_canonicals.

(* ********************* *)

Module KleisliTransformer.
  Definition KLift (t:(Type -> Type) -> Type -> Type) :=
    forall (m:kleisliMap) A, m A -> t m A.

  Record class_of (t:(Type -> Type) -> Type -> Type) :=
    Class {
        kclass:forall m:kleisliMap, Kleisli.class_of (t m);
        klift:KLift t;
        _:forall (m:kleisliMap) A x,
            klift (@eta m A x) = @eta (Kleisli.Pack (kclass _)) _ x;
        _:forall (m:kleisliMap) A B f x,
            klift (@functor m A B f x) =
            @functor (Kleisli.Pack (kclass _)) _ _ f (klift x);
        _:forall (m:kleisliMap) A x,
            klift (@mu m A x) =
            @mu (Kleisli.Pack (kclass _)) _ (klift (functor (@klift _ _) x))
      }.

  Section ClassDef.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition kleisli_class_of := kclass class.
    Definition kleisliMap (m:kleisliMap) := Kleisli.Pack (kleisli_class_of m).
  End ClassDef.

  Module Exports.
    Coercion apply : map >-> Funclass.
    Notation kleisliTransformer := map.
    Definition klift T := klift (class T).
  End Exports.
End KleisliTransformer.
Import KleisliTransformer.Exports.

Section KleisliTransformer_lemma.
  Variable (t:kleisliTransformer).
  Let klift := klift t.

  Definition transformedKleisli_class_of (m:kleisliMap) :
    Kleisli.class_of (t m) :=
    let: KleisliTransformer.Pack
           _ (KleisliTransformer.Class k _ _ _ _) := t in k m.

  Definition transformedKleisliMap (m:kleisliMap) : kleisliMap :=
    Eval hnf in
      @Kleisli.Pack (t m) (transformedKleisli_class_of m).

  Lemma klift_eta (m:kleisliMap) A x:
    klift (@eta m A x) = @eta (transformedKleisliMap _) _ x.
  Proof.
    rewrite /klift /transformedKleisliMap /transformedKleisli_class_of.
      by case : t => T [].
  Qed.

  Lemma klift_functor (m:kleisliMap) A B f x:
    klift (@functor m A B f x) =
    @functor (transformedKleisliMap _) _ _ f (klift x).
  Proof.
    rewrite /klift /transformedKleisliMap /transformedKleisli_class_of.
      by case : t => T [].
  Qed.

  Lemma klift_mu (m:kleisliMap) A x:
    klift (@mu m A x) =
    @mu (transformedKleisliMap _) _ (klift (functor (@klift _ _) x)).
  Proof.
    rewrite /klift /transformedKleisliMap /transformedKleisli_class_of.
      by case : t => T [].
  Qed.
End KleisliTransformer_lemma.

Definition eq_kleisliTransformer (t:(Type -> Type) -> Type -> Type)
           (c d:KleisliTransformer.class_of t) :=
  forall m, eq_kleisliMap
              (@transformedKleisli_class_of
                 (KleisliTransformer.Pack c) m)
              (@transformedKleisli_class_of
                 (KleisliTransformer.Pack d) m).

Section KleisliTransformer_canonicals.

  Definition kleisliTransformer_comp_kleisli_class_of
             (t s:kleisliTransformer) (m:kleisliMap):
    Kleisli.class_of (t (s m)) :=
    let: KleisliTransformer.Pack
           _ (KleisliTransformer.Class k _ _ _ _) := t in
    (k (transformedKleisliMap s m)).

  Definition kleisliTransformer_comp_class_of (t s:kleisliTransformer) :
    KleisliTransformer.class_of (fun m => t (s m)).
  Proof.
    apply : (@KleisliTransformer.Class
               _ (kleisliTransformer_comp_kleisli_class_of t s)
               (fun _ _ x =>
                  @klift _ (transformedKleisliMap _ _) _ (klift _ x)))
    =>[m A x|m A B f x|m A x].
    - by rewrite !klift_eta.
    - by rewrite !klift_functor.
    - by rewrite !klift_mu !(@klift_functor s) -functorD.
  Defined.

  Definition kleisliTransformer_comp (t s:kleisliTransformer) :
    kleisliTransformer :=
  Eval hnf in
      @KleisliTransformer.Pack (fun m => t (s m))
                               (kleisliTransformer_comp_class_of t s).

  Definition pfsequence_transformer_class_of (m:kpfsequenceMap):
    KleisliTransformer.class_of (fun n A => n (m A)).
  Proof.
    apply : (@KleisliTransformer.Class _ (pfcomp_kleisli_class_of m)
                                       (fun _ _ => functor (@eta _ _)))
    =>[n A x|n A B f x|n A x].
    - exact : functor_eta.
    - rewrite functor_comp /= -!functorD. apply : eq_functor => y /=.
        by rewrite functor_eta.
    - rewrite mu_pfcomp /= !functor_mu -!functorD. congr mu.
      apply : eq_functor => y /=. rewrite pfsequence_eta -!functorD.
      apply : eq_functor => z /=. by rewrite mu_eta.
  Qed.

  Definition pfsequence_transformer (m:kpfsequenceMap) :
    kleisliTransformer :=
    Eval hnf in
      @KleisliTransformer.Pack (fun n A => n (m A))
                               (pfsequence_transformer_class_of m).

  Definition id_pftransformer : kleisliTransformer :=
    pfsequence_transformer id_kpfsequenceMap.
  Definition option_pftransformer : kleisliTransformer :=
    pfsequence_transformer option_kpfsequenceMap.
  Definition sumt_comp_pftransformer R t : kleisliTransformer :=
    pfsequence_transformer (sumt_kpfsequenceMap R t).
  Definition mult_comp_pftransformer R (idx:R) (op:Monoid.law idx) t:
    kleisliTransformer := pfsequence_transformer (mult_kpfsequenceMap op t).

  Definition sumt_transformer_class_of R:
    KleisliTransformer.class_of (sumt R).
  Proof.
    apply : (@KleisliTransformer.Class _ (sumt_kleisli_class_of R)
                                       (fun _ _ => functor inr))
    =>[m A x|m A B f x|m A x].
    - by rewrite functor_eta.
    - rewrite functor_sumt -!functorD. exact : (@eq_functor m).
    - by rewrite mu_sumt functor_mu -!functorD.
  Defined.
  Definition sumt_transformer R : kleisliTransformer :=
    Eval hnf in
      @KleisliTransformer.Pack (sumt R) (sumt_transformer_class_of R).

  Definition mult_transformer_class_of R (idx:R) (op:Monoid.law idx):
    KleisliTransformer.class_of (mult op).
  Proof.
    apply : (@KleisliTransformer.Class _ (mult_kleisli_class_of op)
                                       (fun _ _ => functor (pair idx)))
    =>[m A x|m A B f x|m A x].
    - exact : functor_eta.
    - rewrite functor_mult -!functorD. exact : (@eq_functor m).
    - rewrite mu_mult functor_mu -!functorD. congr mu.
      apply : eq_functor => y /=. rewrite -functorD. apply : eq_functor => z /=.
        by rewrite Monoid.mul1m.
  Defined.
  Definition mult_transformer R  (idx:R) (op:Monoid.law idx) :
    kleisliTransformer :=
    Eval hnf in
      @KleisliTransformer.Pack (mult op) (mult_transformer_class_of op).
End KleisliTransformer_canonicals.

(* ********************* *)

Module F2KleisliTransformer.
  Definition F2KLift (t:(Type -> Type) -> Type -> Type) :=
    forall (m:f2kleisliMap) A, m A -> t m A.

  Record class_of (t:(Type -> Type) -> Type -> Type) :=
    Class {
        f2kclass:forall m:f2kleisliMap, F2Kleisli.class_of (t m);
        f2klift:F2KLift t;
        _:forall (m:f2kleisliMap) A x,
            f2klift (@eta m A x) = @eta (F2Kleisli.Pack (f2kclass _)) _ x;
        _:forall (m:f2kleisliMap) A B C f x y,
            f2klift (@functor2 m A B C f x y) =
            @functor2 (F2Kleisli.Pack (f2kclass _))
                      _ _ _ f (f2klift x) (f2klift y);
        _:forall (m:f2kleisliMap) A x,
            f2klift (@mu m A x) =
            @mu (F2Kleisli.Pack (f2kclass _))
                _ (f2klift (functor (@f2klift _ _) x))
      }.

  Section ClassDef.
    Structure map := Pack {apply; _: class_of apply}.
    Variable (cF : map).
    Definition class :=
      let: Pack _ c := cF return class_of (apply cF) in c.
    Definition f2kleisli_class_of := f2kclass class.
    Definition f2kleisliMap (m:f2kleisliMap) :=
      F2Kleisli.Pack (f2kleisli_class_of m).
  End ClassDef.

  Module Exports.
    Coercion apply : map >-> Funclass.
    Notation f2kleisliTransformer := map.
    Definition f2klift T := f2klift (class T).
  End Exports.
End F2KleisliTransformer.
Import F2KleisliTransformer.Exports.

Section F2KleisliTransformer_lemma.
  Variable (t:f2kleisliTransformer).
  Let f2klift := f2klift t.

  Definition transformedF2Kleisli_class_of (m:f2kleisliMap) :
    F2Kleisli.class_of (t m) :=
    let: F2KleisliTransformer.Pack
           _ (F2KleisliTransformer.Class k _ _ _ _) := t in k m.

  Definition transformedF2KleisliMap (m:f2kleisliMap) : f2kleisliMap :=
    Eval hnf in
      @F2Kleisli.Pack (t m) (transformedF2Kleisli_class_of m).

  Lemma f2klift_eta (m:f2kleisliMap) A x:
    f2klift (@eta m A x) = @eta (transformedF2KleisliMap _) _ x.
  Proof.
    rewrite /f2klift /transformedF2KleisliMap /transformedF2Kleisli_class_of.
      by case : t => T [].
  Qed.

  Lemma f2klift_functor2 (m:f2kleisliMap) A B C f x y:
    f2klift (@functor2 m A B C f x y) =
    @functor2 (transformedF2KleisliMap _) _ _ _ f (f2klift x) (f2klift y).
  Proof.
    rewrite /f2klift /transformedF2KleisliMap /transformedF2Kleisli_class_of.
      by case : t => T [].
  Qed.

  Lemma f2klift_functor (m:f2kleisliMap) A B f x:
    f2klift (@functor m A B f x) =
    @functor (transformedF2KleisliMap _) _ _ f (f2klift x).
  Proof.
    by rewrite !functor_def f2klift_functor2 f2klift_eta.
  Qed.

  Lemma f2klift_mu (m:f2kleisliMap) A x:
    f2klift (@mu m A x) =
    @mu (transformedF2KleisliMap _) _ (f2klift (functor (@f2klift _ _) x)).
  Proof.
    rewrite /f2klift /transformedF2KleisliMap /transformedF2Kleisli_class_of.
      by case : t => T [].
  Qed.
End F2KleisliTransformer_lemma.

Definition eq_f2kleisliTransformer (t:(Type -> Type) -> Type -> Type)
           (c d:F2KleisliTransformer.class_of t) :=
  forall m, eq_f2kleisliMap
              (@transformedF2Kleisli_class_of
                 (F2KleisliTransformer.Pack c) m)
              (@transformedF2Kleisli_class_of
                 (F2KleisliTransformer.Pack d) m).

Section F2KleisliTransformer_canonicals.

  Definition f2kleisliTransformer_comp_f2kleisli_class_of
             (t s:f2kleisliTransformer) (m:f2kleisliMap):
    F2Kleisli.class_of (t (s m)) :=
    let: F2KleisliTransformer.Pack
           _ (F2KleisliTransformer.Class k _ _ _ _) := t in
    (k (transformedF2KleisliMap s m)).

  Definition f2kleisliTransformer_comp_class_of (t s:f2kleisliTransformer) :
    F2KleisliTransformer.class_of (fun m => t (s m)).
  Proof.
    apply : (@F2KleisliTransformer.Class
               _ (f2kleisliTransformer_comp_f2kleisli_class_of t s)
               (fun _ _ x =>
                  @f2klift _ (transformedF2KleisliMap _ _) _ (f2klift _ x)))
    =>[m A x|m A B C f x y|m A x].
    - by rewrite !f2klift_eta.
    - by rewrite !f2klift_functor2.
    - by rewrite !f2klift_mu !(@f2klift_functor s) -functorD.
  Defined.

  Definition f2kleisliTransformer_comp (t s:f2kleisliTransformer) :
    f2kleisliTransformer :=
  Eval hnf in
      @F2KleisliTransformer.Pack (fun m => t (s m))
                               (f2kleisliTransformer_comp_class_of t s).

  Definition f2sequence_transformer_class_of (m:f2kf2sequenceMap):
    F2KleisliTransformer.class_of (fun n A => n (m A)).
  Proof.
    apply : (@F2KleisliTransformer.Class _ (f2comp_f2kleisli_class_of m)
                                       (fun _ _ => functor (@eta _ _)))
    =>[n A x|n A B C f x y|n A x].
    - exact : functor_eta.
    - rewrite functor2_comp -functor2Dr -functor2D -functor2Dl.
      apply : eq_functor2 => z w /=. by rewrite functor2_etal functor_eta.
    - rewrite mu_f2comp /= !functor_mu -!functorD. congr mu.
      apply : eq_functor => y /=. rewrite f2sequence_eta -!functorD.
      apply : eq_functor => z /=. by rewrite mu_eta.
  Qed.
  Definition f2sequence_transformer (m:f2kf2sequenceMap) :
    f2kleisliTransformer :=
    Eval hnf in
      @F2KleisliTransformer.Pack (fun n A => n (m A))
                               (f2sequence_transformer_class_of m).

  Definition id_f2transformer : f2kleisliTransformer :=
    f2sequence_transformer id_f2kf2sequenceMap.

End F2KleisliTransformer_canonicals.
