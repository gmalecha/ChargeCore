Require Import ChargeCore.Logics.ILogic.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics. (*  Omega.  *)

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
Set Universe Polymorphism.
Set Printing Universes.

Section ILogicEmbed.
  Polymorphic Universe A B T.
  Context {A : Type@{A}} `{ILOpsA: ILogic@{A T} A}.
  Context {B : Type@{B}} `{ILOpsB: ILogic@{B T} B}.

  Class Embed : Type := mkEmbed { lembed : A -> B }.

  Class EmbedOk {EmbOp: Embed} : Type := mkEmbedOk
  { lembed_sound : forall p q : A, p |-- q -> lembed p |-- lembed q;
    lembedlforall : forall (T : Type@{T}) f,
        Forall x : T, lembed (f x) -|- lembed (Forall x : T, f x);
    lembedlexists : forall (T : Type@{T}) f,
        Exists x : T, lembed (f x) -|- lembed (Exists x : T, f x);
    lembedImpl a b : (lembed a) -->> (lembed b) -|- lembed (a -->> b)
  }.
End ILogicEmbed.

Implicit Arguments Embed [].
Implicit Arguments EmbedOk [[ILOpsA] [ILOpsB] [EmbOp]].

(** TODO(gmalecha): Are these useful? **)
Section ILogicEmbedOps.
  Context {A B} `{HAB: Embed A B} {ILA: ILogic A} {ILB: ILogic B}.

  Definition lembedand (a : A) (b : B) := lembed a //\\ b.
  Definition lembedimpl (a : A) (b : B) := lembed a -->> b.

End ILogicEmbedOps.


Section ILEmbedId.
  Context {A : Type} `{ILA : ILogicOk A}.

  Instance Embed_Id : Embed A A := { lembed := id }.
  Global Instance EmbedOk_Id : EmbedOk A A.
  Proof. split; firstorder. Qed.

End ILEmbedId.


(* TODO(gmalecha): This is from EmbedId *)
(* Section EmbedPropProp. *)
(*   Instance EmbedOpPropProp : Embed Prop Prop := { embed := fun P => P }. *)
(*   Instance EmbedPropProp : EmbedOk Prop Prop. *)
(*   Proof. *)
(*     split; firstorder. *)
(*   Qed. *)
(* End EmbedPropProp. *)

Section ILogicEmbedCompose.
  Polymorphic Universes A B C T.
  Context {A : Type@{A}} {B : Type@{B}} {HAB: Embed@{A B T} A B} {ILA: ILogic@{A T} A} {ILB: ILogic@{B T} B} {HABO: EmbedOk@{A B T} A B}.
  Context {C : Type@{C}} {HC: ILogic@{C T} C} {HE: Embed@{B C T} B C} {HBC : EmbedOk@{B C T} B C}
          {ILC: ILogicOk C}.

  Instance embedOpCompose : Embed A C :=
  { lembed := fun x => lembed (lembed x) }.


  Instance embedCompose : EmbedOk A C.
  Proof.
    constructor.
    { intros. simpl. eapply lembed_sound. eapply lembed_sound. eassumption. }
    { simpl; split;
      erewrite lembedlforall; eapply lembed_sound; eapply lembedlforall. }
    { simpl; split;
      erewrite lembedlexists; eapply lembed_sound; eapply lembedlexists. }
    { simpl; split;
      erewrite lembedImpl; eapply lembed_sound; eapply lembedImpl. }
  Qed.

End ILogicEmbedCompose.

Infix "/\\" := lembedand (at level 75, right associativity).
Infix "->>" := lembedimpl (at level 77, right associativity).

Section ILogicEmbedFacts.
  Polymorphic Universes A B T.
  Context {A : Type@{A}} {B : Type@{B}}
          {ILA: ILogic@{A T} A} {ILAO: ILogicOk@{A T} A}
          {ILB: ILogic@{B T} B} {ILBO: ILogicOk@{B T} B}
          {HAB: Embed@{A B T} A B}
          {HABO: EmbedOk@{A B T} A B}.

  Global Instance lembed_lentails_m :
    Proper (lentails ==> lentails) lembed.
  Proof.
    intros a b Hab; apply lembed_sound; assumption.
  Qed.

  Global Instance lembed_lequiv_m :
    Proper (lequiv ==> lequiv) lembed.
  Proof.
    intros a b Hab; split; destruct Hab; apply lembed_sound; assumption.
  Qed.

  Global Instance lembedimpl_lentails_m:
    Proper (lentails --> lentails ++> lentails) lembedimpl.
  Proof.
    intros P P' HP Q Q' HQ; red in HP.
    unfold lembedimpl. rewrite <- HP, HQ. reflexivity.
  Qed.

  Global Instance lembedimpl_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lembedimpl.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply lembedimpl_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance lembedand_lentails_m:
    Proper (lentails ==> lentails ==> lentails) lembedand.
  Proof.
    intros P P' HP Q Q' HQ.
    unfold lembedand. rewrite HP, HQ. reflexivity.
  Qed.

  Global Instance lembedand_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lembedand.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply lembedand_lentails_m; (apply HP || apply HQ).
  Qed.

  Lemma lembedland a b : lembed a //\\ lembed b -|- lembed (a //\\ b).
  Proof.
    do 2 rewrite land_is_forall; rewrite <- lembedlforall; split;
    apply lforallR; intro x; apply lforallL with x;
    destruct x; reflexivity.
  Qed.

  Lemma lembedlor a b : lembed a \\// lembed b -|- lembed (a \\// b).
  Proof.
    do 2 rewrite lor_is_exists; erewrite <- lembedlexists; split;
    apply lexistsL; intro x; apply lexistsR with x;
    destruct x; reflexivity.
  Qed.

  Lemma lembedlfalse : lembed lfalse -|- lfalse.
  Proof.
    rewrite lfalse_is_exists; erewrite <- lembedlexists; split;
    [apply lexistsL; intro x; destruct x | apply lfalseL].
  Qed.

  Lemma lembedltrue : lembed ltrue -|- ltrue.
  Proof.
    rewrite ltrue_is_forall; rewrite <- lembedlforall; split;
    [apply ltrueR | apply lforallR; intro x; destruct x].
  Qed.

  Lemma lembedlandC (P R : B) (Q : A) : P //\\ Q /\\ R -|- Q /\\ P //\\ R.
  Proof.
    unfold lembedand; rewrite <- landA, (landC P), landA; reflexivity.
  Qed.

  Lemma lembedlimplC (P R : B) (Q : A) : P -->> Q ->> R -|- Q ->> P -->> R.
  Proof.
    unfold lembedimpl. do 2 rewrite limplAdj2.
    rewrite landC. reflexivity.
  Qed.

  Lemma limpllandC (P Q R : B) : P //\\ (Q -->> R) |-- Q -->> P //\\ R.
  Proof.
    apply limplAdj; rewrite landA; apply landR.
    + apply landL1. reflexivity.
    + apply landL2. apply limplL; [reflexivity | apply landL1; reflexivity].
  Qed.

  Lemma lembed_existsL (P : A) : Exists x : |-- P, ltrue |-- lembed P.
  Proof.
    apply lexistsL; intro H.
    rewrite <- H. rewrite lembedltrue. apply ltrueR.
  Qed.

End ILogicEmbedFacts.

Section EmbedProp.
  Context {A : Type} `{HIL: ILogicOk A} {HPropOp: Embed Prop A} {HProp: EmbedOk Prop A}.

  Lemma lembedPropExistsR (p : Prop) : lembed p |-- Exists x : p, ltrue.
  Proof.
    assert (p |-- Exists x : p, (|-- ltrue)). {
      intros Hp. exists Hp. apply ltrueR.
    } etransitivity.
    rewrite H. reflexivity.
    rewrite <- lembedlexists. apply lexistsL. intros Hp.
    apply lexistsR with Hp. apply ltrueR.
  Qed.

  Lemma lembedPropExistsL (p : Prop) (P : A) : Exists x : p, P |-- lembed p.
  Proof.
    assert (Exists x : p, ltrue |-- p). {
      intros HP. destruct HP as [HP _]. apply HP.
    }
    etransitivity; [|rewrite <- H]; [reflexivity|].
    rewrite <- lembedlexists. apply lexistsL; intro Hp.
    apply lexistsR with Hp. rewrite lembedltrue. apply ltrueR.
  Qed.

  Lemma lembedPropExists' (p : Prop) : Exists x : p, ltrue -|- lembed p.
  Proof.
    split; [apply lembedPropExistsL | apply lembedPropExistsR].
  Qed.

  Lemma lembedPropL (p : Prop) C (H: p -> |-- C) :
    lembed p |-- C.
  Proof.
    rewrite lembedPropExistsR.
    apply lexistsL; intro Hp.
    apply H; apply Hp.
  Qed.

  Lemma lembedPropR (p : Prop) (P : A) (H : p) : P |-- lembed p.
  Proof.
    assert (ltrue |-- p) by (intros _; assumption).
    rewrite <- H0, lembedltrue; apply ltrueR.
  Qed.

  Lemma lpropandL (p: Prop) Q C (H: p -> Q |-- C) :
    p /\\ Q |-- C.
  Proof.
    unfold lembedand.
    apply landAdj.
    apply lembedPropL.
    intros Hp.
    apply limplAdj.
    apply landL2.
    apply H. assumption.
  Qed.

  Lemma lpropandR C (p: Prop) Q (Hp: p) (HQ: C |-- Q) :
    C |-- p /\\ Q.
  Proof.
    unfold lembedand.
    apply landR; [|assumption].
    rewrite <- lembedPropR. apply ltrueR. assumption.
  Qed.

  Lemma lpropimplL (p: Prop) (Q C: A) (Hp: p) (HQ: Q |-- C) :
    p ->> Q |-- C.
  Proof.
    unfold lembedimpl.
    rewrite <- lembedPropR, limplTrue; assumption.
  Qed.

  Lemma lpropimplR C (p: Prop) Q (H: p -> C |-- Q) :
    C |-- p ->> Q.
  Proof.
    unfold lembedimpl.
    apply limplAdj. rewrite landC. apply lpropandL. assumption.
  Qed.

  (* Derivable but useful *)
  Lemma lpropandTrue P : True /\\ P -|- P.
  Proof.
    split.
    + apply lpropandL; intros _; reflexivity.
    + apply landR.
      * replace True with (@ltrue Prop _) by reflexivity.
        rewrite lembedltrue. apply ltrueR.
      * reflexivity.
  Qed.

  Lemma lpropandFalse P : False /\\ P -|- lfalse.
  Proof.
    split.
    + apply lpropandL; intros H; destruct H.
    + apply lfalseL.
  Qed.

End EmbedProp.

Section EmbedProp'.
  Context {A : Type} `{HILA: ILogicOk A} {HPropOpA: Embed Prop A} {HPropA: EmbedOk Prop A}.
  Context {B : Type} `{HILB: ILogicOk B} {HPropOpB: Embed Prop B} {HPropB: EmbedOk Prop B}.
  Context {HEmbOp : Embed B A} {Hemb: EmbedOk B A}.

  Lemma lpropandAL (p : B) (q : A) (P : Prop) : P /\\ p /\\ q |-- (P /\\ p) /\\ q.
  Proof.
    apply lpropandL; intros HP; apply landR.
    + apply landL1; apply lembed_sound; apply landR.
      * apply lembedPropR. assumption.
      * reflexivity.
    + apply landL2; reflexivity.
  Qed.

  Lemma lpropandAC (p : B) (q : A) (P : Prop) : p /\\ P /\\ q -|- P /\\ p /\\ q.
  Proof.
    unfold lembedand.
    do 2 rewrite <- landA; rewrite (landC (lembed p)); reflexivity.
  Qed.

  Lemma lpropandAR (p : B) (q : A) (P : Prop)
    : (P /\\ p) /\\ q |-- P /\\ p /\\ q.
  Proof.
    apply landR.
    + apply landL1.
      unfold lembedand; rewrite <- lembedland; apply landL1.
      rewrite lembedPropExistsR, <- lembedlexists.
      apply lexistsL; intro Hp.
      apply lembedPropR; apply Hp.
    + unfold lembedand; rewrite <- lembedland; apply landR.
      * apply landL1; apply landL2. reflexivity.
      * apply landL2; reflexivity.
  Qed.

  Lemma lpropimplAL (p : B) (q : A) (P : Prop)
    : (P ->> p) /\\ q |-- P ->> (p /\\ q).
  Proof.
    unfold lembedimpl, lembedand. apply limplAdj. rewrite landA.
    rewrite <- lembedImpl. apply limplL. apply landL2.
    rewrite lembedPropExistsR. apply lexistsL; intro Hp.
    rewrite <- (lembedPropR ltrue); [apply lembedltrue | apply Hp].
    apply landR; [apply landL1|apply landL2; apply landL1]; reflexivity.
  Qed.

  Lemma lpropimplAR (p : B) (q : A) (P : Prop)
    : p /\\ (P ->> q) |-- P ->> (p /\\ q).
  Proof.
    unfold lembedimpl, lembedand. rewrite landC. apply limplAdj. rewrite landA.
    apply limplL. apply landL2; reflexivity.
    apply landR; [apply landL2; apply landL1|apply landL1]; reflexivity.
  Qed.

  Lemma embedPropR2 (p : Prop) (P : A) (H : p) : P |-- lembed (lembed p).
  Proof.
    assert (ltrue |-- p) by (intros _; assumption).
    rewrite <- H0. do 2 rewrite lembedltrue. apply ltrueR.
  Qed.

  Lemma embedPropL2 (p : Prop) (C : A) (H: p -> |-- C) :
    lembed (lembed p) |-- C.
  Proof.
    rewrite lembedPropExistsR, <- lembedlexists.
    apply lexistsL; intro Hp. rewrite lembedltrue.
    apply H; apply Hp.
  Qed.

End EmbedProp'.


Section EmbedPropInj.
  Context {A : Type} `{ILA : ILogicOk A}.
  Context {EmbOp1 : Embed Prop A} {Emb1 : EmbedOk Prop A}.
  Context {EmbOp2 : Embed Prop A} {Emb2 : EmbedOk Prop A}.

  Lemma emb_prop_eq (P : Prop) : @lembed _ _ EmbOp1 P -|- @lembed _ _ EmbOp2 P.
  Proof.
    split; rewrite lembedPropExistsR; apply lexistsL; intro Hp;
    (rewrite <- (lembedPropR ltrue); [apply ltrueR | apply Hp]).
  Qed.

End EmbedPropInj.
