Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILEmbed.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
Set Printing Universes.
Set Universe Polymorphism.

Section BILogic.
  Context {A : Type}.
  Context {HILOp: ILogic A}.

  Class BILogic : Type := mkBILogic
  {
    lemp  : A;
    lsep  : A -> A -> A;
    lwand : A -> A -> A
  }.

  Class BILogicOk (Ops : BILogic) : Type := mkBILogicOk {
    lsepC1 P Q : lsep P Q |-- lsep Q P;
    lsepA1 P Q R : lsep (lsep P Q) R |-- lsep P (lsep Q R);
    wandSepSPAdj P Q R : lsep P Q |-- R <-> P |-- lwand Q R;
    bilsep P Q R : P |-- Q -> lsep P R |-- lsep Q R;
    lempR P : lsep P lemp -|- P
  }.

End BILogic.

Arguments BILogicOk _ {BILogic ILogic} : rename.

Notation "a '**' b"  := (lsep a b)
  (at level 58, right associativity).
Notation "a '-*' b"  := (lwand a b)
  (at level 60, right associativity).

Section CoreInferenceRules.

  Context {A} `{HBIL: BILogicOk A} {ILO : ILogicOk A}.

  Lemma lwandAdj P Q C (HSep: C ** P |-- Q) : C |-- P -* Q.
  Proof.
    apply wandSepSPAdj; assumption.
  Qed.

  Lemma lwandAdj' P Q C (HSep: P ** C |-- Q) : C |-- P -* Q.
  Proof.
    apply wandSepSPAdj. etransitivity; [apply lsepC1|]. assumption.
  Qed.

  Lemma lsepAdj P Q C (HWand: C |-- P -* Q) : C ** P |-- Q.
  Proof.
    apply wandSepSPAdj; assumption.
  Qed.

  Lemma lsepAdj' P Q C (HWand: C |-- P -* Q) : P ** C |-- Q.
  Proof.
    etransitivity; [apply lsepC1|]. apply wandSepSPAdj. assumption.
  Qed.

  Lemma lsepC (P Q : A) : P ** Q -|- Q ** P.
  Proof.
    split; apply lsepC1.
  Qed.

  Lemma lsepA2 (P Q R : A) : P ** (Q ** R) |-- (P ** Q) ** R.
  Proof.
    rewrite lsepC.
    etransitivity; [apply lsepA1|].
    rewrite lsepC.
    etransitivity; [apply lsepA1|].
    rewrite lsepC.
    reflexivity.
  Qed.

  Lemma lsepA (P Q R : A) : (P ** Q) ** R -|- P ** (Q ** R).
  Proof.
    split; [apply lsepA1 | apply lsepA2].
  Qed.

  Lemma lwandI (P Q R : A) (HQ : P ** Q |-- R) : (P |-- Q -* R).
  Proof.
    apply lwandAdj; assumption.
  Qed.

  Lemma lwandE (P Q R T : A) (HQR: Q |-- T -* R) (HP : P |-- Q ** T) : P |-- R.
  Proof.
    apply lsepAdj in HQR.
    rewrite <- HQR, HP. reflexivity.
  Qed.

  Lemma lempL P : lemp ** P -|- P.
  Proof.
    rewrite lsepC; apply lempR.
  Qed.

  Lemma bilexistsscL {T} (P : A) (Q : T -> A):
    Exists x : T, P ** Q x |-- P ** Exists x : T, Q x.
  Proof.
  	apply lexistsL; intro x.
    rewrite lsepC. etransitivity; [|rewrite <- lsepC; reflexivity].
    apply bilsep. eapply lexistsR; reflexivity.
  Qed.

  Lemma bilexistsscR {T} (P : A) (Q : T -> A) :
    P ** (Exists x : T, Q x) |-- Exists x : T, P ** Q x.
  Proof.
    rewrite lsepC; rewrite wandSepSPAdj.
    apply lexistsL; intro x; erewrite <- lwandAdj. reflexivity.
    eapply lexistsR; rewrite lsepC; reflexivity.
  Qed.

  Lemma bilexistssc {T} (P : A) (Q : T -> A) :
    Exists x : T, P ** Q x -|- P ** Exists x : T, Q x.
  Proof.
    split; [apply bilexistsscL | apply bilexistsscR].
  Qed.

  Lemma bilforallscR {T} (P : A) (Q : T -> A) :
    P ** (Forall x : T, Q x) |-- Forall x : T, P ** Q x.
  Proof.
    apply lforallR; intro x.
    rewrite lsepC; etransitivity; [|rewrite <- lsepC; reflexivity].
    apply bilsep. apply lforallL with x; reflexivity.
  Qed.

  Lemma bilandscDL (P Q R : A) : (P //\\ Q) ** R |-- (P ** R) //\\ (Q ** R).
  Proof.
  	apply landR.
  	+ apply wandSepSPAdj; apply landL1; apply wandSepSPAdj; reflexivity.
  	+ apply wandSepSPAdj; apply landL2; apply wandSepSPAdj; reflexivity.
  Qed.

  Lemma bilorscDL (P Q R : A) : (P \\// Q) ** R -|- (P ** R) \\// (Q ** R).
  Proof.
  	split.
  	+ apply wandSepSPAdj; apply lorL; apply wandSepSPAdj;
  	  [apply lorR1 | apply lorR2]; reflexivity.
  	+ apply lorL; apply bilsep; [apply lorR1 | apply lorR2]; reflexivity.
  Qed.

End CoreInferenceRules.

Section BILogicMorphisms.
  Context {A : Type} `{BIL: BILogicOk A} {ILO : ILogicOk A}.

  Global Instance lsep_lentails_m:
    Proper (lentails ++> lentails ++> lentails) lsep.
  Proof.
    intros P P' HP Q Q' HQ.
    etransitivity; [eapply bilsep; exact HP|].
    rewrite -> lsepC.
    etransitivity; [eapply bilsep; exact HQ|].
    rewrite -> lsepC. reflexivity.
  Qed.

  Global Instance lsep_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lsep.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply lsep_lentails_m; (apply HP || apply HQ).
  Qed.

  Global Instance lwand_lentails_m:
    Proper (lentails --> lentails ++> lentails) lwand.
  Proof.
    intros P P' HP Q Q' HQ. red in HP.
    apply lwandAdj. rewrite <- HQ, -> HP.
    apply lsepAdj. reflexivity.
  Qed.

  Global Instance lwand_lequiv_m:
    Proper (lequiv ==> lequiv ==> lequiv) lwand.
  Proof.
    intros P P' HP Q Q' HQ.
    split; apply lwand_lentails_m; (apply HP || apply HQ).
  Qed.

End BILogicMorphisms.

Section DerivedInferenceRules.

  Context {A : Type} `{BILogicOk A} {ILO: ILogicOk A}.

  Lemma lsep_falseR P : P ** lfalse -|- lfalse.
  Proof.
    rewrite lfalse_is_exists, <- bilexistssc.
    split; apply lexistsL; intro x; destruct x.
  Qed.

  Lemma lsep_falseL P : lfalse ** P -|- lfalse.
  Proof.
    rewrite -> lsepC; apply lsep_falseR.
  Qed.

  Lemma scME (P Q R S : A) (HPR: P |-- R) (HQS: Q |-- S) :
    P ** Q |-- R ** S.
  Proof.
    rewrite HPR, HQS; reflexivity.
  Qed.

  Lemma lwandL P Q CL CR (HP: CL |-- P) (HR: Q |-- CR) :
    (P -* Q) ** CL |-- CR.
  Proof.
    rewrite <-HR, <-HP. apply lsepAdj. reflexivity.
  Qed.


  Lemma siexistsE {T : Type} (P : T -> A) (Q : A) :
    (Exists x, P x) -* Q -|- Forall x, (P x -* Q).
  Proof.
    split.
	+ apply lforallR; intro x. apply wandSepSPAdj; eapply lwandL; [|reflexivity].
	  apply lexistsR with x. reflexivity.
	+ apply wandSepSPAdj. rewrite bilexistsscR. apply lexistsL; intro x.
	  rewrite lsepC, bilforallscR. apply lforallL with x. rewrite lsepC.
	  apply lwandL; reflexivity.
  Qed.

  Lemma septrue : forall p, p |-- p ** ltrue.
  Proof.
    intros. rewrite <- lempR at 1.
    rewrite lsepC. rewrite (lsepC p).
    apply bilsep. apply ltrueR.
  Qed.

  Lemma wand_curry : forall a b c, (a ** b) -* c -|- a -* (b -* c).
  Proof.
    intros; split.
    { eapply lwandAdj.
      eapply lwandAdj.
      rewrite lsepA.
      eapply lsepAdj.
      reflexivity. }
    { eapply lwandAdj.
      rewrite <- lsepA.
      eapply lsepAdj.
      eapply lsepAdj. reflexivity. }
  Qed.

End DerivedInferenceRules.