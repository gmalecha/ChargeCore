Require Import ChargeCore.Open.Stack.
Require Import ChargeCore.Open.Open.

Require Import FunctionalExtensionality.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Data.PList.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.
Set Universe Polymorphism.

Fixpoint zip {A} {B} (lst1 : plist A) (lst2 : plist B) : plist (A * B) :=
  match (lst1, lst2) with
    | (pnil, pnil) => pnil
    | (pcons x xs, pnil) => pnil
    | (pnil, pcons y ys) => pnil
    | (pcons x xs, pcons y ys) => pcons (x, y) (zip xs ys)
  end.

Section Subst.
  Context {A val : Type} {Heq : RelDec (@eq A)}.
  Context {R : ValNull val}.

  Definition subst := A -> (A -> val) -> val.

  Definition stack_subst (s: stack A val) (sub: subst) : stack A val :=
    fun x => sub x s.

  Definition apply_subst {B}
          (e : (A -> val) -> B) (sub : subst) : (A -> val) -> B :=
    fun s => e (stack_subst s sub).

  Definition substlist := plist (A * @expr A val).

  (* The identity substitution *)
  Definition subst0 : subst := fun x => var_expr x.

  (* Substitution of one variable *)
  Definition subst1 e x : subst :=
    fun x' => if x' ?[ eq ] x then e else var_expr x'.

  (* Truncating substitution of one variable *)
  Definition subst1_trunc e x : subst :=
    fun x' => if x' ?[ eq ] x then e else empty_open.

  (* Simultaneous substitution of a finite list of variables *)
  Fixpoint substl_aux (subs: substlist) : subst :=
    match subs with
      | pnil => subst0
      | pcons (x,e) subs' => fun x' => 
        if x' ?[ eq ] x then e else substl_aux subs' x'
    end.

(* Truncating simultaneous substitution of a finite list of variables *)
  Fixpoint substl_trunc_aux (subs: substlist) : subst :=
    match subs with
      | pnil => fun _ => empty_open
      | pcons (x,e) subs' => fun x' => 
        if x' ?[ eq ] x then e else substl_trunc_aux subs' x'
    end.

  Definition substl es v := substl_aux es v.
  Definition substl_trunc es v := substl_trunc_aux es v.

End Subst.

(* Binds tighter than function application *)
(* We have the e at precedence level one less than the precedence of the infix
   // operator to make parsing work. *)

Notation "g [{ e // x }]" := (apply_subst g (subst1 e x)) (at level 9, e at level 39,
  format "g [{ e // x }]") : open_scope.

Notation "g [{ e //! x }]" := (apply_subst g (subst1_trunc e x)) (at level 9, e at level 39,
  format "g [{ e //! x }]") : open_scope.

Notation " g '//' es " := (apply_subst g (substl es)) (at level 40) : open_scope.

Notation " g '//!' es " := (apply_subst g (substl_trunc es)) (at level 40) : open_scope.

Section Properties.
  Context {A val : Type} {Heq : RelDec (@eq A)} {HeqOk : RelDec_Correct Heq}.
  Context {R : ValNull val}.

  Lemma open_subst_stack {B} (m: @open A val B) (sub : subst) (s : @stack A val) :
    (apply_subst m sub) s = m (stack_subst s sub).
  Proof. reflexivity. Qed.

  Lemma subst0_id B (g: @open A val B) : (apply_subst g (@subst0 A val)) = g.
  Proof.
    apply functional_extensionality.
    intros s; simpl; reflexivity.
  Qed.

  Lemma subst1_stack (s: @stack A val) e x :
    stack_subst s (subst1 e x) = stack_add x (e s) s.
  Proof.
    apply functional_extensionality; intro x'; simpl.
    unfold stack_subst, subst1, stack_add.
    consider (x' ?[ eq ] x); reflexivity.
  Qed.

  Lemma substl_subst1 x e :
    substl (val := val) (pcons (x,e) pnil) = subst1 e x.
  Proof. 
    reflexivity.
  Qed.

  Lemma substl_subst1_trunc x e :
    substl_trunc (pcons (x,e) pnil) = subst1_trunc e x.
  Proof. 
    reflexivity.
  Qed.

  Local Open Scope open_scope.
  Lemma subst1_stack_add {B} (p : open B) (e : expr) (x : A) (v : val) (s : @stack A val) : 
    p[{e//x}] (stack_add x v s) = p[{e[{V_expr v//x}]//x}] s.
  Proof.
    unfold apply_subst, subst1; simpl.
    apply f_equal.
    unfold stack_subst.
    apply functional_extensionality.
    intros y.
    consider (y ?[ eq ] x); intros; subst.
    + f_equal. apply functional_extensionality; intro z; simpl.
      consider (z ?[ eq ] x); intros; subst.
      * rewrite stack_lookup_add; reflexivity.
      * rewrite stack_lookup_add2; [reflexivity| intuition congruence].
    + unfold var_expr.
      rewrite stack_lookup_add2; [reflexivity | intuition].
  Qed.
      
  Lemma stack_add_var (x : A) (s : @stack A val) (v : val) : (var_expr x) (stack_add x v s) = v.
  Proof.
    unfold var_expr. rewrite stack_lookup_add. reflexivity.
  Qed.
  
  Lemma subst1_val (v : val) (e : open val) (x : A) :
    (V_expr v)[{e//x}] = (V_expr v).
  Proof.
    reflexivity.
  Qed.

  Lemma subst_identity {B} (x : A) (s : @stack A val) (p : open B) :
    p[{(V_expr (s x))//x}] s = p s.
  Proof.
    unfold subst1, apply_subst.
    apply f_equal.
    unfold stack_subst; simpl.
    apply functional_extensionality.
    intros y; simpl.
    consider (y ?[ eq ] x); intro; subst; reflexivity.
  Qed.

  Lemma substl_trunc_notin x' xs es :
    ~ pIn x' xs ->
    substl_trunc (zip xs es) x' = @empty_open _ val _.
  Proof.
    intro HnotIn. revert es. induction xs as [|x]; intros.
    + simpl. destruct es; reflexivity.
    + destruct es as [|e]; [reflexivity|]. simpl. consider (x' ?[ eq ] x); intro.
      - subst. contradiction HnotIn. simpl. auto.
      - apply IHxs. auto with datatypes.
        simpl in HnotIn. firstorder congruence.
  Qed.

  Lemma subst1_trunc_singleton_stack {B} (p : open B) (s : @stack A val) x y :
    p[{(var_expr y) //! x}] s = p (stack_add x (s y) (stack_empty A val)).
  Proof.
    unfold apply_subst, subst1_trunc, stack_subst; simpl.
    apply f_equal.
    apply functional_extensionality.
    intro x'.
    consider (x' ?[ eq ] x); intros; subst.
    * rewrite stack_lookup_add.
      reflexivity.
    * rewrite stack_lookup_add2; [| auto].
      reflexivity.
  Qed.

End Properties.

Hint Rewrite @subst0_id : open.
Hint Rewrite @substl_subst1 : open.
Hint Rewrite @substl_trunc_notin using assumption : open.

Section MoreLemmas.
  Context {A val : Type} {Heq : RelDec (@eq A)} {HeqOk : RelDec_Correct Heq}.
  Context {R : ValNull val}.

  Open Scope open_scope.

  Lemma subst_singleton {B} : 
    forall x e (P : @open A val B), P[{e//x}] = P // (pcons (x, e) pnil).
  Proof.
    reflexivity.
  Qed.

  Lemma subst_open_expr_nil {B} :
    forall (e : @open A val B), (e // pnil) = e.
  Proof.
    reflexivity.
  Qed.

  Lemma subst_var_cons_eq : 
    forall (x:A) es (e : expr (val := val)), (var_expr x // (pcons (x, e) es)) = e.
  Proof.
    intros x es e.
    apply functional_extensionality; intros s; simpl.
    unfold var_expr, apply_subst, stack_subst. simpl.
    consider (x ?[ eq ] x); intuition congruence.
  Qed.

  Lemma subst_var_cons_ineq : forall (x:A) y es (e : expr (val := val))
    (Hneq: x <> y),
    (var_expr x // (pcons (y, e) es)) = (var_expr x // es).
  Proof.
    intros x y es e Hneq.
    apply functional_extensionality; intros s.
    unfold var_expr, apply_subst, stack_subst; simpl.
    consider (x ?[ eq ] y); congruence.
  Qed.

  Lemma val_expr_substs : forall (v : val) es,
    ((V_expr v) // es) = (V_expr v).
  Proof.
    reflexivity.
  Qed.

  Definition subst_substlist (es fs : @substlist A val) : substlist :=
    fmap_plist (fun x => (fst x, (snd x) // fs)) es.

  Lemma subst_combine {B} (e : @open A val B) (es fs : substlist) :
    (e // es // fs) = (e // (app _ (subst_substlist es fs) fs)).
  Proof.
    apply functional_extensionality; intros s.
    unfold apply_subst, stack_subst; simpl.
    f_equal. apply functional_extensionality. intros x.
    induction es; simpl.
    + reflexivity.
    + destruct t; simpl.
      consider (x ?[ eq ] a); intros; subst; simpl.
      * reflexivity.
      * apply IHes.
  Qed.


Close Scope open_scope.

End MoreLemmas.

Section SubstFresh.

  Context {A val : Type} {Heq : RelDec (@eq A)} {HeqOk : RelDec_Correct Heq}.
  Context {R : ValNull val}.
      
   Definition subst_fresh (vs: A -> val) (xs: plist A) : subst :=
      fun x' => if (anyb (rel_dec x')) xs then V_expr (vs x') else var_expr x'.

   Fixpoint subst_fresh_l (vs: A -> val) (xs: plist A) : plist (@expr A val) :=
      match xs with
      | pnil => pnil
      | pcons x xs' => pcons (V_expr (vs x)) (subst_fresh_l vs xs')
      end.

    (* TODO: switch the two alt. definitions. *)
    Lemma subst_fresh_alt (vs: A -> val) (xs: plist A) :
      subst_fresh vs xs = substl (zip xs (subst_fresh_l vs xs)).
    Proof.
      induction xs as [|x]; [reflexivity|].
      apply functional_extensionality.
      intro x'. simpl. 
      consider (x' ?[ eq ] x); intros.
      + subst x'. unfold subst_fresh. simpl.
        consider (x ?[ eq ] x); congruence.
      + rewrite <- IHxs. unfold subst_fresh.
        simpl. 
        consider (x ?[ eq ] x'); intros; [congruence|].
        consider (x' ?[ eq ]x); intros; [congruence|reflexivity].
    Qed.

End SubstFresh.
