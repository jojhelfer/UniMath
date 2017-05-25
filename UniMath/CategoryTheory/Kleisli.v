(** **********************************************************
Contents:
        - "Kleisli" definition of monad
        - proof of equivalence between this definition and the "monoidal" definition

Written by: Joseph Helfer (May 2017)

************************************************************)
Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.

Local Open Scope cat.

(* definition of "Kleisli style" monad *)
Section kleisli_def.

Definition kleisli_data (C : precategory) : UU :=
  ∑ T : C → C, ((∏ a : C, a --> T a) × (∏ a b : C, a --> T b -> T a --> T b)).

Definition fun_on_objects_from_kleisli_data {C : precategory} (T : kleisli_data C) := pr1 T.

Coercion fun_on_objects_from_kleisli_data : kleisli_data >-> Funclass.

Definition unit {C : precategory} (T : kleisli_data C) := pr1 (pr2 T).
Definition lift {C : precategory} (T : kleisli_data C) {a b : C} := pr2 (pr2 T) a b.

Definition kleisli_laws {C : precategory} (T : kleisli_data C) : UU :=
  ((∏ a : C, lift T (unit T a) = identity (T a)) × (∏ (a b : C) (f : a --> T b), unit T a · lift T f = f)) ×
  (∏ (a b c : C) (f : a --> T b) (g : b --> T c), lift T f · lift T g = lift T (f · lift T g)).

Definition kleisli (C : precategory) : UU := ∑ T : kleisli_data C, kleisli_laws T.

Definition kleisli_law1 {C : precategory} (T : kleisli C) := pr1 (pr1 (pr2 T)).
Definition kleisli_law2 {C : precategory} (T : kleisli C) := pr2 (pr1 (pr2 T)).
Definition kleisli_law3 {C : precategory} (T : kleisli C) := pr2 (pr2 T).

Definition kleisli_data_from_kleisli {C : precategory} (T : kleisli C) : kleisli_data C := pr1 T.
Coercion kleisli_data_from_kleisli : kleisli >-> kleisli_data.

End kleisli_def.

(* construction of "monoidal style" monad from "Kleisli style" monad *)
Section monad_to_kleisli.

Definition monad_to_kleisli_data {C : precategory} (T : Monad_data C) : kleisli_data C :=
  (functor_on_objects T,, ((fun (a : C) => (η T a)),,
                            (fun (a b: C) (f : a --> T b) => #T f · μ T b))).

Lemma monad_to_kleisli_laws {C : precategory} (T : Monad C) : kleisli_laws (monad_to_kleisli_data T).
Proof.
  apply tpair.
  apply tpair.
  + apply Monad_law2.
  + intros a b f.
    unfold unit.
    unfold lift.
    simpl.
    rewrite assoc.
    rewrite <- (nat_trans_ax (η T) a).
    rewrite <- assoc.
    rewrite (@Monad_law1 C).
    rewrite (id_right).
    apply idpath.
  + intros a b c f g.
    unfold lift.
    simpl.
    rewrite <- assoc.
    rewrite (assoc (μ T b)).
    rewrite <- nat_trans_ax.
    rewrite !functor_comp.
    rewrite <- !assoc.
    rewrite <- (@Monad_law3 C).
    apply idpath.
Qed.

Definition monad_to_kleisli {C : precategory} (T : Monad C) : kleisli C :=
  (_,, monad_to_kleisli_laws T).

End monad_to_kleisli.

(* construction of "Kleisli style" monad from "monoidal style" monad *)
Section kleisli_to_monad.

Definition kleisli_to_monad_functor_data {C : precategory} (T : kleisli_data C) : functor_data C C :=
  mk_functor_data (fun_on_objects_from_kleisli_data T) (fun (a b : C) (f : a --> b) => lift T (f · unit T b)).

Lemma kleisli_to_monad_functor_laws {C : precategory} (T: kleisli C) :
  is_functor (kleisli_to_monad_functor_data T).
Proof.
  apply tpair.
  + intro a.
    simpl.
    rewrite id_left.
    rewrite (kleisli_law1 T).
    apply idpath.
  + intros a b c f g.
    simpl.
    rewrite (kleisli_law3 T).
    rewrite <- !assoc.
    rewrite (kleisli_law2 T).
    apply idpath.
Qed.

Definition kleisli_to_monad_functor {C : precategory} (T: kleisli C) : C ⟶ C :=
  (_,, kleisli_to_monad_functor_laws T).

Definition kleisli_to_monad_μ_data {C : precategory} (T: kleisli C) :
  let F := kleisli_to_monad_functor T in ∏ x : C, (F ∙ F) x --> F x :=
  fun (x : C) => (lift T) (identity (T x)).

Lemma kleisli_to_monad_μ_law {C : precategory} (T: kleisli C) :
  is_nat_trans _ _ (kleisli_to_monad_μ_data T).
Proof.
  intros x x' f.
  unfold kleisli_to_monad_μ_data.
  simpl.
  rewrite (kleisli_law3 T).
  rewrite <- assoc.
  rewrite (kleisli_law2 T).
  rewrite id_right.
  rewrite (kleisli_law3 T).
  rewrite id_left.
  apply idpath.
Qed.

Definition kleisli_to_monad_μ {C : precategory} (T : kleisli C) :
  let F := kleisli_to_monad_functor T in (F ∙ F) ⟹ F :=
  (_,, kleisli_to_monad_μ_law T).

Definition kleisli_to_monad_η_data {C : precategory} (T: kleisli C) :
  ∏ x : C, functor_identity C x --> (kleisli_to_monad_functor T) x := unit T.

Lemma kleisli_to_monad_η_law {C : precategory} (T: kleisli C) :
  is_nat_trans _ _ (kleisli_to_monad_η_data T).
Proof.
  intros x x' f.
  unfold kleisli_to_monad_η_data.
  simpl.
  rewrite (kleisli_law2 T).
  apply idpath.
Qed.

Definition kleisli_to_monad_η {C : precategory} (T : kleisli C) :
  functor_identity C ⟹ kleisli_to_monad_functor T :=
  (_,, kleisli_to_monad_η_law T).

Definition kleisli_to_monad_data {C : precategory} (T : kleisli C) : Monad_data C :=
  ((kleisli_to_monad_functor T,, kleisli_to_monad_μ T),, kleisli_to_monad_η T).

Lemma kleisli_to_monad_laws {C : precategory} (T : kleisli C) :
  Monad_laws (kleisli_to_monad_data T).
Proof.
  apply tpair.
  apply tpair.
  + intro c.
    simpl.
    unfold kleisli_to_monad_η_data.
    unfold kleisli_to_monad_μ_data.
    apply kleisli_law2.
  + intro c.
    simpl.
    unfold kleisli_to_monad_η_data.
    unfold kleisli_to_monad_μ_data.
    rewrite (kleisli_law3 T).
    rewrite <- assoc.
    rewrite (kleisli_law2 T).
    rewrite id_right.
    rewrite (kleisli_law1 T).
    apply idpath.
  + intro c.
    simpl.
    unfold kleisli_to_monad_μ_data.
    rewrite !(kleisli_law3 T).
    rewrite id_left.
    rewrite <- assoc.
    rewrite (kleisli_law2 T).
    rewrite id_right.
    apply idpath.
Qed.

Definition kleisli_to_monad {C : precategory} (T : kleisli C) : Monad C :=
  (_,, kleisli_to_monad_laws T).

End kleisli_to_monad.