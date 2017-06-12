(** **********************************************************
Contents:
        - "Kleisli" definition of monad
        - proof of equivalence between this definition and the "monoidal" definition

************************************************************)
Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.

Local Open Scope cat.

(** * Definition of "Kleisli style" monad *)
Section kleisli_def.

Definition kleisli_data (C : precategory) : UU :=
  ∑ T : C → C, ((∏ a : C, a --> T a) × (∏ a b : C, a --> T b -> T a --> T b)).

Definition fun_on_objects_from_kleisli_data {C : precategory} (T : kleisli_data C) := pr1 T.
Coercion fun_on_objects_from_kleisli_data : kleisli_data >-> Funclass.

Definition unit {C : precategory} (T : kleisli_data C) := pr1 (pr2 T).
Definition bind {C : precategory} (T : kleisli_data C) {a b : C} := pr2 (pr2 T) a b.

Definition kleisli_laws {C : precategory} (T : kleisli_data C) : UU :=
  ((∏ a : C, bind T (unit T a) = identity (T a)) ×
   (∏ (a b : C) (f : a --> T b), unit T a · bind T f = f)) ×
   (∏ (a b c : C) (f : a --> T b) (g : b --> T c), bind T f · bind T g = bind T (f · bind T g)).

Lemma isaprop_kleisli_laws {C : precategory} (hs : has_homsets C) (T : kleisli_data C) :
  isaprop (kleisli_laws T).
Proof.
  repeat apply isapropdirprod;
  repeat (apply impred; intro);
  apply hs.
Qed.

Definition kleisli (C : precategory) : UU := ∑ T : kleisli_data C, kleisli_laws T.

Definition kleisli_law1 {C : precategory} (T : kleisli C) := pr1 (pr1 (pr2 T)).
Definition kleisli_law2 {C : precategory} (T : kleisli C) := pr2 (pr1 (pr2 T)).
Definition kleisli_law3 {C : precategory} (T : kleisli C) := pr2 (pr2 T).

Definition kleisli_data_from_kleisli {C : precategory} (T : kleisli C) : kleisli_data C := pr1 T.
Coercion kleisli_data_from_kleisli : kleisli >-> kleisli_data.

End kleisli_def.

(** * Construction of "monoidal style" monad from "Kleisli style" monad *)
Section monad_to_kleisli.

  Definition monad_to_kleisli_data {C : precategory} (T : Monad_data C) : kleisli_data C :=
    (functor_on_objects T,, (eta T,, (fun (a b: C) (f : a --> T b) => #T f · mu T b))).

  Lemma monad_to_kleisli_laws {C : precategory} (T : Monad C) :
    kleisli_laws (monad_to_kleisli_data (pr1 T)).
  Proof.
    apply tpair.
    apply tpair.
    + apply Monad_law2.
    + apply (@η_bind C T).
    + apply (@bind_bind C T).
  Qed.

  Definition monad_to_kleisli {C : precategory} (T : Monad C) : kleisli C :=
    (_,, monad_to_kleisli_laws T).

End monad_to_kleisli.

(** * Construction of "Kleisli style" monad from "monoidal style" monad *)
Section kleisli_to_monad.

  Definition kleisli_to_monad_on_morphisms {C : precategory} (T : kleisli_data C) :
    ∏ (a b : C) (f : a --> b), (T a --> T b) :=
    fun (a b : C) (f : a --> b) => bind T (f · unit T b).

  Definition kleisli_to_monad_functor_data {C : precategory} (T : kleisli_data C) :
    functor_data C C := (fun_on_objects_from_kleisli_data T,, kleisli_to_monad_on_morphisms T).

  Lemma kleisli_to_monad_functor_laws {C : precategory} (T: kleisli C) :
    is_functor (kleisli_to_monad_functor_data T).
  Proof.
    apply tpair; intro; intros; simpl; unfold kleisli_to_monad_on_morphisms.
    now rewrite id_left, (kleisli_law1 T).
    now rewrite (kleisli_law3 T), <- !assoc, (kleisli_law2 T).
  Qed.

  Definition kleisli_to_monad_μ_data {C : precategory} (T: kleisli C) : ∏ x : C, T (T x) --> T x :=
    fun (x : C) => (bind T) (identity (T x)).

  Lemma kleisli_to_monad_μ_law {C : precategory} (T: kleisli C) :
    is_nat_trans (functor_composite_data
                    (kleisli_to_monad_functor_data T)
                    (kleisli_to_monad_functor_data T)) (kleisli_to_monad_functor_data T)
                 (kleisli_to_monad_μ_data T).
  Proof.
    intros x x' f.
    unfold kleisli_to_monad_μ_data.
    simpl.
    unfold kleisli_to_monad_on_morphisms.
    now rewrite (kleisli_law3 T), <- assoc, (kleisli_law2 T), id_right, (kleisli_law3 T), id_left.
  Qed.

  Definition kleisli_to_monad_η_data {C : precategory} (T: kleisli C) :
    ∏ x : C, functor_identity C x --> (kleisli_to_monad_functor_data T) x := unit T.

  Lemma kleisli_to_monad_η_law {C : precategory} (T: kleisli C) :
    is_nat_trans _ _ (kleisli_to_monad_η_data T).
  Proof.
    intros x x' f.
    unfold kleisli_to_monad_η_data.
    simpl.
    unfold kleisli_to_monad_on_morphisms.
    now rewrite (kleisli_law2 T).
  Qed.

  Definition kleisli_to_monad_data {C : precategory} (T : kleisli C) : Monad_data C :=
    (fun_on_objects_from_kleisli_data T,,
                                      dirprodpair (dirprodpair (kleisli_to_monad_on_morphisms T)
                                                               (kleisli_to_monad_μ_data T))
                                                  (kleisli_to_monad_η_data T)).

  Lemma kleisli_to_monad_functoriality {C : precategory} (T : kleisli C) :
    is_functorial_Monad_data (kleisli_to_monad_data T).
  Proof.
    apply tpair.
    apply tpair.
    apply kleisli_to_monad_functor_laws.
    apply kleisli_to_monad_μ_law.
    apply kleisli_to_monad_η_law.
  Qed.

  Lemma kleisli_to_monad_laws {C : precategory} (T : kleisli C) :
    Monad_laws (kleisli_to_monad_data T).
  Proof.
    apply tpair; try apply tpair;
    unfold
      kleisli_to_monad_data,
      kleisli_to_monad_on_morphisms,
      kleisli_to_monad_μ_data,
      kleisli_to_monad_η_data,
      eta,
      mu;
    simpl;
    intro.
    now rewrite (kleisli_law2 T).
    now rewrite (kleisli_law3 T), <- assoc, (kleisli_law2 T), id_right, (kleisli_law1 T).
    now rewrite !(kleisli_law3 T), <- assoc, (kleisli_law2 T), id_right, id_left.
  Qed.

  Definition kleisli_to_monad {C : precategory} (T : kleisli C) : Monad C :=
    (_,, dirprodpair (kleisli_to_monad_functoriality T) (kleisli_to_monad_laws T)).

End kleisli_to_monad.

(** * Equivalence of two constructions *)
Section kleisli_monad_equivalence.

  Lemma kleisli_to_monad_to_kleisli_data {C : precategory} (T : kleisli C) :
    pr1 (monad_to_kleisli (kleisli_to_monad T)) = pr1 T.
  Proof.
    use total2_paths_f.
    + apply idpath.
    + rewrite idpath_transportf.
      apply dirprod_paths.
    - apply idpath.
    - repeat (apply funextsec; unfold homot; intro).
      simpl.
      unfold kleisli_to_monad_on_morphisms, mu, kleisli_to_monad_data, kleisli_to_monad_μ_data.
      simpl.
      now rewrite (kleisli_law3 T), <- assoc, (kleisli_law2 T), id_right.
  Qed.

  Proposition kleisli_to_monad_to_kleisli {C : precategory} (hs : has_homsets C) (T : kleisli C) :
    (monad_to_kleisli (kleisli_to_monad T)) = T.
  Proof.
    use total2_paths_f.
    apply kleisli_to_monad_to_kleisli_data.
    now apply isaprop_kleisli_laws.
  Qed.

  Lemma monad_to_kleisli_to_monad_data {C : precategory} (T : Monad C) :
    pr1 (kleisli_to_monad (monad_to_kleisli T)) = pr1 T.
    use total2_paths_f.
    apply idpath.
    rewrite idpath_transportf.
    apply dirprod_paths.
    apply dirprod_paths;
      repeat (apply funextsec; unfold homot; intro);
      simpl.
    - unfold kleisli_to_monad_on_morphisms, monad_to_kleisli_data, bind, unit, eta.
      simpl.
      rewrite (functor_comp T), <- assoc.
      change (# T x1 · (# T ((η T) x0) · (μ T) x0) = pr1 (pr1 (pr2 (pr1 T))) x x0 x1).
      now rewrite (@Monad_law2 C T x0), id_right.
    - unfold kleisli_to_monad_μ_data, bind.
      simpl.
      now rewrite (functor_id T), id_left.
    - apply idpath.
  Qed.

  Proposition monad_to_kleisli_to_monad {C : precategory} (hs : has_homsets C) (T : Monad C) :
    kleisli_to_monad (monad_to_kleisli T) = T.
  Proof.
    use total2_paths_f.
    apply monad_to_kleisli_to_monad_data.
    apply dirprod_paths.
    now apply isaprop_is_functoriral_Monad_data.
    now apply isaprop_Monad_laws.
  Qed.

  Proposition kleisli_weq_Monad {C : precategory} (hs : has_homsets C) : weq (kleisli C) (Monad C).
  Proof.
    assert (isweq (@kleisli_to_monad C)).
    apply (gradth _ _ (@kleisli_to_monad_to_kleisli C hs) (@monad_to_kleisli_to_monad C hs)).
    apply (_,, X).
  Qed.

  Proposition kleisli_eq_Monad {C : precategory} (hs : has_homsets C) : kleisli C = Monad C.
  Proof.
    apply univalence.
    apply kleisli_weq_Monad.
    apply hs.
  Qed.

End kleisli_monad_equivalence.
