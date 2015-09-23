(* -*- coding: utf-8 -*- *)

Require Import UniMath.Foundations.Sets.
Require UniMath.Ktheory.Utilities.
Import UniMath.Ktheory.Utilities.Notation.
Definition unit : hSet := tpair isaset unit isasetunit.
Definition Product {I} (X:I -> hSet) : hSet.
  intros. exists (Utilities.Section (funcomp X set_to_type)).
  apply (impred 2); intros i. apply (pr2 (X i)). Defined.    
