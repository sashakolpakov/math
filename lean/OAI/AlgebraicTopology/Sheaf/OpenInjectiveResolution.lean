/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicTopology.Sheaf.OpenRestriction
import OAI.Algebra.Homology.LiftToInjective
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Open Injective Resolution -/

namespace OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Comparing an ambient resolution with a resolution on an open subspace

The comparison is lifted on the open subspace across the restricted
augmentation. Exact open restriction and the normalized constant-sheaf
comparison prove that this augmentation is a monic quasi-isomorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable (X : TopCat.{0}) (U : Opens X) (A : AddCommGrpCat.{0})

set_option backward.isDefEq.respectTransparency false in
/-- Let `X` be a topological space and `A` an abelian group. This is a chosen injective resolution
`A_X → I^•` of the sheaf of locally constant `A`-valued functions on `X`, indexed by nonnegative
integers. -/
def ambientConstantInjectiveResolution :
    InjectiveResolution (C := Sheaf AddCommGrpCat.{0} X)
      𝓒[X; A] :=
  injectiveResolution (C := Sheaf AddCommGrpCat.{0} X) _

end

end OAI.AlgebraicTopology.Sheaf.OpenInjectiveResolution.TopCat
