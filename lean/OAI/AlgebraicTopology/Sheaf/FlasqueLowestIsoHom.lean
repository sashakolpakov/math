/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicTopology.Sheaf.FlasqueLowestCohomology

/-! # Flasque Lowest Iso Hom -/

namespace OAI.AlgebraicTopology.Sheaf.FlasqueLowestIsoHom.TopCat

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# The lowest-degree cohomology comparison for flasque complexes

-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex

universe u

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

@[simp] theorem lowestSectionCohomologyIso_hom (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque)
    (U : Opens X) :
    (FlasqueLowestCohomology.TopCat.lowestSectionCohomologyIso X K N n hK hflasque U).hom =
      CohomologySection.TopCat.sectionCohomologyToSheafSection X K n U := rfl

end

end OAI.AlgebraicTopology.Sheaf.FlasqueLowestIsoHom.TopCat
