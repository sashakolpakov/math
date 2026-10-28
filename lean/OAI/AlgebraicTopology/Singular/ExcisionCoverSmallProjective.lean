/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
This file has been modified.
-/
import OAI.AlgebraicTopology.Singular.ExcisionCoverSmall
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Excision Cover Small Projective -/

namespace OAI.AlgebraicTopology.Singular.ExcisionCoverSmallProjective

noncomputable section

/-!

# Projective reduction for the small-chain theorem

Integral simplicial chain groups are free abelian and hence projective. Consequently, for the
nonnegatively graded singular chain complexes used by the excision development, it is enough to
prove that the cover-small inclusion is a quasi-isomorphism: projectivity upgrades it to a
chain-homotopy equivalence.
-/

open _root_.AlgebraicTopology _root_.CategoryTheory
open scoped Simplicial

/-- If the cover-small inclusion is a quasi-isomorphism, then it is a chain-homotopy
equivalence, because all the chain groups involved are projective. -/
theorem coverSmallChainApproximation_of_quasiIso
    {i : Type} (X : TopCat) (U : i → Set X)
    (h : QuasiIso (ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U)) :
    HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.down ℕ)
      (ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U) := by
  let : QuasiIso (ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U) := h
  let projectiveInteger : Projective (AddCommGrpCat.of ℤ) :=
    ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.map_projective_iff
      (ModuleCat.of ℤ ℤ)).mpr inferInstance
  let projectiveSmall (n : ℕ) :
      Projective ((ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U).X n) := by
    change Projective
      (∐ fun _ : (ExcisionCoverSmall.coverSmallSingularSubcomplex X U : SSet).obj
          (Opposite.op (SimplexCategory.mk n)) ↦
        AddCommGrpCat.of ℤ)
    infer_instance
  let projectiveFull (n : ℕ) :
      Projective ((ExcisionCoverSmall.IntegralSingularChainComplexObj X).X n) := by
    change Projective
      (∐ fun _ : (TopCat.toSSet.obj X).obj
          (Opposite.op (SimplexCategory.mk n)) ↦ AddCommGrpCat.of ℤ)
    infer_instance
  exact (ChainComplex.quasiIso_iff_of_projective
    (ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U)).mp (by infer_instance)

end

end OAI.AlgebraicTopology.Singular.ExcisionCoverSmallProjective
