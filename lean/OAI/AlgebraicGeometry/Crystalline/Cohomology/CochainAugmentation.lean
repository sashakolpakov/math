import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Cochain Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation.CochainAugmentationCriterion

noncomputable section

/-!
# Degree-zero criterion for a cochain augmentation

When the source has zero first differential, a map induces an
isomorphism on degree-zero cohomology precisely when its first component
is injective and identifies its source with the zero-cocycles.
-/

open _root_.CategoryTheory Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℕ} (f : K ⟶ L) (hK : K.d 0 1 = 0)

def initialShort : ShortComplex C :=
  ShortComplex.mk (f.f 0) (L.d 0 1) (by rw [f.comm, hK, zero_comp])

theorem quasiIsoAt_zero_iff :
    QuasiIsoAt f 0 ↔ (initialShort f hK).Exact ∧ Mono (f.f 0) := by
  rw [CochainComplex.quasiIsoAt₀_iff]
  exact ShortComplex.quasiIso_iff_of_zeros
    ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℕ) 0 0 1).map f)
    (by change K.d 0 0 = 0; simp) hK (by change L.d 0 0 = 0; simp)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CochainAugmentation.CochainAugmentationCriterion
