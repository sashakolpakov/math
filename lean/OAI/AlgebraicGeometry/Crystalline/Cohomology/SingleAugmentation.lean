import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology

/-! # Single Augmentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SingleAugmentation.SingleAugmentationExact

noncomputable section

/-! # A nonnegative resolution has an exact injective augmentation -/

open _root_.CategoryTheory Limits _root_.HomologicalComplex

variable {C : Type*} [Category C] [Abelian C] (A : C) (K : CochainComplex C ℕ)
  (f : (CochainComplex.single₀ C).obj A ⟶ K) (hf : QuasiIsoAt f 0)
  (w : f.f 0 ≫ K.d 0 1 = 0)

include hf in
theorem exact_mono : (ShortComplex.mk (f.f 0) (K.d 0 1) w).Exact ∧ Mono (f.f 0) := by
  let g := (shortComplexFunctor' C (ComplexShape.up ℕ) 0 0 1).map f
  have hg : ShortComplex.QuasiIso g :=
    (quasiIsoAt_iff' f 0 0 1 (by simp) (by simp)).mp hf
  exact (ShortComplex.quasiIso_iff_of_zeros g (by simp; rfl) (by simp; rfl) (by simp; rfl)).mp hg

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SingleAugmentation.SingleAugmentationExact
