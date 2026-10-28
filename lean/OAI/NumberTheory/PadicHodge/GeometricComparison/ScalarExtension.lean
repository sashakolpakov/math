import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Scalar Extension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarExtension.ScalarExtensionRanges

noncomputable section

/-! Scalar extension of an actual image is the image of the scalar-extended map. -/

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] (S : Type*) [Semiring S] [Algebra R S]
  {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

theorem range (f : M →ₗ[R] N) : f.range.baseChange S = (f.baseChange S).range := by
  have hf : f.range.subtype.comp f.rangeRestrict = f := rfl
  have hb : (f.range.subtype.baseChange S).comp (f.rangeRestrict.baseChange S) =
      f.baseChange S := (LinearMap.baseChange_comp _ _).symm.trans (congrArg (fun g => g.baseChange S) hf)
  rw [Submodule.baseChange, ← hb]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := LinearMap.baseChange_surjective S f.surjective_rangeRestrict x
    exact ⟨z, congrArg (f.range.subtype.baseChange S) hz⟩
  · rintro ⟨x, rfl⟩
    exact ⟨f.rangeRestrict.baseChange S x, rfl⟩

theorem map (P : Submodule R M) (f : M →ₗ[R] N) :
    (P.map f).baseChange S = (P.baseChange S).map (f.baseChange S) := by
  rw [← LinearMap.range_domRestrict P f, ScalarExtensionRanges.range]
  change ((f.comp P.subtype).baseChange S).range = _
  rw [LinearMap.baseChange_comp, LinearMap.range_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarExtension.ScalarExtensionRanges
