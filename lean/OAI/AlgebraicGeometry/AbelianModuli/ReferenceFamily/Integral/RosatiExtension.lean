import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ActionExtension
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reconstruction

/-! # Rosati Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.RosatiExtension

noncomputable section

/-! The actual rational span of the ring of integers extends a bilinear
Rosati identity from integral operators to the entire CM field. -/

open scoped TensorProduct

variable {E W : Type*} [Field E] [NumberField E] [Algebra ℚ E]
    [AddCommGroup W] [Module ℚ W]

theorem rationalLinearMap_eq_of_integers (f g : E →ₗ[ℚ] W)
    (h : ∀ a : NumberField.RingOfIntegers E, f (a : E) = g (a : E)) : f = g := by
  ext x
  obtain ⟨t, rfl⟩ := (ActionExtension.integralRationalTensorIso (E := E)).surjective x
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => rw [map_add, map_add, map_add, ht, hu]
  | tmul q a =>
    have he : ActionExtension.integralRationalTensorIso (q ⊗ₜ[ℤ] a) = q • (a : E) :=
      (Algebra.IsPushout.equiv_tmul ℤ ℚ (NumberField.RingOfIntegers E) E q a).trans
        (Algebra.smul_def q (a : E)).symm
    rw [he, map_smul, map_smul, h]

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module E V] [IsScalarTower ℚ E V]
    [NumberField.IsCMField E]

theorem rosatiBalanced_of_integers (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (h : ∀ (a : NumberField.RingOfIntegers E) (x y : V),
      ψ ((a : E) • x) y = ψ x (ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (a : E) • y)) :
    Hermitian.Reconstruction.TraceReconstruction.RosatiBalanced (E := E) ψ := by
  intro a x y
  have he := rationalLinearMap_eq_of_integers
    (TraceReconstructionEq.TraceReconstruction.coefficientFunctional ψ x y)
    ((TraceReconstructionEq.TraceReconstruction.coefficientFunctional ψ.flip y x).comp (ComplexMultiplication.CM.TraceForm.cmFieldConjugation E).toLinearMap)
    (fun b => h b x y)
  exact LinearMap.congr_fun he a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.RosatiExtension
