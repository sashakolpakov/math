import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticNorm

/-! # Norm Polar Form -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.NormPolarForm.Construction

noncomputable section

/-! The polar bilinear form of the quadratic field norm. -/

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable [FiniteDimensional F E] [CharZero F]
variable (σ : E ≃ₐ[F] E)

def normPolarForm : LinearMap.BilinForm F E :=
  (Algebra.traceForm F E).compl₂ σ.toLinearMap

omit [FiniteDimensional F E] [CharZero F] in
theorem normPolarForm_apply (x y : E) : normPolarForm σ x y = Algebra.trace F E (x * σ y) := rfl

theorem normPolarForm_nondegenerate : (normPolarForm σ).Nondegenerate := by
  constructor
  · intro x hx
    apply (traceForm_nondegenerate F E).1 x
    intro y
    obtain ⟨z, rfl⟩ := σ.surjective y
    exact hx z
  · intro y hy
    apply σ.injective
    rw [map_zero]
    apply (traceForm_nondegenerate F E).2 (σ y)
    exact hy

variable (hQuadratic : Module.finrank F E = 2) (hne : ∃ z : E, σ z ≠ z)

include hQuadratic hne in
theorem quadratic_norm_add (x y : E) :
    Algebra.norm F (x + y) = Algebra.norm F x + Algebra.norm F y + normPolarForm σ x y := by
  apply (algebraMap F E).injective
  simp only [map_add, QuadraticNorm.Construction.quadratic_norm_formula hQuadratic σ hne,
    normPolarForm_apply, QuadraticNorm.Construction.quadratic_trace_formula hQuadratic σ hne, map_mul]
  have hσ := TracePairing.Construction.quadratic_automorphism_involutive hQuadratic σ
  rw [hσ y]
  ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.NormPolarForm.Construction
