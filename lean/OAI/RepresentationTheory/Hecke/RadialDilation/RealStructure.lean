import OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates

/-! # Real Structure -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.RealStructure.Realization

noncomputable section

/-! Rational coordinate changes preserve the actual real structure. -/

open scoped Classical TensorProduct

theorem realConj_embedding_smul
    {E : Type*} [Field E] [Algebra ℚ E] {Place : Type*}
    (σ : Place → E →ₐ[ℚ] ℂ) (z : ℂ) (x : Fin 3 → E) :
    Geometry.ComplexBall.PrescribedSignsB.realConj (z • Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x) = star z • Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x := by
  ext τ j <;> simp [Geometry.ComplexBall.PrescribedSignsB.realConj, Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates, AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding, star_smul]

theorem rationalCoordinates_realConj
    (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
    {Place κ : Type*} [Fintype κ] [DecidableEq κ]
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (κ → ℚ)) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient Place) :
    RationalCoordinates.Realization.rationalCoordinates E σ hσ e (Geometry.ComplexBall.PrescribedSignsB.realConj u) = star (RationalCoordinates.Realization.rationalCoordinates E σ hσ e u) := by
  obtain ⟨x, rfl⟩ := (Complexification.Realization.pairedComplexification E σ hσ).surjective u
  change RationalCoordinates.Realization.rationalCoordinates E σ hσ e
    (Geometry.ComplexBall.PrescribedSignsB.realConjLinearMap Place (Complexification.Realization.pairedComplexification E σ hσ x)) = _
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, star_add]
  | tmul z x =>
      have hc : Geometry.ComplexBall.PrescribedSignsB.realConjLinearMap Place (Complexification.Realization.pairedComplexification E σ hσ (z ⊗ₜ[ℚ] x)) =
          Complexification.Realization.pairedComplexification E σ hσ (star z ⊗ₜ[ℚ] x) := by
        change Geometry.ComplexBall.PrescribedSignsB.realConj _ = _
        rw [Complexification.Realization.pairedComplexification_tmul, Complexification.Realization.pairedComplexification_tmul,
          realConj_embedding_smul]
      rw [hc, RationalCoordinates.Realization.rationalCoordinates_tmul, RationalCoordinates.Realization.rationalCoordinates_tmul]
      ext i
      simp

end

end OAI.RepresentationTheory.Hecke.RadialDilation.RealStructure.Realization
