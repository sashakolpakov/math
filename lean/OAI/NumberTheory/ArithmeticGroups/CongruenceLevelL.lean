import OAI.NumberTheory.ArithmeticGroups.CongruenceLevelTrace
import OAI.Geometry.ComplexBall.PrescribedSignsOn
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Congruence Level L -/

namespace OAI.NumberTheory.ArithmeticGroups.CongruenceLevelL

noncomputable section

/-! Unconditional composition with the committed native PrescribedSigns and RiemannProjectivity proofs.
The older conditional declaration and its specification remain unchanged. -/

open scoped Classical

theorem l32Input_proved (E Place : Type*)
    [Field E] [Algebra ℚ E] [NumberField E]
    [IsGalois ℚ E] [NumberField.IsCMField E] [Fintype Place] : CongruenceLevelDatum.PrescribedSignsInput E Place := by
  intro σ hσ μ δ hδ hδc H hHermitian hμpos hμneg hcompact d
  obtain ⟨a, F, h, _⟩ :=
    Geometry.ComplexBall.Intrinsic.PrescribedSigns.lagrangians_with_prescribed_compact_place_signs_native
      σ hσ μ δ hδ hδc H hHermitian hμpos hμneg hcompact d
  exact ⟨a, F, h⟩

theorem riemannInput_proved : CongruenceLevelDatum.RiemannInput := by
  intro T _ _ _ Γ _ _
  exact Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion T Γ

/-- The complete original analytic reference datum, with no result assumptions. -/
theorem reference_polarized_abelian_moduli_datum_unconditional
    {E Place : Type*} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Fintype Place] [IsGalois ℚ E]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective
      (fun p : Place × Bool =>
        if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (μ : Place) (b : E)
    (hb : NumberField.IsCMField.complexConj E b = b)
    (hb_nonzero : b ≠ 0)
    (hμ : (σ μ b).re < 0)
    (hcompact : ∀ τ, τ ≠ μ → 0 < (σ τ b).re)
    (dref : Place → Bool) : CongruenceLevelDatum.ReferenceDatum σ μ b dref :=
  CongruenceLevelTrace.reference_polarized_abelian_moduli_datum (l32Input_proved E Place)
    riemannInput_proved σ hσ μ b hb hb_nonzero hμ hcompact dref

end

end OAI.NumberTheory.ArithmeticGroups.CongruenceLevelL
