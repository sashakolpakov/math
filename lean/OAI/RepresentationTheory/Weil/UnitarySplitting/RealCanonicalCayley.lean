import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyLift
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyComposition
import OAI.RepresentationTheory.Weil.UnitarySplitting.PositiveCommutation

/-! # Real Canonical Cayley -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealCanonicalCayley.Construction

noncomputable section

/-! Real canonical lifts multiply with the regularized Gaussian phase. -/

open _root_.MeasureTheory

variable {E : Type} [NormedField E] [Algebra ℝ E] {m n : ℕ}
variable (σ : E ≃ₐ[ℝ] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K)
variable (ψ : AddChar ℝ ℂ) (hc : Continuous (fun x : ℝ => ψ x)) (hu : ∀ x : ℝ, ‖ψ x‖ = 1)
variable (hn : ∃ x : ℝ, ψ x ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n))) [ν.IsAddHaarMeasure]

theorem realCayleyLift_congr (g h : FrameTransport.Construction.StandardSymplectic ℝ (m * n))
    (D : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n) ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n))
    (hDg : ∀ x, D x = g.val x - x) (hDh : ∀ x, D x = h.val x - x) (heq : g = h) :
    RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν g D hDg =
      RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν h D hDh := by
  cases heq
  rfl

theorem realCayleyLift_multiplication
    (g h : FrameTransport.Construction.StandardSymplectic ℝ (m * n))
    (Dg Dh Dgh : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n) ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n))
    (hDg : ∀ x, Dg x = g.val x - x) (hDh : ∀ x, Dh x = h.val x - x)
    (hDgh : ∀ x, Dgh x = (g * h).val x - x)
    (Γ : ℂ) (hΓ0 : Γ ≠ 0) (hΓ : QuadraticGaussianRegularization.Construction.HasGaussianRegularization ν ψ
      (fun x => CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ (m * n)) Dg x +
        CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ (m * n)) Dh x) Γ) :
    RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν g Dg hDg *
      RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν h Dh hDh =
        Oscillator.Construction.circleScalar σ H K c ψ (DiagonalNormGaussian.Construction.gaussianCircle Γ hΓ0) *
          RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν (g * h) Dgh hDgh := by
  let ag := RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν g Dg hDg
  let ah := RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν h Dh hDh
  let agh := RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν (g * h) Dgh hDgh
  let rg := RealCayleyLift.Construction.realCayleyLiftRadius σ H K c ψ hc hu hn ν g Dg hDg
  let rh := RealCayleyLift.Construction.realCayleyLiftRadius σ H K c ψ hc hu hn ν h Dh hDh
  let rgh := RealCayleyLift.Construction.realCayleyLiftRadius σ H K c ψ hc hu hn ν (g * h) Dgh hDgh
  obtain ⟨hrg, hpg, hMg⟩ := RealCayleyLift.Construction.realCayleyLift_spec σ H K c ψ hc hu hn ν g Dg hDg
  obtain ⟨hrh, hph, hMh⟩ := RealCayleyLift.Construction.realCayleyLift_spec σ H K c ψ hc hu hn ν h Dh hDh
  obtain ⟨hrgh, hpgh, hMgh⟩ := RealCayleyLift.Construction.realCayleyLift_spec σ H K c ψ hc hu hn ν (g * h) Dgh hDgh
  have heq (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ (m * n)) :
      ((rg * rh : ℝ) : ℂ) • (ag * ah).val.2 f = (Γ * (rgh : ℂ)) • agh.val.2 f := by
    have hh := RealCayleyComposition.Construction.realCayleyOperator_composition ψ hc hu hn ν g h Dg Dh Dgh hDg hDh hDgh Γ hΓ f
    rw [hMg, hMh, map_smul, hMgh, smul_smul, smul_smul] at hh
    rw [Complex.ofReal_mul]
    exact hh
  obtain ⟨u, hu0⟩ := LocalTest.Construction.exists_test_nonzero_of_real_coordinates (ContinuousAddEquiv.refl (Local.FunctionsMetaplectic.Construction.Position ℝ (m * n)))
  have hphase := PositiveCommutation.Construction.positive_operator_scalar_phase (ag * ah).val.2.toLinearMap agh.val.2.toLinearMap
    (ag * ah).property.1 agh.property.1 u hu0 (rg * rh) rgh (mul_pos hrg hrh) hrgh Γ heq
  apply Subtype.ext
  apply Prod.ext
  · change Oscillator.Construction.circleProjection σ H K c ψ (ag * ah) =
      Oscillator.Construction.circleProjection σ H K c ψ (Oscillator.Construction.circleScalar σ H K c ψ (DiagonalNormGaussian.Construction.gaussianCircle Γ hΓ0) * agh)
    rw [map_mul, map_mul, hpg, hph, hpgh, Oscillator.Construction.circleScalar_projects_to_one, one_mul, map_mul]
  · apply LinearEquiv.ext
    intro f
    exact hphase f

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealCanonicalCayley.Construction
