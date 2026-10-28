import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyLift
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyComposition
import OAI.RepresentationTheory.Weil.UnitarySplitting.PositiveCommutation

/-! # Canonical Cayley Lift -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CanonicalCayleyLift.Construction

noncomputable section

/-! Canonical positive Cayley lifts in the circle extension and their
Gaussian-phase multiplication law. -/

open _root_.MeasureTheory

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E] {m n : ℕ}
variable [CompleteSpace F] [LocallyCompactSpace F] [CharZero F] [IsUltrametricDist F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K) (hF : ¬ DiscreteTopology F)
variable (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
variable (hn : ∃ x : F, ψ x ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))) [ν.IsAddHaarMeasure]

def ultraCayleyLiftRadius (g : FrameTransport.Construction.StandardSymplectic F (m * n))
    (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)) (hD : ∀ x, D x = g.val x - x) : ℝ :=
  Classical.choose (UltraCayleyLift.Construction.exists_ultraCayleyLift σ H K c hF ψ hc hu hn ν g D hD)

def ultraCayleyLift (g : FrameTransport.Construction.StandardSymplectic F (m * n))
    (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)) (hD : ∀ x, D x = g.val x - x) :
    Oscillator.Construction.CircleExtension σ H K c ψ :=
  Classical.choose (Classical.choose_spec (UltraCayleyLift.Construction.exists_ultraCayleyLift σ H K c hF ψ hc hu hn ν g D hD))

theorem ultraCayleyLift_spec (g : FrameTransport.Construction.StandardSymplectic F (m * n))
    (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)) (hD : ∀ x, D x = g.val x - x) :
    0 < ultraCayleyLiftRadius σ H K c hF ψ hc hu hn ν g D hD ∧
      Oscillator.Construction.circleProjection σ H K c ψ (ultraCayleyLift σ H K c hF ψ hc hu hn ν g D hD) =
        FrameTransport.Construction.frameSymplectic σ H K c g ∧
      ∀ f, UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν g D hD f =
        (ultraCayleyLiftRadius σ H K c hF ψ hc hu hn ν g D hD : ℂ) •
          (ultraCayleyLift σ H K c hF ψ hc hu hn ν g D hD).val.2 f :=
  Classical.choose_spec (Classical.choose_spec (UltraCayleyLift.Construction.exists_ultraCayleyLift σ H K c hF ψ hc hu hn ν g D hD))

theorem ultraCayleyLift_congr (g h : FrameTransport.Construction.StandardSymplectic F (m * n))
    (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))
    (hDg : ∀ x, D x = g.val x - x) (hDh : ∀ x, D x = h.val x - x) (heq : g = h) :
    ultraCayleyLift σ H K c hF ψ hc hu hn ν g D hDg =
      ultraCayleyLift σ H K c hF ψ hc hu hn ν h D hDh := by
  cases heq
  rfl

theorem ultraCayleyLift_multiplication
    (g h : FrameTransport.Construction.StandardSymplectic F (m * n))
    (Dg Dh Dgh : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))
    (hDg : ∀ x, Dg x = g.val x - x) (hDh : ∀ x, Dh x = h.val x - x)
    (hDgh : ∀ x, Dgh x = (g * h).val x - x)
    (Γ : ℂ) (hΓ0 : Γ ≠ 0) (hΓ : GaussianCutoff.Construction.HasGaussianCutoffs ν ψ
      (fun x => CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F (m * n)) Dg x +
        CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F (m * n)) Dh x) Γ) :
    ultraCayleyLift σ H K c hF ψ hc hu hn ν g Dg hDg *
      ultraCayleyLift σ H K c hF ψ hc hu hn ν h Dh hDh =
        Oscillator.Construction.circleScalar σ H K c ψ (DiagonalNormGaussian.Construction.gaussianCircle Γ hΓ0) *
          ultraCayleyLift σ H K c hF ψ hc hu hn ν (g * h) Dgh hDgh := by
  let ag := ultraCayleyLift σ H K c hF ψ hc hu hn ν g Dg hDg
  let ah := ultraCayleyLift σ H K c hF ψ hc hu hn ν h Dh hDh
  let agh := ultraCayleyLift σ H K c hF ψ hc hu hn ν (g * h) Dgh hDgh
  let rg := ultraCayleyLiftRadius σ H K c hF ψ hc hu hn ν g Dg hDg
  let rh := ultraCayleyLiftRadius σ H K c hF ψ hc hu hn ν h Dh hDh
  let rgh := ultraCayleyLiftRadius σ H K c hF ψ hc hu hn ν (g * h) Dgh hDgh
  obtain ⟨hrg, hpg, hMg⟩ := ultraCayleyLift_spec σ H K c hF ψ hc hu hn ν g Dg hDg
  obtain ⟨hrh, hph, hMh⟩ := ultraCayleyLift_spec σ H K c hF ψ hc hu hn ν h Dh hDh
  obtain ⟨hrgh, hpgh, hMgh⟩ := ultraCayleyLift_spec σ H K c hF ψ hc hu hn ν (g * h) Dgh hDgh
  have heq (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n)) :
      ((rg * rh : ℝ) : ℂ) • (ag * ah).val.2 f = (Γ * (rgh : ℂ)) • agh.val.2 f := by
    have hh := UltraCayleyComposition.Construction.ultraCayleyOperator_composition hF ψ hc hu hn ν g h Dg Dh Dgh hDg hDh hDgh Γ hΓ f
    rw [hMg, hMh, map_smul, hMgh, smul_smul, smul_smul] at hh
    rw [Complex.ofReal_mul]
    exact hh
  have hphase := PositiveCommutation.Construction.positive_operator_scalar_phase (ag * ah).val.2.toLinearMap agh.val.2.toLinearMap
    (ag * ah).property.1 agh.property.1 (LocalTest.Construction.ultraTestVector F hF (m * n))
    (LocalTest.Construction.ultraTestVector_ne_zero F hF (m * n)) (rg * rh) rgh (mul_pos hrg hrh) hrgh Γ heq
  apply Subtype.ext
  apply Prod.ext
  · change Oscillator.Construction.circleProjection σ H K c ψ (ag * ah) =
      Oscillator.Construction.circleProjection σ H K c ψ (Oscillator.Construction.circleScalar σ H K c ψ (DiagonalNormGaussian.Construction.gaussianCircle Γ hΓ0) * agh)
    rw [map_mul, map_mul, hpg, hph, hpgh, Oscillator.Construction.circleScalar_projects_to_one, one_mul, map_mul]
  · apply LinearEquiv.ext
    intro f
    exact hphase f

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CanonicalCayleyLift.Construction
