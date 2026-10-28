import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakCayleyTestCoefficients
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylSynthesis
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylResolutionOperator
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianLinearity

/-! # Cayley Synthesis Pairing -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CayleySynthesisPairing.Construction

noncomputable section

/-! The Cayley coefficient amplitudes synthesize a test vector representing
the weak Gaussian form after the positive reconstruction normalization. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

theorem standardCayleyWeylPhase_continuous
    {F : Type} [NormedField F] [CompleteSpace F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    Continuous (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · change Continuous (fun v => BilinearFourierCoordinates.Construction.finiteBilinearContinuous (StandardTransvections.Construction.standardSymplecticBilinear F d)
      (D.symm.toContinuousLinearEquiv v) v / (2 : F))
    fun_prop

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable [IsUltrametricDist F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
variable (hn : ∃ x : F, ψ x ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
variable (g : FrameTransport.Construction.StandardSymplectic F d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
variable (hD : ∀ x, D x = g.val x - x)

def ultraCayleySynthesis (u f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d :=
  ⟨WeylSynthesisAdd.Construction.weylSynthesis ψ ν (WeakCayleyTestCoefficients.Construction.cayleyTestCoefficient hF ψ hc hu ν D f u) u.val,
    WeylSynthesisAdd.Construction.weylSynthesis_mem_ultra hF ψ hc ν _
      (WeakCayleyTestCoefficients.Construction.cayleyTestCoefficient_compact_locallyConstant hF ψ hc hu hn ν g D hD f u).1
      (WeakCayleyTestCoefficients.Construction.cayleyTestCoefficient_compact_locallyConstant hF ψ hc hu hn ν g D hD f u).2 u⟩

theorem ultraCayleySynthesis_pairing (u f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪Weak.Construction.testToL2 F d h, Weak.Construction.testToL2 F d (ultraCayleySynthesis hF ψ hc hu hn ν g D hD u f)⟫_ℂ =
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν
        (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D)
        f.val (WeylResolutionOperator.Construction.ultraResolutionLinearMap hF ψ hc hu hn ν u h).val := by
  let q := CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D
  have hq : Continuous q := standardCayleyWeylPhase_continuous hF D
  obtain ⟨hbl, hbs⟩ := WeakCayleyTestCoefficients.Construction.cayleyTestCoefficient_compact_locallyConstant hF ψ hc hu hn ν g D hD f u
  have hweak := WeakWeylSynthesis.Construction.weakWeylGaussian_synthesized_output hF ψ hc hu hn ν q hq
    (WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure F d) u.val h.val)
    (WeylResolutionOperator.Construction.weylAnalysis_locallyConstant hF ψ hc u h).continuous
    (WeylResolutionOperator.Construction.weylAnalysis_compactSupport hF ψ hn u h) f u
    (WeylResolutionOperator.Construction.ultraResolutionLinearMap hF ψ hc hu hn ν u h) rfl
  rw [hweak, Weak.Construction.testToL2_inner]
  change (∫ x, WeylSynthesisAdd.Construction.weylSynthesis ψ ν (WeakCayleyTestCoefficients.Construction.cayleyTestCoefficient hF ψ hc hu ν D f u) u.val x *
    conj (h.val x) ∂ Weak.Construction.referencePositionMeasure F d) = _
  rw [WeylSynthesis.Construction.weylSynthesis_pairing ψ hc hu (Weak.Construction.referencePositionMeasure F d) ν _ hbl.continuous
    (hbl.continuous.integrable_of_hasCompactSupport hbs)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    dsimp only [WeylAnalysis.Construction.weylAnalysis, WeakCayleyTestCoefficients.Construction.cayleyTestCoefficient]
    rw [starRingEnd_self_apply]
    ring

theorem ultraCayleySynthesis_normalized_pairing
    (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (r : ℝ) (hr : r ≠ 0)
    (hres : ∀ h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d,
      WeylResolutionOperator.Construction.ultraResolutionLinearMap hF ψ hc hu hn ν u h = (r : ℂ) • h)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪Weak.Construction.testToL2 F d h, Weak.Construction.testToL2 F d
      ((r : ℂ)⁻¹ • ultraCayleySynthesis hF ψ hc hu hn ν g D hD u f)⟫_ℂ =
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν
        (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D) f.val h.val := by
  rw [map_smul, inner_smul_right, ultraCayleySynthesis_pairing, hres,
    WeakGaussianLinearity.Construction.weakWeylGaussian_smul_right hF ψ hc hu, Complex.conj_ofReal,
    ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hr), one_mul]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CayleySynthesisPairing.Construction
