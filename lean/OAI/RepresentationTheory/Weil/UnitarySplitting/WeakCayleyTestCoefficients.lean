import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakCayleyCoefficients
import OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierPairing

/-! # Weak Cayley Test Coefficients -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeakCayleyTestCoefficients.Construction

noncomputable section

/-! Coherent coefficients of the weak Cayley transform are actual compact
locally constant amplitudes, suitable for Weyl synthesis. -/

open _root_.MeasureTheory

def cayleyTestCoefficient
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) : ℂ :=
  WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν
    (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D)
    f.val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v h).val

theorem cayleyTestCoefficient_compact_locallyConstant
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [IsUltrametricDist F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1) (hn : ∃ x : F, ψ x ≠ 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic F d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (hD : ∀ x, D x = g.val x - x) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    IsLocallyConstant (cayleyTestCoefficient hF ψ hc hu ν D f h) ∧
      HasCompactSupport (cayleyTestCoefficient hF ψ hc hu ν D f h) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
    let B := StandardTransvections.Construction.standardSymplecticBilinear F d
    let q := CayleyCompositionPhase.Construction.cayleyWeylPhase B D
    let L := D.symm.toContinuousLinearEquiv
    have hqc : Continuous q := by
      change Continuous (fun v => BilinearFourierCoordinates.Construction.finiteBilinearContinuous B (L v) v / (2 : F))
      fun_prop
    let e : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃L[F] Local.FunctionsMetaplectic.Construction.Position F (d + d) :=
      ContinuousLinearEquiv.piCongrLeft F (fun _ : Fin (d + d) => F) finSumFinEquiv
    let φ : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ := fun x => ψ (q x) *
      WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val h.val x
    have hφl : IsLocallyConstant φ :=
      ((LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hc).comp_continuous hqc).mul
        (UltraWeylCoefficients.Construction.weylMatrixCoefficient_locallyConstant_ultra hF ψ hc (Weak.Construction.referencePositionMeasure F d) f h)
    have hφs : HasCompactSupport φ :=
      (WeylSynthesisAdd.Construction.weylMatrixCoefficient_compactSupport_ultra hF ψ hn (Weak.Construction.referencePositionMeasure F d) f h).mul_left
    obtain ⟨hTl, hTs⟩ := BilinearFourierPairing.Construction.bilinear_fourier_compact_locallyConstant hF e B
      (StandardTransvections.Construction.standardSymplecticBilinear_nondegenerate d) L ψ hc hn ν φ hφl hφs
    have heq : cayleyTestCoefficient hF ψ hc hu ν D f h =
        fun v => ψ (q v) * ∫ x, ψ (B (L v) x) * φ x ∂ν := by
      funext v
      exact WeakCayleyCoefficients.Construction.weakCayleyGaussian_output_coefficient hF ψ hc hu ν g D hD f h v
    rw [heq]
    exact ⟨((LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hc).comp_continuous hqc).mul hTl, hTs.mul_left⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeakCayleyTestCoefficients.Construction
