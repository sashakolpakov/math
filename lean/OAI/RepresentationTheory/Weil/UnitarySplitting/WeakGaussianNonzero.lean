import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylConjugation
import OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierInjectivity

/-! # Weak Gaussian Nonzero -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianNonzero.Construction

noncomputable section

/-! The weak Gaussian transform is nonzero. Simultaneous Weyl shifts
test every symplectic Fourier frequency of a nonzero matrix coefficient. -/

open _root_.MeasureTheory _root_.Topology
open scoped InnerProductSpace

theorem weakWeylGaussian_nonzero_ultra
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [IsUltrametricDist F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1) (hn : ∃ x : F, ψ x ≠ 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → F) (hq : Continuous q) :
    ∃ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d,
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q f.val h.val ≠ 0 := by
  let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  let u := LocalTest.Construction.ultraTestVector F hF d
  have hu0 : u ≠ 0 := LocalTest.Construction.ultraTestVector_ne_zero F hF d
  let C := WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) u.val u.val
  let φ : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → ℂ := fun v => ψ (q v) * C v
  have hφc : Continuous φ := (hc.comp hq).mul
    (WeylMatrixCoefficients.Construction.weylMatrixCoefficient_continuous ψ hc hu (Weak.Construction.referencePositionMeasure F d) u u)
  have hφi : Integrable φ ν := WeakWeylGaussian.Construction.weakWeylGaussian_integrable_ultra hF ψ hc hn
    (Weak.Construction.referencePositionMeasure F d) ν q hq u u
  have hC0 : C 0 ≠ 0 := by
    have hρ0 : HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu 0 u = u := by
      apply Subtype.ext
      exact Heisenberg.Construction.heisenbergFunction_zero ψ u.val
    change WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) u.val u.val 0 ≠ 0
    rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu, hρ0, inner_self_eq_norm_sq_to_K]
    change (‖Weak.Construction.testToL2 F d u‖ : ℂ) ^ 2 ≠ 0
    apply pow_ne_zero
    apply Complex.ofReal_ne_zero.mpr
    apply norm_ne_zero_iff.mpr
    intro hz
    apply hu0
    apply Weak.Construction.testToL2_injective F d
    simpa only [map_zero] using hz
  have hφ0 : φ 0 ≠ 0 := by
    apply mul_ne_zero _ hC0
    intro hz
    have hh := hu (q 0)
    rw [hz, norm_zero] at hh
    exact zero_ne_one hh
  let e : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃L[F] Local.FunctionsMetaplectic.Construction.Position F (d + d) :=
    ContinuousLinearEquiv.piCongrLeft F (fun _ : Fin (d + d) => F) finSumFinEquiv
  obtain ⟨w, hw⟩ := BilinearFourierInjectivity.Construction.exists_bilinear_fourier_integral_ne_zero e (StandardTransvections.Construction.standardSymplecticBilinear F d)
    (StandardTransvections.Construction.standardSymplecticBilinear_nondegenerate d) ψ hc hu hn ν φ hφi hφc ⟨0, hφ0⟩
  refine ⟨HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w u, HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w u, ?_⟩
  have heq : WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure F d) ν q
      (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w u).val (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w u).val =
        ∫ v, ψ (StandardTransvections.Construction.standardSymplecticBilinear F d v w) * φ v ∂ν := by
    unfold WeakWeylGaussian.Construction.weakWeylGaussian
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      dsimp only
      rw [WeylConjugation.Construction.weylMatrixCoefficient_conjugation hF ψ hc hu]
      change ψ (q v) * (ψ (Oscillator.Construction.standardSymplecticPairing d v w) * C v) =
        ψ (Oscillator.Construction.standardSymplecticPairing d v w) * (ψ (q v) * C v)
      ring
  rw [heq]
  exact hw

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianNonzero.Construction
