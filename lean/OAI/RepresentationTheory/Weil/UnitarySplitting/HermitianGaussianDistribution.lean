import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianCutoffHaar
import OAI.RepresentationTheory.Weil.UnitarySplitting.MatrixUnitTopology
import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianDiscriminant

/-! # Hermitian Gaussian Distribution -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianDistribution.Construction

noncomputable section

/-! Every nondegenerate Hermitian trace Gaussian has stable cutoffs and
the quadratic-character phase prescribed by its determinant. -/

open _root_.MeasureTheory _root_.Matrix
open scoped BigOperators NNReal

theorem hermitian_hasGaussianCutoffs
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
    (hE : ¬ DiscreteTopology E) (hQuadratic : Module.finrank F E = 2)
    (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (ψ : AddChar F ℂ) (Γ : ℂ) (hΓ0 : Γ ≠ 0)
    (hΓ : ∀ a : Fˣ, GaussianCutoff.Construction.HasGaussianCutoffs μE ψ (fun x => (a : F) * Algebra.norm F x)
      (GaussianCutoffHaar.Construction.normGaussianValue ω Γ a))
    {d : ℕ} (μ : Measure (Fin d → E)) [μ.IsAddHaarMeasure] [μ.Regular]
    (A : Matrix (Fin d) (Fin d) E) (hA : DualPair.Construction.adjointMatrix σ A = A) (hdet : A.det ≠ 0)
    (b : Fˣ) (hb : algebraMap F E (b : F) = A.det) :
    ∃ Z : ℂ, Z ≠ 0 ∧ GaussianCutoff.Construction.HasGaussianCutoffs μ ψ (HermitianNormForms.Construction.hermitianTraceQuadratic σ A) Z ∧
      DiagonalNormGaussian.Construction.gaussianPhase Z = (ω b : ℂ) * DiagonalNormGaussian.Construction.gaussianPhase Γ ^ d := by
  let : SecondCountableTopology E := TestSpaceAnalysis.Construction.localField_secondCountable E hE
  obtain ⟨u, a₀, ha₀, hdiag₀⟩ := HermitianGaussianDiscriminant.Construction.hermitian_matrix_diagonal σ hQuadratic hne A hA hdet
  let a : Fin d → Fˣ := fun i => Units.mk0 (a₀ i) (ha₀ i)
  have hdiag : DualPair.Construction.adjointMatrix σ (u : Matrix (Fin d) (Fin d) E) * A *
      (u : Matrix (Fin d) (Fin d) E) = Matrix.diagonal (fun i => algebraMap F E (a i : F)) := hdiag₀
  let Q : (Fin d → E) → F := fun x => ∑ i, (a i : F) * Algebra.norm F (x i)
  let w := MatrixUnitTopology.Construction.matrixUnitContinuousAddEquiv u
  let e := w.symm
  have hform (x : Fin d → E) : HermitianNormForms.Construction.hermitianTraceQuadratic σ A (w x) = Q x := by
    change Algebra.trace F E (DualPair.Construction.sesquilinear σ A ((u : Matrix (Fin d) (Fin d) E) *ᵥ x)
      ((u : Matrix (Fin d) (Fin d) E) *ᵥ x)) / 2 = Q x
    rw [DualPair.Construction.sesquilinear_change, hdiag, HermitianNormForms.Construction.sesquilinear_diagonal_norm hQuadratic σ hne,
      Algebra.trace_algebraMap, hQuadratic]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    change (2 : F) * Q x / 2 = Q x
    ring
  let μD : Measure (Fin d → E) := Measure.pi (fun _ => μE)
  let ν : Measure (Fin d → E) := μ.map e
  let : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let : ν.Regular := Measure.Regular.map e.toHomeomorph
  have hprod := GaussianCutoffHaar.Construction.diagonal_norm_hasGaussianCutoffs μE ψ ω Γ hΓ a
  obtain ⟨c, hc, hcut⟩ := GaussianCutoffHaar.Construction.gaussianCutoffs_haar_comparison μD ν ψ Q
    (∏ i, GaussianCutoffHaar.Construction.normGaussianValue ω Γ (a i)) hprod
  have ht := hcut.transport e μ ψ Q ((c : ℂ) * ∏ i, GaussianCutoffHaar.Construction.normGaussianValue ω Γ (a i))
  have hQe : (fun x => Q (e x)) = HermitianNormForms.Construction.hermitianTraceQuadratic σ A := by
    funext x
    have hh := hform (e x)
    rw [show w (e x) = x from w.apply_symm_apply x] at hh
    exact hh.symm
  rw [hQe] at ht
  have hcR : 0 < (c : ℝ) := hc
  refine ⟨(c : ℂ) * ∏ i, GaussianCutoffHaar.Construction.normGaussianValue ω Γ (a i), ?_, ht, ?_⟩
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hcR.ne')
      (Finset.prod_ne_zero_iff.mpr (fun i _ => GaussianCutoffHaar.Construction.normGaussianValue_ne_zero ω Γ hΓ0 (a i)))
  · rw [DiagonalNormGaussian.Construction.gaussianPhase_mul, DiagonalNormGaussian.Construction.gaussianPhase_positive (c : ℝ) hcR, one_mul,
      GaussianCutoffHaar.Construction.diagonal_norm_gaussian_value_phase,
      HermitianGaussianDiscriminant.Construction.hermitianDiagonal_discriminant_character hQuadratic σ hne ω hω A u a b hb hdiag]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianDistribution.Construction
