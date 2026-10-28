import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchNormRegularization
import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianDistribution

/-! # Hermitian Gaussian Regularization -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianRegularization.Construction

noncomputable section

/-! Hermitian diagonalization determines the phase of regularized Gaussians. -/

open _root_.MeasureTheory _root_.Matrix
open scoped BigOperators NNReal

theorem gaussianPhase_finset_prod {I : Type} (s : Finset I) (z : I → ℂ) :
    DiagonalNormGaussian.Construction.gaussianPhase (∏ i ∈ s, z i) = ∏ i ∈ s, DiagonalNormGaussian.Construction.gaussianPhase (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact DiagonalNormGaussian.Construction.gaussianPhase_positive 1 zero_lt_one
  | @insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, DiagonalNormGaussian.Construction.gaussianPhase_mul, ih]

theorem gaussianRegularization_haar_comparison
    {F V : Type} [Field F] [AddCommGroup V] [TopologicalSpace V]
    [T2Space V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
    [MeasurableSpace V] [BorelSpace V]
    (μ ν : Measure V) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] [μ.Regular] [ν.Regular]
    (ψ : AddChar F ℂ) (q : V → F) (Γ : ℂ) (hΓ : QuadraticGaussianRegularization.Construction.HasGaussianRegularization μ ψ q Γ) :
    ∃ c : ℝ≥0, 0 < c ∧ QuadraticGaussianRegularization.Construction.HasGaussianRegularization ν ψ q ((c : ℂ) * Γ) := by
  let c := Measure.addHaarScalarFactor ν μ
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
  have hν : ν = c • μ := Measure.isAddLeftInvariant_eq_smul_of_regular ν μ
  exact ⟨c, hc, hν ▸ hΓ.smul_measure c hc⟩

theorem hermitian_hasGaussianRegularization
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
    (hE : ¬ DiscreteTopology E) (hQuadratic : Module.finrank F E = 2)
    (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (ψ : AddChar F ℂ) (Γ : ℂ)
    (hΓ : ∀ a : Fˣ, ∃ Z : ℂ, Z ≠ 0 ∧
      QuadraticGaussianRegularization.Construction.HasGaussianRegularization μE ψ (fun x => (a : F) * Algebra.norm F x) Z ∧
      DiagonalNormGaussian.Construction.gaussianPhase Z = (ω a : ℂ) * DiagonalNormGaussian.Construction.gaussianPhase Γ)
    {d : ℕ} (μ : Measure (Fin d → E)) [μ.IsAddHaarMeasure] [μ.Regular]
    (A : Matrix (Fin d) (Fin d) E) (hA : DualPair.Construction.adjointMatrix σ A = A) (hdet : A.det ≠ 0)
    (b : Fˣ) (hb : algebraMap F E (b : F) = A.det) :
    ∃ Z : ℂ, Z ≠ 0 ∧ QuadraticGaussianRegularization.Construction.HasGaussianRegularization μ ψ (HermitianNormForms.Construction.hermitianTraceQuadratic σ A) Z ∧
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
  choose z hz0 hz hphase using fun i => hΓ (a i)
  have hprod := QuadraticGaussianRegularization.Construction.HasGaussianRegularization.finite_product μE ψ
    (fun i x => (a i : F) * Algebra.norm F x) z hz
  obtain ⟨c, hc, hreg⟩ := gaussianRegularization_haar_comparison μD ν ψ Q (∏ i, z i) hprod
  have ht := hreg.transport e μ ψ Q ((c : ℂ) * ∏ i, z i)
  have hQe : (fun x => Q (e x)) = HermitianNormForms.Construction.hermitianTraceQuadratic σ A := by
    funext x
    have hh := hform (e x)
    rw [show w (e x) = x from w.apply_symm_apply x] at hh
    exact hh.symm
  rw [hQe] at ht
  have hcR : 0 < (c : ℝ) := hc
  refine ⟨(c : ℂ) * ∏ i, z i, ?_, ht, ?_⟩
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hcR.ne')
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hz0 i))
  · rw [DiagonalNormGaussian.Construction.gaussianPhase_mul, DiagonalNormGaussian.Construction.gaussianPhase_positive (c : ℝ) hcR, one_mul, gaussianPhase_finset_prod]
    simp_rw [hphase]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hp : (∏ i, (ω (a i) : ℂ)) = (ω (∏ i, a i) : ℂ) := by
      rw [map_prod]
      exact (map_prod Circle.coeHom _ _).symm
    rw [hp, HermitianGaussianDiscriminant.Construction.hermitianDiagonal_discriminant_character hQuadratic σ hne ω hω A u a b hb hdiag]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianRegularization.Construction
