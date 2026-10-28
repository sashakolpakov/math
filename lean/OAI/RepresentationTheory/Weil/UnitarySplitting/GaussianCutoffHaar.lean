import OAI.RepresentationTheory.Weil.UnitarySplitting.NormGaussianCutoffs
import OAI.RepresentationTheory.Weil.UnitarySplitting.DiagonalNormGaussian
import OAI.RepresentationTheory.Weil.UnitarySplitting.HaarScaling

/-! # Gaussian Cutoff Haar -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Weil.UnitarySplitting.GaussianCutoffHaar.Construction

/-! Quadratic norm Gaussians and their finite diagonal products have stable
cutoffs with the prescribed quadratic-character phase. -/

open _root_.MeasureTheory
open scoped BigOperators

variable {F : Type} [NormedField F] [LocallyCompactSpace F]
variable [MeasurableSpace F] [BorelSpace F]

def normGaussianValue (ω : Fˣ →ₜ* Circle) (Γ : ℂ) (a : Fˣ) : ℂ :=
  (ω a : ℂ) * Γ / (FieldModulus.Construction.fieldModulus F a : ℂ)

theorem normGaussianValue_phase (ω : Fˣ →ₜ* Circle) (Γ : ℂ) (a : Fˣ) :
    DiagonalNormGaussian.Construction.gaussianPhase (normGaussianValue ω Γ a) = (ω a : ℂ) * DiagonalNormGaussian.Construction.gaussianPhase Γ := by
  apply DiagonalNormGaussian.Construction.positive_weight_gaussian_phase (FieldModulus.Construction.fieldModulus F a : ℝ) (FieldModulus.Construction.fieldModulus_pos a) (ω a)
  change (FieldModulus.Construction.fieldModulus F a : ℂ) * ((ω a : ℂ) * Γ / (FieldModulus.Construction.fieldModulus F a : ℂ)) = _
  have hpos : 0 < (FieldModulus.Construction.fieldModulus F a : ℝ) := FieldModulus.Construction.fieldModulus_pos a
  field_simp [Complex.ofReal_ne_zero.mpr hpos.ne']

theorem normGaussianValue_ne_zero (ω : Fˣ →ₜ* Circle) (Γ : ℂ) (hΓ : Γ ≠ 0) (a : Fˣ) :
    normGaussianValue ω Γ a ≠ 0 := by
  have hpos : 0 < (FieldModulus.Construction.fieldModulus F a : ℝ) := FieldModulus.Construction.fieldModulus_pos a
  exact div_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) hΓ)
    (Complex.ofReal_ne_zero.mpr hpos.ne')

theorem ultra_norm_hasGaussianCutoffs
    {E : Type} [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace E]
    [FiniteDimensional F E] [CharZero F] [IsUltrametricDist F]
    [MeasurableSpace E] [BorelSpace E]
    (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
    (hEmbedding : Continuous (algebraMap F E))
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μF : Measure F) [μF.IsAddHaarMeasure] [μF.Regular]
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (hu : ∀ x : F, ‖ψ x‖ = 1) (hn : ∃ x : F, ψ x ≠ 1) :
    ∃ Γ : ℂ, Γ ≠ 0 ∧ ∀ a : Fˣ,
      GaussianCutoff.Construction.HasGaussianCutoffs μE ψ (fun x => (a : F) * Algebra.norm F x) (normGaussianValue ω Γ a) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · obtain ⟨Γ, hΓ, R, -, hformula⟩ := NormGaussianNonzero.Construction.ultra_norm_gaussian_formula hF hE hEmbedding hQuadratic
      σ hne ω hω μF μE ψ hc hu hn
    refine ⟨Γ, hΓ, fun a => NormGaussianCutoffs.Construction.norm_hasGaussianCutoffs_of_stable hF hEmbedding hQuadratic σ hne
      μE ψ a (normGaussianValue ω Γ a) R (fun r hr => ?_)⟩
    have hpos : 0 < (FieldModulus.Construction.fieldModulus F a : ℝ) := FieldModulus.Construction.fieldModulus_pos a
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hpos.ne')).mpr
    simpa only [mul_comm] using hformula r hr a

theorem diagonal_norm_hasGaussianCutoffs
    {E : Type} [NormedField E] [Algebra F E] [MeasurableSpace E]
    (μ : Measure E) [SigmaFinite μ] (ψ : AddChar F ℂ)
    (ω : Fˣ →ₜ* Circle) (Γ : ℂ)
    (hΓ : ∀ a : Fˣ, GaussianCutoff.Construction.HasGaussianCutoffs μ ψ (fun x => (a : F) * Algebra.norm F x)
      (normGaussianValue ω Γ a)) {d : ℕ} (a : Fin d → Fˣ) :
    GaussianCutoff.Construction.HasGaussianCutoffs (Measure.pi (fun _ : Fin d => μ)) ψ
      (fun x => ∑ i, (a i : F) * Algebra.norm F (x i)) (∏ i, normGaussianValue ω Γ (a i)) :=
  GaussianCutoff.Construction.HasGaussianCutoffs.finite_product μ ψ _ _ (fun i => hΓ (a i))

theorem diagonal_norm_gaussian_value_phase (ω : Fˣ →ₜ* Circle) (Γ : ℂ)
    {d : ℕ} (a : Fin d → Fˣ) :
    DiagonalNormGaussian.Construction.gaussianPhase (∏ i, normGaussianValue ω Γ (a i)) =
      (ω (∏ i, a i) : ℂ) * DiagonalNormGaussian.Construction.gaussianPhase Γ ^ d := by
  have hp (s : Finset (Fin d)) : DiagonalNormGaussian.Construction.gaussianPhase (∏ i ∈ s, normGaussianValue ω Γ (a i)) =
      ∏ i ∈ s, DiagonalNormGaussian.Construction.gaussianPhase (normGaussianValue ω Γ (a i)) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact DiagonalNormGaussian.Construction.gaussianPhase_positive 1 zero_lt_one
    | @insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, DiagonalNormGaussian.Construction.gaussianPhase_mul, ih]
  rw [hp]
  simp_rw [normGaussianValue_phase]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_prod]
  congr 1
  exact (map_prod Circle.coeHom _ _).symm

end RepresentationTheory.Weil.UnitarySplitting.GaussianCutoffHaar.Construction

namespace RepresentationTheory.Weil.UnitarySplitting

/-! Gaussian cutoff values scale positively with additive Haar measure. -/

open _root_.MeasureTheory
open scoped NNReal

theorem GaussianCutoff.Construction.HasGaussianCutoffs.smul_measure
    {F V : Type} [Field F] [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (μ : Measure V) (ψ : AddChar F ℂ) (q : V → F) (Γ : ℂ)
    (hΓ : GaussianCutoff.Construction.HasGaussianCutoffs μ ψ q Γ) (a : ℝ≥0) :
    GaussianCutoff.Construction.HasGaussianCutoffs (a • μ) ψ q ((a : ℂ) * Γ) := by
  intro K hK
  obtain ⟨D, hDc, hDo, hKD, hshift, hvalue⟩ := hΓ K hK
  refine ⟨D, hDc, hDo, hKD, hshift, ?_⟩
  rw [integral_smul_nnreal_measure, hvalue]
  rfl

theorem GaussianCutoffHaar.Construction.gaussianCutoffs_haar_comparison
    {F V : Type} [Field F] [AddCommGroup V] [TopologicalSpace V]
    [T2Space V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
    [MeasurableSpace V] [BorelSpace V]
    (μ ν : Measure V) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] [μ.Regular] [ν.Regular]
    (ψ : AddChar F ℂ) (q : V → F) (Γ : ℂ) (hΓ : GaussianCutoff.Construction.HasGaussianCutoffs μ ψ q Γ) :
    ∃ c : ℝ≥0, 0 < c ∧ GaussianCutoff.Construction.HasGaussianCutoffs ν ψ q ((c : ℂ) * Γ) := by
  let c := Measure.addHaarScalarFactor ν μ
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
  have hν : ν = c • μ := Measure.isAddLeftInvariant_eq_smul_of_regular ν μ
  exact ⟨c, hc, hν ▸ hΓ.smul_measure μ ψ q Γ c⟩

end RepresentationTheory.Weil.UnitarySplitting

end

end OAI
