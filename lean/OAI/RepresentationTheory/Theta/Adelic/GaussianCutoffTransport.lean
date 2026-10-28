import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianCutoffHaar
import OAI.RepresentationTheory.Theta.Adelic.GaussianCutoffComparison

/-! # Gaussian Cutoff Transport -/

namespace OAI.RepresentationTheory.Theta.Adelic.GaussianCutoffTransport

noncomputable section

/-! Pushing stable cutoffs through actual additive coordinates and
removing the positive Haar factors from a diagonal Fresnel coefficient. -/

open scoped Classical

open _root_.MeasureTheory
open OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianCutoffHaar.Construction

theorem gaussianCutoffs_map
    {F V W : Type} [Field F] [AddCommGroup V] [AddCommGroup W]
    [TopologicalSpace V] [TopologicalSpace W] [T2Space V] [T2Space W]
    [MeasurableSpace V] [MeasurableSpace W] [BorelSpace V] [BorelSpace W]
    (e : V ≃ₜ+ W) (μ : Measure V) (ψ : AddChar F ℂ) (q : V → F) (Γ : ℂ)
    (hΓ : Weil.UnitarySplitting.GaussianCutoff.Construction.HasGaussianCutoffs μ ψ q Γ) :
    Weil.UnitarySplitting.GaussianCutoff.Construction.HasGaussianCutoffs (μ.map e) ψ (fun x => q (e.symm x)) Γ := by
  have hm : (μ.map e).map e.symm = μ := by
    rw [Measure.map_map (show Measurable e.symm from e.symm.continuous.measurable)
      (show Measurable e from e.continuous.measurable)]
    simp only [Function.comp_def, e.symm_apply_apply]
    change Measure.map id μ = μ
    exact Measure.map_id
  have hΓ' : Weil.UnitarySplitting.GaussianCutoff.Construction.HasGaussianCutoffs ((μ.map e).map e.symm) ψ q Γ := by rw [hm]; exact hΓ
  exact hΓ'.transport e.symm (μ.map e) ψ q Γ

theorem diagonal_coefficient_phase
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
    (hc : Continuous (fun x : k => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1)
    (hn : ∃ x : k, ψ x ≠ 1) {n : ℕ} (a : Fin n → kˣ) :
    Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase (Weil.Local.DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a) = ∏ i, Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val := by
  have hp (s : Finset (Fin n)) :
      Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase (∏ i ∈ s, Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val *
        ((Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (a i)))⁻¹ : ℂ)) =
        ∏ i ∈ s, Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase (Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val *
          ((Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (a i)))⁻¹ : ℂ)) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty, Complex.ofReal_one] using Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_positive 1 zero_lt_one
    | @insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_mul, ih]
  rw [Weil.Local.DiagonalQuadratic.Construction.diagonalGaussianCoefficient, hp]
  apply Finset.prod_congr rfl
  intro i _
  rw [Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_mul, ← Complex.ofReal_inv, Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_positive _
    (inv_pos.mpr (Real.sqrt_pos.mpr (Weil.Local.FunctionsMetaplectic.Construction.localModulus_pos k (a i)))), mul_one]
  unfold Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase
  rw [Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex_norm k ψ (a i).val
    (Weil.Local.GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hnd ψ hu hc hn (a i).val (a i).ne_zero).2,
    Complex.ofReal_one, div_one]

end

end OAI.RepresentationTheory.Theta.Adelic.GaussianCutoffTransport
