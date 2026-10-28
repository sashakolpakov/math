import OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalGaussian
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization
import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianFormula

/-! # Norm Weil Comparison -/

namespace OAI.RepresentationTheory.Theta.Adelic.NormWeilComparison

noncomputable section

/-! Compare UnitarySplitting's actual norm-Gaussian constant with the two scalar
Gaussian phases used by AdelicSplitting, including the normalization by one half. -/

open _root_.MeasureTheory
open OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianFormula.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction
open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalGaussian OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter
open OAI.RepresentationTheory.Theta.Adelic.GaussianCutoffTransport OAI.RepresentationTheory.Theta.Adelic.GaussianCutoffComparison

variable {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [LocallyCompactSpace k]
variable [IsUltrametricDist k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
variable (d : k) (hd : d ≠ 0) (hns : ¬ IsSquare d) (hnd : ¬ DiscreteTopology k)
variable (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x))
variable (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1)

include hd hnd hc hu hn

theorem normGaussian_phase_of_cutoffs
    (μE : Measure (QuadraticLocalField.FieldModel k d hns)) [μE.IsAddHaarMeasure] [μE.Regular]
    (a : kˣ) (Γ : ℂ)
    (hΓ : Weil.UnitarySplitting.GaussianCutoff.Construction.HasGaussianCutoffs μE ψ (fun x => a.val * Algebra.norm k x) Γ) :
    Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Γ = Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (2 * a.val) * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-2 * d * a.val) := by
  let : SecondCountableTopology k := Weil.Local.FunctionsMetaplectic.Construction.localField_secondCountable k hnd
  let e := (QuadraticLocalField.coordinates k d hns).toContinuousAddEquiv
  let ν := μE.map e
  let : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μE
  let : ν.Regular := Measure.Regular.map e.toHomeomorph
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    Weil.Local.NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hnd ψ hu hc hn
  let μ := Weil.Local.FunctionsMetaplectic.Construction.positionMeasure k 2 ψ
  let : μ.IsAddHaarMeasure := by dsimp [μ, Weil.Local.FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).Regular := by
    dsimp [Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure]
    exact Measure.Regular.smul ENNReal.ofReal_ne_top
  let : μ.Regular := by dsimp [μ, Weil.Local.FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  have ht := GaussianCutoffTransport.gaussianCutoffs_map e μE ψ (fun x => a.val * Algebra.norm k x) Γ hΓ
  have hform : (fun x : Weil.Local.FunctionsMetaplectic.Construction.Position k 2 => a.val * Algebra.norm k (e.symm x)) =
      Weil.Local.FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal fun i => (QuadraticLocalGaussian.normCoefficients d hd a i).val) := by
    funext x
    rw [QuadraticLocalGaussian.normCoefficients_quadratic]
    exact congrArg (fun z : k => a.val * z) (QuadraticLocalGaussian.model_norm_coordinates d hns x)
  rw [hform] at ht
  obtain ⟨c, hcp, hcΓ⟩ := Weil.UnitarySplitting.GaussianCutoffHaar.Construction.gaussianCutoffs_haar_comparison ν μ ψ _ Γ ht
  have he := GaussianCutoffComparison.diagonal_cutoff_coefficient hnd ψ hc hu hn (QuadraticLocalGaussian.normCoefficients d hd a) ((c : ℂ) * Γ) hcΓ
  have hphase := congrArg Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase he
  rw [Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_mul, Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_positive (c : ℝ) hcp, one_mul,
    GaussianCutoffTransport.diagonal_coefficient_phase hnd ψ hc hu hn] at hphase
  simpa only [Fin.prod_univ_two, QuadraticLocalGaussian.normCoefficients, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Units.val_mk0] using hphase

theorem normWeilConstant_eq
    (μE : Measure (QuadraticLocalField.FieldModel k d hns)) [μE.IsAddHaarMeasure] [μE.Regular]
    (Γ : ℂ) (hΓ0 : Γ ≠ 0)
    (hΓ : ∀ a : kˣ, Weil.UnitarySplitting.GaussianCutoff.Construction.HasGaussianCutoffs μE ψ (fun x => a.val * Algebra.norm k x)
      (Weil.UnitarySplitting.GaussianCutoffHaar.Construction.normGaussianValue (QuadraticNormCharacter.nonarchimedeanNormCharacter d hd hnd) Γ a)) :
    (Weil.UnitarySplitting.GaussianFormula.Construction.normWeilConstant (QuadraticNormCharacter.nonarchimedeanNormCharacter d hd hnd) Γ hΓ0 : ℂ) =
      Weil.AdelicSplitting.Normalization.Construction.quadraticWeilConstant k ψ d := by
  let a : kˣ := Units.mk0 (1 / 2 : k) (one_div_ne_zero two_ne_zero)
  have he := normGaussian_phase_of_cutoffs d hd hns hnd ψ hc hu hn μE a _ (hΓ a)
  rw [Weil.UnitarySplitting.GaussianCutoffHaar.Construction.normGaussianValue_phase] at he
  have htwo : (2 : k) * a.val = 1 := by dsimp [a]; field_simp
  have hneg : -2 * d * a.val = -d := by dsimp [a]; field_simp
  rw [htwo, hneg] at he
  exact he

end

end OAI.RepresentationTheory.Theta.Adelic.NormWeilComparison
