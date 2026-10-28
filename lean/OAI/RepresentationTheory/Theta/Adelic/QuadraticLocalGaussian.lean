import OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalCharacter
import OAI.RepresentationTheory.Theta.Adelic.GaussianCutoffTransport

/-! # Quadratic Local Gaussian -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalGaussian

noncomputable section

/-! The phase of the actual quadratic norm Gaussian, computed both from
the norm character and from the diagonal LocalWeil Gaussian integrals. -/

open scoped Classical NNReal

open _root_.Matrix _root_.MeasureTheory
open OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter
open OAI.RepresentationTheory.Theta.Adelic.GaussianCutoffTransport OAI.RepresentationTheory.Theta.Adelic.GaussianCutoffComparison

def normCoefficients {k : Type} [Field k] [CharZero k] (d : k) (hd : d ≠ 0) (a : kˣ) : Fin 2 → kˣ :=
  ![Units.mk0 (2 * a.val) (mul_ne_zero (by norm_num) a.ne_zero),
    Units.mk0 (-2 * d * a.val) (mul_ne_zero (mul_ne_zero (by norm_num) hd) a.ne_zero)]

theorem normCoefficients_quadratic {k : Type} [Field k] [CharZero k]
    (d : k) (hd : d ≠ 0) (a : kˣ) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k 2) :
    Weil.Local.FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal fun i => (normCoefficients d hd a i).val) x =
      a.val * (x 0 ^ 2 - d * x 1 ^ 2) := by
  rw [Weil.Local.RealDiagonalFresnel.Construction.quadratic_diagonal, Fin.sum_univ_two]
  dsimp [normCoefficients]
  ring

variable {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [LocallyCompactSpace k]
variable [IsUltrametricDist k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
variable (d : k) (hd : d ≠ 0) (hns : ¬ IsSquare d) (hnd : ¬ DiscreteTopology k)
variable (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x))
variable (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1)

omit [LocallyCompactSpace k] [CharZero k] [MeasurableSpace k] [BorelSpace k] in
theorem model_norm_coordinates (x : Weil.Local.FunctionsMetaplectic.Construction.Position k 2) :
    Algebra.norm k ((QuadraticLocalField.coordinates k d hns).symm x) = x 0 ^ 2 - d * x 1 ^ 2 := by
  rw [QuadraticLocalField.model_norm, QuadraticNormChart.Compact.quadratic_norm]
  have he := QuadraticLocalField.coordinates_apply k d hns ((QuadraticLocalField.coordinates k d hns).symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  exact congrArg₂ (fun u v : k => u ^ 2 - d * v ^ 2) h0.symm h1.symm

include hd hns hnd hc hu hn

theorem exists_norm_gaussian_phase :
    ∃ Γ : ℂ, Γ ≠ 0 ∧ ∀ a : kˣ,
      (∏ i, Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (normCoefficients d hd a i).val) =
        (QuadraticNormCharacter.normSign d a : ℂ) * Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Γ := by
  let : SecondCountableTopology k := Weil.Local.FunctionsMetaplectic.Construction.localField_secondCountable k hnd
  let E := QuadraticLocalField.FieldModel k d hns
  let μF : Measure k := Measure.addHaar
  let μE : Measure E := Measure.addHaar
  let ω := QuadraticNormCharacter.nonarchimedeanNormCharacter d hd hnd
  obtain ⟨Γ, hΓ, hcut⟩ := Weil.UnitarySplitting.GaussianCutoffHaar.Construction.ultra_norm_hasGaussianCutoffs hnd (QuadraticLocalField.model_nondiscrete k d hns)
    (continuous_algebraMap k E) (QuadraticLocalField.model_finrank k d hns) (QuadraticLocalField.conjugation k d hns)
    (QuadraticLocalField.conjugation_nontrivial k d hns) ω (QuadraticLocalCharacter.model_quadratic_character d hd hns hnd)
    μF μE ψ hc hu hn
  let e := (QuadraticLocalField.coordinates k d hns).toContinuousAddEquiv
  let ν : Measure (Weil.Local.FunctionsMetaplectic.Construction.Position k 2) := μE.map e
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
  refine ⟨Γ, hΓ, fun a => ?_⟩
  have ht := GaussianCutoffTransport.gaussianCutoffs_map e μE ψ (fun x : E => a.val * Algebra.norm k x)
    (Weil.UnitarySplitting.GaussianCutoffHaar.Construction.normGaussianValue ω Γ a) (hcut a)
  have hform : (fun x : Weil.Local.FunctionsMetaplectic.Construction.Position k 2 => a.val * Algebra.norm k (e.symm x)) =
      Weil.Local.FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal fun i => (normCoefficients d hd a i).val) := by
    funext x
    rw [normCoefficients_quadratic]
    exact congrArg (fun z : k => a.val * z) (model_norm_coordinates d hns x)
  rw [hform] at ht
  obtain ⟨c, hcp, hcΓ⟩ := Weil.UnitarySplitting.GaussianCutoffHaar.Construction.gaussianCutoffs_haar_comparison ν μ ψ _ (Weil.UnitarySplitting.GaussianCutoffHaar.Construction.normGaussianValue ω Γ a) ht
  have he := GaussianCutoffComparison.diagonal_cutoff_coefficient hnd ψ hc hu hn (normCoefficients d hd a)
    ((c : ℂ) * Weil.UnitarySplitting.GaussianCutoffHaar.Construction.normGaussianValue ω Γ a) hcΓ
  have hphase := congrArg Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase he
  rw [Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_mul, Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_positive (c : ℝ) hcp, one_mul,
    Weil.UnitarySplitting.GaussianCutoffHaar.Construction.normGaussianValue_phase, GaussianCutoffTransport.diagonal_coefficient_phase hnd ψ hc hu hn] at hphase
  exact hphase.symm

theorem norm_character_gaussian_identity (a : kˣ) :
    (QuadraticNormCharacter.normSign d a : ℂ) *
        (Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 2 * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-2 * d)) =
      Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (2 * a.val) * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-2 * d * a.val) := by
  obtain ⟨Γ, _, hΓ⟩ := exists_norm_gaussian_phase d hd hns hnd ψ hc hu hn
  have h1 : (∏ i, Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (normCoefficients d hd 1 i).val) = Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Γ := by
    simpa only [QuadraticNormCharacter.normSign_one, Circle.coe_one, one_mul] using hΓ 1
  have ha := hΓ a
  rw [← h1] at ha
  simpa [normCoefficients, Fin.prod_univ_two] using ha.symm

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalGaussian
