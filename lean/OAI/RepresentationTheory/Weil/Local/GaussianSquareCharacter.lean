import OAI.RepresentationTheory.Weil.Local.GaussianNormInvariance
import OAI.RepresentationTheory.Weil.Local.QuadraticNormIndex
import OAI.RepresentationTheory.Weil.Local.IndexTwoPhaseCharacter

/-! # Gaussian Square Character -/

namespace OAI.RepresentationTheory.Weil.Local.GaussianSquareCharacter.Construction

noncomputable section

/-! The normalized squared actual Gaussian index is a quadratic character at a nonsplit nonarchimedean place. -/

variable {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
  [MeasurableSpace k] [BorelSpace k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)

def nonarchimedeanGaussianSquaredUnit (a : kˣ) : ℂˣ :=
  Units.mk0 (FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2) (pow_ne_zero 2
    (FunctionsMetaplectic.Construction.phase_ne_zero (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hnd ψ hu hc hn a.val a.ne_zero).2))

theorem nonarchimedeanGaussianSquaredUnit_norm_mul (a b : kˣ) (hb : b ∈ QuadraticNormSubgroup.Construction.quadraticNormSubgroup k) :
    nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn (a * b) =
      nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn a := by
  apply Units.ext
  exact GaussianNormInvariance.Construction.nonarchimedean_gaussianIndex_sq_mul_norm hnd ψ hu hc hn a b hb

theorem nonarchimedeanGaussianSquaredUnit_neg (a : kˣ) :
    nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn ((-1) * a) =
      (nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn a)⁻¹ := by
  apply Units.ext
  rw [Units.val_inv_eq_inv_val]
  change FunctionsMetaplectic.Construction.gaussianIndex k ψ ((-1) * a).val ^ 2 = (FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2)⁻¹
  rw [Units.val_mul]
  change FunctionsMetaplectic.Construction.gaussianIndex k ψ ((-1) * a.val) ^ 2 = _
  rw [neg_one_mul, GaussianNonarchimedean.Construction.nonarchimedean_gaussianIndex_neg hnd ψ hu hc hn a.val a.ne_zero, inv_pow]

theorem nonarchimedeanGaussianSquaredUnit_fourth (a : kˣ) :
    nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn a ^ 4 = 1 := by
  apply Units.ext
  change (FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2) ^ 4 = 1
  rw [← pow_mul]
  exact GaussianNonarchimedean.Construction.nonarchimedean_gaussianIndex_eighth hnd ψ hu hc hn a.val a.ne_zero

def nonarchimedeanGaussianSquareCharacter [CompleteSpace k] (h : ¬ ∃ t : k, t ^ 2 = -1) :
    kˣ →* ℂˣ := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hnd
  exact IndexTwoPhaseCharacter.Construction.indexTwoPhaseCharacter (QuadraticNormSubgroup.Construction.quadraticNormSubgroup k) (QuadraticNormIndex.Construction.localField_quadraticNorm_index_two hnd h)
    (nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn) (-1)
    (nonarchimedeanGaussianSquaredUnit_norm_mul hnd ψ hu hc hn)
    (nonarchimedeanGaussianSquaredUnit_neg hnd ψ hu hc hn)
    (nonarchimedeanGaussianSquaredUnit_fourth hnd ψ hu hc hn)

theorem nonarchimedeanGaussianSquareCharacter_apply [CompleteSpace k]
    (h : ¬ ∃ t : k, t ^ 2 = -1) (a : kˣ) :
    (nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn h a).val =
      (FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) ^ 2 := by
  change FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2 / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ 2 = _
  rw [div_pow]

theorem nonarchimedeanGaussianSquareCharacter_square [CompleteSpace k]
    (h : ¬ ∃ t : k, t ^ 2 = -1) (a : kˣ) :
    nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn h a ^ 2 = 1 := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hnd
  exact IndexTwoPhaseCharacter.Construction.indexTwo_phase_ratio_square (QuadraticNormSubgroup.Construction.quadraticNormSubgroup k) (QuadraticNormIndex.Construction.localField_quadraticNorm_index_two hnd h)
    (nonarchimedeanGaussianSquaredUnit hnd ψ hu hc hn) (-1)
    (nonarchimedeanGaussianSquaredUnit_norm_mul hnd ψ hu hc hn)
    (nonarchimedeanGaussianSquaredUnit_neg hnd ψ hu hc hn)
    (nonarchimedeanGaussianSquaredUnit_fourth hnd ψ hu hc hn) a

include hnd hu hc hn in
theorem nonarchimedean_gaussianIndex_normalized_sq_mul [CompleteSpace k]
    (h : ¬ ∃ t : k, t ^ 2 = -1) (a b : kˣ) :
    (FunctionsMetaplectic.Construction.gaussianIndex k ψ (a * b).val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) ^ 2 =
      (FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) ^ 2 *
        (FunctionsMetaplectic.Construction.gaussianIndex k ψ b.val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) ^ 2 := by
  have hh := congrArg Units.val ((nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn h).map_mul a b)
  simpa only [Units.val_mul, nonarchimedeanGaussianSquareCharacter_apply] using hh

end

end OAI.RepresentationTheory.Weil.Local.GaussianSquareCharacter.Construction
