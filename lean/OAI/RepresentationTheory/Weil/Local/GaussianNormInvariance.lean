import OAI.RepresentationTheory.Weil.Local.FresnelChangeCoordinates
import OAI.RepresentationTheory.Weil.Local.QuadraticNormReflection
import OAI.RepresentationTheory.Weil.Local.QuadraticNormSubgroup

/-! # Gaussian Norm Invariance -/

namespace OAI.RepresentationTheory.Weil.Local.GaussianNormInvariance.Construction

noncomputable section

/-! Squared actual Gaussian indices are invariant under multiplication by a quadratic norm. -/

open _root_.Matrix

theorem phase_diagonalGaussianCoefficient_pair
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k ℂ) (a : kˣ) (ha : FunctionsMetaplectic.Construction.gaussianIntegral k ψ a.val ≠ 0) :
    FunctionsMetaplectic.Construction.phase (DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ (fun _ : Fin 2 => a)) = FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2 := by
  have he : DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ (fun _ : Fin 2 => a) =
      Complex.ofReal (((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k a))⁻¹) ^ 2) * FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2 := by
    simp only [DiagonalQuadratic.Construction.diagonalGaussianCoefficient, Fin.prod_univ_two]
    push_cast
    ring
  rw [he, Gaussian.Construction.phase_positive_mul _ (sq_pos_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (FunctionsMetaplectic.Construction.localModulus_pos k a))))]
  rw [FunctionsMetaplectic.Construction.phase, norm_pow, FunctionsMetaplectic.Construction.gaussianIndex_norm k ψ a.val ha, one_pow, Complex.ofReal_one, div_one]

theorem nonarchimedean_gaussianIndex_sq_mul_norm
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (hn : ∃ t : k, ψ t ≠ 1) (a b : kˣ) (hb : b ∈ QuadraticNormSubgroup.Construction.quadraticNormSubgroup k) :
    FunctionsMetaplectic.Construction.gaussianIndex k ψ (a * b).val ^ 2 = FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2 := by
  obtain ⟨s, t, hst⟩ := hb
  have hN : s ^ 2 + t ^ 2 ≠ 0 := by rw [hst]; exact b.ne_zero
  let A := QuadraticNormReflection.Construction.quadraticNormGeneralLinear s t hN
  have hdiv : (a * b).val / (s ^ 2 + t ^ 2) = a.val := by
    rw [hst, Units.val_mul]
    field_simp
  have hinv : (a * b).val⁻¹ * (s ^ 2 + t ^ 2) = a.val⁻¹ := by
    rw [hst, Units.val_mul]
    field_simp
  have hq (x : FunctionsMetaplectic.Construction.Position k 2) :
      FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => (a * b).val) (A⁻¹.val *ᵥ x) =
        FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => a.val) x := by
    change FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => (a * b).val)
      ((QuadraticNormReflection.Construction.quadraticNormGeneralLinear s t hN)⁻¹.val *ᵥ x) = _
    rw [QuadraticNormReflection.Construction.quadratic_normGeneralLinear_inverse, hdiv]
  have hqi (x : FunctionsMetaplectic.Construction.Position k 2) :
      FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => (a * b).val⁻¹) (A.val *ᵥ x) =
        FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => a.val⁻¹) x := by
    change FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => (a * b).val⁻¹)
      (QuadraticNormReflection.Construction.quadraticNormReflection s t *ᵥ x) = _
    rw [QuadraticNormReflection.Construction.quadratic_normReflection, hinv]
  have hcoef := FresnelChangeCoordinates.Construction.nonarchimedean_diagonalGaussianCoefficient_congruence hnd ψ hu hc hn
    (fun _ : Fin 2 => a * b) (fun _ : Fin 2 => a) A (QuadraticNormReflection.Construction.quadraticNormReflection_isSymm s t) hq hqi
  have ha0 := (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hnd ψ hu hc hn a.val a.ne_zero).2
  have hab0 := (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hnd ψ hu hc hn (a * b).val (a * b).ne_zero).2
  have hp := congrArg FunctionsMetaplectic.Construction.phase hcoef
  rw [phase_diagonalGaussianCoefficient_pair ψ a ha0,
    Gaussian.Construction.phase_positive_mul _ (FunctionsMetaplectic.Construction.localModulus_pos k _), phase_diagonalGaussianCoefficient_pair ψ (a * b) hab0] at hp
  exact hp.symm

end

end OAI.RepresentationTheory.Weil.Local.GaussianNormInvariance.Construction
