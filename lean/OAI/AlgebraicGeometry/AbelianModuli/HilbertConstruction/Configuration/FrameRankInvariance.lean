import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.CoordinateChangeEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.EvaluationInvariance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.CokernelRelabeling
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Unit.RowLinearEquivalence

/-! # Frame Rank Invariance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.FrameRankInvariance

noncomputable section

/-! Common invertible projective-coordinate changes and independent
unit rescalings of rows preserve the actual flat-cokernel rank
condition. The homogeneous relation kernel transforms by the
explicit polynomial-degree substitution. -/
universe u v
variable {R : Type u} [CommRing R] {ι : Type v} {n : ℕ}
variable (w : ι → Fin (n + 1) → R) (d : ℕ)
variable (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) (s : ι → Rˣ)

theorem homogeneousConfigurationEvaluation_range_linearCoordinates :
    (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c => T (w c)) d).range =
      (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w d).range := by
  rw [Polynomial.CoordinateChangeEvaluation.homogeneousConfigurationEvaluation_linearCoordinates]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Polynomial.CoordinateChangeEvaluation.pointCoordinatePolynomialDegreeEquiv T d x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(Polynomial.CoordinateChangeEvaluation.pointCoordinatePolynomialDegreeEquiv T d).symm x, ?_⟩
    change Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w d
      (Polynomial.CoordinateChangeEvaluation.pointCoordinatePolynomialDegreeEquiv T d ((Polynomial.CoordinateChangeEvaluation.pointCoordinatePolynomialDegreeEquiv T d).symm x)) = _
    rw [LinearEquiv.apply_symm_apply]

theorem homogeneousConfigurationEvaluation_kernel_frameChange :
    (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c j => (s c : R) * T (w c) j) d).ker =
      (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w d).ker.comap (Polynomial.CoordinateChangeEvaluation.pointCoordinatePolynomialDegreeEquiv T d).toLinearMap := by
  rw [EvaluationInvariance.homogeneousConfigurationEvaluation_kernel_rowUnits,
    Polynomial.CoordinateChangeEvaluation.homogeneousConfigurationEvaluation_linearCoordinates, LinearMap.ker_comp]

def configurationEvaluationCokernelFrameEquiv :
    ((ι → R) ⧸ (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w d).range) ≃ₗ[R]
      ((ι → R) ⧸ (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c j => (s c : R) * T (w c) j) d).range) :=
  (Submodule.quotEquivOfEq _ _ (homogeneousConfigurationEvaluation_range_linearCoordinates w d T).symm).trans
    (CokernelRelabeling.linearCokernelCodomainEquiv (Unit.RowLinearEquivalence.unitRowLinearEquiv (fun c => (s c) ^ d))
      (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c => T (w c)) d)
      (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c j => (s c : R) * T (w c) j) d) (by
        apply LinearMap.ext
        intro p
        funext c
        exact (EvaluationInvariance.homogeneousConfigurationEvaluation_rowScale (fun c => T (w c)) (fun c => (s c : R)) p c).symm))

variable [Fintype ι] [DecidableEq ι]

def configurationMatrixCokernelFrameEquiv :
    ((ι → R) ⧸ (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix w d)).range) ≃ₗ[R]
      ((ι → R) ⧸ (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix (fun c j => (s c : R) * T (w c) j) d)).range) :=
  (Submodule.quotEquivOfEq _ _ (MonomialMatrix.configurationMonomialMatrix_range w)).trans
    ((configurationEvaluationCokernelFrameEquiv w d T s).trans
      (Submodule.quotEquivOfEq _ _
        (MonomialMatrix.configurationMonomialMatrix_range (fun c j => (s c : R) * T (w c) j)).symm))

theorem configurationMonomialMatrix_flatRank_frameChange_iff (k m : ℕ) :
    (Module.Flat R ((ι → R) ⧸
      (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix (fun c j => (s c : R) * T (w c) j) d)).range) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R)
        ((ι → R) ⧸ (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix (fun c j => (s c : R) * T (w c) j) d)).range) p + k = m) ↔
    (Module.Flat R ((ι → R) ⧸ (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix w d)).range) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R)
        ((ι → R) ⧸ (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix w d)).range) p + k = m) := by
  let E := configurationMatrixCokernelFrameEquiv w d T s
  have h := Module.rankAtStalk_eq_of_equiv E
  constructor
  · rintro ⟨hflat, hrank⟩
    let := hflat
    refine ⟨Module.Flat.of_linearEquiv E, fun p => ?_⟩
    rw [congrFun h p]
    exact hrank p
  · rintro ⟨hflat, hrank⟩
    let := hflat
    refine ⟨Module.Flat.of_linearEquiv E.symm, fun p => ?_⟩
    rw [← congrFun h p]
    exact hrank p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.FrameRankInvariance
