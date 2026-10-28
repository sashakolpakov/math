import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ConfigurationEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Evaluation

/-! # Evaluation Invariance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.EvaluationInvariance

noncomputable section

/-! The homogeneous evaluation kernel is unchanged by rescaling each
configuration row by a unit or by permuting its labels. These are exact
kernel identities over arbitrary, including nonreduced, rings. -/
universe u v w
variable {R : Type u} [CommRing R] {n d : ℕ} {ι : Type v} {κ : Type w}

theorem homogeneousConfigurationEvaluation_rowScale
    (v : ι → Fin (n + 1) → R) (a : ι → R) (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) (c : ι) :
    Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c j => a c * v c j) d p c =
      (a c) ^ d * Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation v d p c := by
  change MvPolynomial.eval₂Hom (algebraMap R R) (fun j => a c * v c j) p.val =
    (a c) ^ d * MvPolynomial.eval₂Hom (algebraMap R R) (v c) p.val
  exact Homogeneous.Evaluation.homogeneousEvaluation_scale (algebraMap R R) (v c) (a c) p.val d p.property

theorem homogeneousConfigurationEvaluation_kernel_rowUnits
    (v : ι → Fin (n + 1) → R) (a : ι → Rˣ) :
    (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c j => (a c : R) * v c j) d).ker =
      (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation v d).ker := by
  ext p
  change Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c j => (a c : R) * v c j) d p = 0 ↔
    Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation v d p = 0
  constructor
  · intro hp
    funext c
    have hc := congrFun hp c
    rw [homogeneousConfigurationEvaluation_rowScale] at hc
    apply ((a c).isUnit.pow d).mul_left_cancel
    simpa only [Pi.zero_apply, mul_zero] using hc
  · intro hp
    funext c
    rw [homogeneousConfigurationEvaluation_rowScale, congrFun hp c, Pi.zero_apply, mul_zero]

theorem homogeneousConfigurationEvaluation_kernel_relabel
    (v : ι → Fin (n + 1) → R) (e : κ ≃ ι) :
    (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c => v (e c)) d).ker =
      (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation v d).ker := by
  ext p
  change Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c => v (e c)) d p = 0 ↔
    Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation v d p = 0
  constructor
  · intro hp
    funext c
    have h := congrFun hp (e.symm c)
    change Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation v d p (e (e.symm c)) = 0 at h
    simpa only [e.apply_symm_apply, Pi.zero_apply] using h
  · intro hp
    funext c
    exact congrFun hp (e c)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.EvaluationInvariance
