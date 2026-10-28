import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DifferenceEquation

/-! A uniformly bounded Hölder forcing for the differentiated equation. -/

noncomputable section
open Set
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Weak

local instance forcingFirstGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance forcingFirstSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance forcingHessianGroup (m : ℕ) : NormedAddCommGroup (EuclideanHessian m) := inferInstance
local instance forcingHessianSpace (m : ℕ) : NormedSpace ℝ (EuclideanHessian m) := inferInstance
local instance forcingFunctionalGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanHessian m →L[ℝ] ℝ) := inferInstance
local instance forcingFunctionalSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanHessian m →L[ℝ] ℝ) := inferInstance
local instance forcingMatrixGroup (m : ℕ) : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance forcingMatrixSpace (m : ℕ) : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))
local instance forcingMatrixDerivativeGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)) := inferInstance
local instance forcingMatrixDerivativeSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)) := inferInstance

def holderTranslation {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ} (hα : 0 ≤ α)
    (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (z : E) : OAI.Analysis.Normed.Function.Holder.HolderMap E F α :=
  holderIsometricPullback hα (fun x => x + z) (Isometry.of_dist_eq (fun _ _ => dist_add_right _ _ _)) f

@[simp] theorem holderTranslation_value {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ} (hα : 0 ≤ α)
    (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (z x : E) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderTranslation hα f z) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value f (x + z) := rfl

theorem norm_holderTranslation_le {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ} (hα : 0 ≤ α)
    (f : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (z : E) : ‖holderTranslation hα f z‖ ≤ ‖f‖ :=
  norm_holderIsometricPullback_le _ _ _ _

def differenceEquationForcing {m : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (B : EuclideanSpace ℝ (Fin m) → (Fin m → Fin m → ℝ)) (hB : ContDiff ℝ 1 B)
    (DB : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)) α)
    (hDB : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value DB x = fderiv ℝ B x)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 1 f)
    (Df : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (hDf : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value Df x = fderiv ℝ f x)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m) α)
    (v : EuclideanSpace ℝ (Fin m)) {h : ℝ} (hh : h ≠ 0) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α :=
  differenceHolder hα f hf Df hDf v hh +
    OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (matrixCoefficientField (differenceHolder hα B hB DB hDB v hh))
      (holderTranslation hα H (h • v))

theorem differenceEquationForcing_value {m : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (B : EuclideanSpace ℝ (Fin m) → (Fin m → Fin m → ℝ)) (hB : ContDiff ℝ 1 B)
    (DB : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)) α)
    (hDB : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value DB x = fderiv ℝ B x)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 1 f)
    (Df : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (hDf : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value Df x = fderiv ℝ f x)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m) α)
    (v : EuclideanSpace ℝ (Fin m)) {h : ℝ} (hh : h ≠ 0) (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (differenceEquationForcing hα B hB DB hDB f hf Df hDf H v hh) x =
      OAI.Analysis.PDE.Weak.differenceQuotient v h f x +
        matrixHessianFunctional (OAI.Analysis.PDE.Weak.differenceQuotient v h B x) (OAI.Analysis.Normed.Function.Holder.HolderMap.value H (x + h • v)) := rfl

theorem norm_matrix_forcing_of_bounds {m : ℕ} {α p q : ℝ} (hα : 0 ≤ α)
    (g : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (b : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ((Fin m → Fin m → ℝ)) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m) α)
    (z : EuclideanSpace ℝ (Fin m)) (hg : ‖g‖ ≤ p) (hb : ‖b‖ ≤ q) :
    ‖g + OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (matrixCoefficientField b) (holderTranslation hα H z)‖ ≤
      p + 2 * ((m : ℝ) * m) * q * ‖H‖ := by
  have hq : 0 ≤ q := (norm_nonneg b).trans hb
  have ha : ‖matrixCoefficientField b‖ ≤ ((m : ℝ) * m) * q :=
    (norm_matrixCoefficientField_le b).trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have ht : ‖holderTranslation hα H z‖ ≤ ‖H‖ := norm_holderTranslation_le hα H z
  have hp : ‖OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (matrixCoefficientField b) (holderTranslation hα H z)‖ ≤
      2 * ‖matrixCoefficientField b‖ * ‖holderTranslation hα H z‖ :=
    OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα (matrixCoefficientField b) (holderTranslation hα H z)
  have hp' : ‖OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (matrixCoefficientField b) (holderTranslation hα H z)‖ ≤
      2 * ((m : ℝ) * m) * q * ‖H‖ := by
    apply hp.trans
    calc
      _ ≤ (2 * (((m : ℝ) * m) * q)) * ‖H‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num)) ht (norm_nonneg _) (by positivity)
      _ = _ := by ring
  exact (norm_add_le _ _).trans (add_le_add hg hp')

theorem norm_differenceEquationForcing_le {m : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (B : EuclideanSpace ℝ (Fin m) → (Fin m → Fin m → ℝ)) (hB : ContDiff ℝ 1 B)
    (DB : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)) α)
    (hDB : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value DB x = fderiv ℝ B x)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 1 f)
    (Df : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (hDf : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value Df x = fderiv ℝ f x)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m) α)
    (v : EuclideanSpace ℝ (Fin m)) {h : ℝ} (hh : h ≠ 0) :
    ‖differenceEquationForcing hα B hB DB hDB f hf Df hDf H v hh‖ ≤
      (‖Df‖ + 2 * ((m : ℝ) * m) * ‖DB‖ * ‖H‖) * ‖v‖ := by
  have hg : ‖differenceHolder hα f hf Df hDf v hh‖ ≤ ‖Df‖ * ‖v‖ :=
    norm_differenceHolder_le hα f hf Df hDf v hh
  have hb : ‖differenceHolder hα B hB DB hDB v hh‖ ≤ ‖DB‖ * ‖v‖ :=
    norm_differenceHolder_le hα B hB DB hDB v hh
  have hbound := norm_matrix_forcing_of_bounds hα
    (differenceHolder hα f hf Df hDf v hh) (differenceHolder hα B hB DB hDB v hh) H (h • v)
    hg hb
  exact hbound.trans_eq (by ring)

end OAI.Analysis.PDE.Schauder
