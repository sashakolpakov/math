import OAI.Analysis.PDE.Schauder.Calculus.Schauder.CompactLimit
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.LowerHolder

/-! The lower Hölder jet fields canonically associated to a global C²,α function. -/

noncomputable section
open Set
open scoped Topology BoundedContinuousFunction
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem gradient_holder_bound {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (u : GlobalC2Holder m α) (x y : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (globalC2Value u) x - fderiv ℝ (globalC2Value u) y‖ ≤
      (3 * ‖u‖) * (dist x y) ^ α := by
  have hu := contDiff_globalC2Value u
  have hb (z) : ‖fderiv ℝ (fderiv ℝ (globalC2Value u)) z‖ ≤ ‖u‖ := by
    rw [← globalHessianHolder_apply hα]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le _ _).trans (norm_globalHessianHolder_le hα u)
  have hl (x y) : ‖fderiv ℝ (globalC2Value u) x - fderiv ℝ (globalC2Value u) y‖ ≤ ‖u‖ * ‖x - y‖ :=
    (convex_univ : Convex ℝ (univ : Set (EuclideanSpace ℝ (Fin m)))).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero z)
      (fun z _ => hb z) (mem_univ y) (mem_univ x)
  have h := holder_of_bounded_lipschitz (fderiv ℝ (globalC2Value u)) hα hα1
    (norm_nonneg u) (norm_nonneg u) (norm_fderiv_globalC2Value_le u) hl x y
  convert h using 1 ; rw [dist_eq_norm] ; ring

def globalGradientHolder {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (u : GlobalC2Holder m α) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α := by
  let g : EuclideanSpace ℝ (Fin m) →ᵇ (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fderiv ℝ (globalC2Value u))
      ((contDiff_globalC2Value u).continuous_fderiv (by norm_num)) ‖u‖ (norm_fderiv_globalC2Value_le u)
  exact OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα g (gradient_holder_bound hα hα1 u)

@[simp] theorem globalGradientHolder_value {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (u : GlobalC2Holder m α) (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (globalGradientHolder hα hα1 u) x = fderiv ℝ (globalC2Value u) x := rfl

theorem norm_globalGradientHolder_le {m : ℕ} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (u : GlobalC2Holder m α) : ‖globalGradientHolder hα hα1 u‖ ≤ 3 * ‖u‖ := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα (by positivity)
  · intro x
    exact (norm_fderiv_globalC2Value_le u x).trans (by nlinarith only [norm_nonneg u])
  · exact gradient_holder_bound hα hα1 u

end OAI.Analysis.PDE.Schauder
