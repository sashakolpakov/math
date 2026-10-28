import OAI.Analysis.PDE.Nonlinear.LinearDirectional

/-! C³ regularity from the actual linear elliptic equation and Hölder jets. -/

noncomputable section
open Set
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

local instance linearBootstrapFirstGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance linearBootstrapFirstSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance linearBootstrapHessianGroup (m : ℕ) : NormedAddCommGroup (OAI.Analysis.PDE.Schauder.EuclideanHessian m) := inferInstance
local instance linearBootstrapHessianSpace (m : ℕ) : NormedSpace ℝ (OAI.Analysis.PDE.Schauder.EuclideanHessian m) := inferInstance
local instance linearBootstrapMatrixDGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)))
local instance linearBootstrapMatrixDSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)))

theorem linear_C3On {m : ℕ} (hm : 3 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hA : ContDiff ℝ 1 (OAI.Analysis.Normed.Function.Holder.HolderMap.value A))
    (DA : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) α)
    (hDA : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value DA x = fderiv ℝ (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) x)
    (u f : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u) (hf : ContDiff ℝ 1 f)
    (V D : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (OAI.Analysis.PDE.Schauder.EuclideanHessian m) α)
    (hV : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x)
    (hD : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ f x)
    (hH : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) x)
    {Ω : Set (EuclideanSpace ℝ (Fin m))} (hΩ : IsOpen Ω)
    (hPDE : ∀ x ∈ Ω, OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u x = f x)
    (hPD : ∀ x ∈ Ω, (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x).PosDef) : ContDiffOn ℝ 3 u Ω := by
  change ContDiffOn ℝ ((2 : WithTop ℕ∞) + 1) u Ω
  apply contDiffOn_succ_of_fderiv_apply (hu.differentiable (by norm_num)).differentiableOn
    (by intro he; norm_num at he)
  intro v
  have hh : ContDiffOn ℝ 2 (fun x => fderiv ℝ u x v) Ω := by
    intro x hx
    exact (linear_directional_C2At hm hα hα1 A hA DA hDA u f hu hf V D H hV hD hH
      hΩ hPDE hPD v x hx).contDiffWithinAt
  apply hh.congr
  intro x hx
  rw [fderivWithin_of_isOpen hΩ hx]

end OAI.Analysis.PDE.Nonlinear
