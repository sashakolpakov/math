import OAI.Analysis.PDE.Nonlinear.EllipticLimit
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DifferenceForcing

/-! One derivative of gain for a genuine linear elliptic equation with C¹,α data. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Weak

local instance linearDirectionalFirstGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance linearDirectionalFirstSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance linearDirectionalHessianGroup (m : ℕ) : NormedAddCommGroup (OAI.Analysis.PDE.Schauder.EuclideanHessian m) := inferInstance
local instance linearDirectionalHessianSpace (m : ℕ) : NormedSpace ℝ (OAI.Analysis.PDE.Schauder.EuclideanHessian m) := inferInstance
local instance linearDirectionalMatrixGroup (m : ℕ) : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance linearDirectionalMatrixSpace (m : ℕ) : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))
local instance linearDirectionalMatrixDGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)))
local instance linearDirectionalMatrixDSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)))

theorem linear_directional_C2At {m : ℕ} (hm : 3 ≤ m) {α : ℝ}
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
    (hPD : ∀ x ∈ Ω, (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x).PosDef)
    (v x₀ : EuclideanSpace ℝ (Fin m)) (hx₀ : x₀ ∈ Ω) :
    ContDiffAt ℝ 2 (fun x => fderiv ℝ u x v) x₀ := by
  classical
  let B := fun x => (1 : Matrix (Fin m) (Fin m) ℝ) - OAI.Analysis.Normed.Function.Holder.HolderMap.value A x
  have hB : ContDiff ℝ 1 B := contDiff_const.sub hA
  have hDB (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (-DA) x = fderiv ℝ B x := by
    change -OAI.Analysis.Normed.Function.Holder.HolderMap.value DA x = _
    rw [hDA x]
    exact ((hA.differentiable one_ne_zero x).hasFDerivAt.const_sub 1).fderiv.symm
  have hBA (x) : (1 : Matrix (Fin m) (Fin m) ℝ) - B x = OAI.Analysis.Normed.Function.Holder.HolderMap.value A x := sub_sub_cancel _ _
  obtain ⟨R, hR, hRΩ⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  let ρ := R / 2
  let δ := R / (2 * (‖v‖ + 1))
  have hρ : 0 < ρ := half_pos hR
  have hδ : 0 < δ := div_pos hR (by positivity)
  have hinside (x) (hx : x ∈ ball x₀ ρ) : x ∈ Ω :=
    hRΩ (ball_subset_ball (by dsimp only [ρ]; linarith only [hR]) hx)
  have hshift (h : ℝ) (hh : |h| < δ) (x) (hx : x ∈ ball x₀ ρ) : x + h • v ∈ Ω := by
    apply hRΩ
    have hdist : dist x x₀ < R / 2 := hx
    have hb : |h| * (‖v‖ + 1) < R / 2 := by
      have ht := mul_lt_mul_of_pos_right hh (show 0 < ‖v‖ + 1 by positivity)
      have he : δ * (‖v‖ + 1) = R / 2 := by dsimp only [δ]; field_simp
      rwa [he] at ht
    change dist (x + h • v) x₀ < R
    calc
      _ ≤ dist (x + h • v) x + dist x x₀ := dist_triangle _ _ _
      _ = |h| * ‖v‖ + dist x x₀ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      _ < R := by nlinarith only [hb, hdist, abs_nonneg h]
  let Uₕ (h : ℝ) := if hh : h = 0 then (0 : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    else OAI.Analysis.PDE.Schauder.differenceHolder hα.le u (hu.of_le (by norm_num)) V hV v hh
  let Vₕ (h : ℝ) := if hh : h = 0 then (0 : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    else OAI.Analysis.PDE.Schauder.differenceHolder hα.le (fderiv ℝ u) (hu.fderiv_right (m := 1) (by norm_num)) H hH v hh
  let Fₕ (h : ℝ) := if hh : h = 0 then (0 : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    else OAI.Analysis.PDE.Schauder.differenceEquationForcing hα.le B hB (-DA) hDB f hf D hD H v hh
  have hUv (h) (hh : h ≠ 0) (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (Uₕ h) x = OAI.Analysis.PDE.Weak.differenceQuotient v h u x := by
    simp only [Uₕ, dite_eq_right hh, OAI.Analysis.PDE.Schauder.differenceHolder_value]
  have hVv (h) (hh : h ≠ 0) (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (Vₕ h) x = fderiv ℝ (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x := by
    simp only [Vₕ, dite_eq_right hh, OAI.Analysis.PDE.Schauder.differenceHolder_value]
    exact (OAI.Analysis.PDE.Schauder.fderiv_differenceQuotient u (hu.differentiable (by norm_num)) v h x).symm
  apply elliptic_family_limit_C2 hm hα hα1 hρ hδ (norm_nonneg A) (fun _ => A)
    (fun _ => le_rfl) x₀ (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) (hPD x₀ hx₀) tendsto_const_nhds
    (fun h => OAI.Analysis.PDE.Weak.differenceQuotient v h u) (fun h _ _ => OAI.Analysis.PDE.Schauder.contDiff_differenceQuotient u hu v h)
    Uₕ Vₕ Fₕ (fun h hh _ => hUv h hh) (fun h hh _ => hVv h hh)
    (N₀ := ‖V‖ * ‖v‖) (N₁ := ‖H‖ * ‖v‖)
    (Nf := (‖D‖ + 2 * ((m : ℝ) * m) * ‖-DA‖ * ‖H‖) * ‖v‖)
  · intro h hh _
    simp only [Uₕ, dite_eq_right hh]
    exact OAI.Analysis.PDE.Schauder.norm_differenceHolder_le hα.le u _ V hV v hh
  · intro h hh _
    simp only [Vₕ, dite_eq_right hh]
    exact OAI.Analysis.PDE.Schauder.norm_differenceHolder_le hα.le (fderiv ℝ u) _ H hH v hh
  · intro h hh _
    simp only [Fₕ, dite_eq_right hh]
    exact OAI.Analysis.PDE.Schauder.norm_differenceEquationForcing_le hα.le B hB (-DA) hDB f hf D hD H v hh
  · intro h hh hd x hx
    exact hPD x (hinside x hx)
  · intro h hh hd x hx
    simp only [Fₕ, dite_eq_right hh]
    change OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x =
      OAI.Analysis.PDE.Weak.differenceQuotient v h f x + OAI.Analysis.PDE.Schauder.matrixHessianFunctional (OAI.Analysis.PDE.Weak.differenceQuotient v h B x)
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value H (x + h • v))
    rw [hH]
    have he₀ := hPDE x (hinside x hx)
    have he₁ := hPDE (x + h • v) (hshift h hd x hx)
    simpa only [hBA] using OAI.Analysis.PDE.Schauder.nondivergence_differenceQuotient B u f hu v h x
      (by simpa only [hBA] using he₀) (by simpa only [hBA] using he₁)
  · intro x
    exact OAI.Analysis.PDE.Schauder.tendsto_differenceQuotient u v x (hu.differentiable (by norm_num) x)

end OAI.Analysis.PDE.Nonlinear
