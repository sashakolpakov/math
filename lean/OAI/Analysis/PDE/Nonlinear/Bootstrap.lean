import OAI.Analysis.PDE.Nonlinear.IndexedLimit
import OAI.Analysis.PDE.Nonlinear.MatrixFamily
import OAI.Analysis.PDE.Dirichlet.C2HolderQuaternion

/-! The actual Moore equation improves a C²,α potential by one derivative. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Weak

theorem moore_directional_C2At {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (hu : ContDiff ℝ 2 u) (hf : ContDiff ℝ 1 f)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) α)
    (hV : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x)
    (hH : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) x)
    (hD : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ f x)
    {Ω : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} (hΩ : IsOpen Ω)
    (hPDE : ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ x ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef)
    (v x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (hx₀ : x₀ ∈ Ω) :
    ContDiffAt ℝ 2 (fun x => fderiv ℝ u x v) x₀ := by
  classical
  let HQ := OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots) H
  have hHQ (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value HQ x = OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x := by
    change OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.HolderMap.value H x) = _
    rw [hH x]
    rfl
  obtain ⟨B, hB, ⟨M, hM, hBN⟩, hlim, hBPD, hBeq⟩ :=
    exists_moore_matrix_family hα u f hu HQ hHQ v
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
  let Uₕ (h : ℝ) := if hh : h = 0 then (0 : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) ℝ α)
    else OAI.Analysis.PDE.Schauder.differenceHolder hα.le u (hu.of_le (by norm_num)) V hV v hh
  let Vₕ (h : ℝ) := if hh : h = 0 then (0 : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) α)
    else OAI.Analysis.PDE.Schauder.differenceHolder hα.le (fderiv ℝ u) (hu.fderiv_right (m := 1) (by norm_num)) H hH v hh
  let Fₕ (h : ℝ) := if hh : h = 0 then (0 : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) ℝ α)
    else OAI.Analysis.PDE.Schauder.differenceHolder hα.le f hf D hD v hh
  have hUv (h) (hh : h ≠ 0) (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (Uₕ h) x = OAI.Analysis.PDE.Weak.differenceQuotient v h u x := by
    simp only [Uₕ, dite_eq_right hh, OAI.Analysis.PDE.Schauder.differenceHolder_value]
  have hVv (h) (hh : h ≠ 0) (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (Vₕ h) x = fderiv ℝ (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x := by
    simp only [Vₕ, dite_eq_right hh, OAI.Analysis.PDE.Schauder.differenceHolder_value]
    exact (OAI.Analysis.PDE.Schauder.fderiv_differenceQuotient u (hu.differentiable (by norm_num)) v h x).symm
  have hFv (h) (hh : h ≠ 0) (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (Fₕ h) x = OAI.Analysis.PDE.Weak.differenceQuotient v h f x := by
    simp only [Fₕ, dite_eq_right hh, OAI.Analysis.PDE.Schauder.differenceHolder_value]
  have hA₀ : (OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x₀))).PosDef := by
    simpa only [segmentOperator_self] using segmentOperator_coordinate_posDef
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x₀) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x₀) (hPD x₀ hx₀) (hPD x₀ hx₀)
  apply indexed_family_limit_C2 finProdFinEquiv hn hα hα1 hρ hδ hM B hBN x₀ _ hA₀ (hlim x₀)
    (fun h => OAI.Analysis.PDE.Weak.differenceQuotient v h u) (fun h _ _ => OAI.Analysis.PDE.Schauder.contDiff_differenceQuotient u hu v h)
    Uₕ Vₕ Fₕ (fun h hh _ => hUv h hh) (fun h hh _ => hVv h hh)
    (N₀ := ‖V‖ * ‖v‖) (N₁ := ‖H‖ * ‖v‖) (Nf := ‖D‖ * ‖v‖)
  · intro h hh _
    simp only [Uₕ, dite_eq_right hh]
    exact OAI.Analysis.PDE.Schauder.norm_differenceHolder_le hα.le u _ V hV v hh
  · intro h hh _
    simp only [Vₕ, dite_eq_right hh]
    exact OAI.Analysis.PDE.Schauder.norm_differenceHolder_le hα.le (fderiv ℝ u) _ H hH v hh
  · intro h hh _
    simp only [Fₕ, dite_eq_right hh]
    exact OAI.Analysis.PDE.Schauder.norm_differenceHolder_le hα.le f _ D hD v hh
  · intro h _ hd x hx
    exact hBPD h x (hPD x (hinside x hx)) (hPD _ (hshift h hd x hx))
  · intro h hh hd x hx
    rw [hFv h hh x]
    exact hBeq h x (hPDE x (hinside x hx)) (hPDE _ (hshift h hd x hx))
  · intro x
    exact OAI.Analysis.PDE.Schauder.tendsto_differenceQuotient u v x (hu.differentiable (by norm_num) x)

theorem moore_C3_of_C2_holder {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (hu : ContDiff ℝ 2 u) (hf : ContDiff ℝ 1 f)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) α)
    (hV : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x)
    (hH : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) x)
    (hD : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ f x)
    {Ω : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} (hΩ : IsOpen Ω)
    (hPDE : ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ x ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    ContDiffOn ℝ 3 u Ω := by
  change ContDiffOn ℝ ((2 : WithTop ℕ∞) + 1) u Ω
  apply contDiffOn_succ_of_fderiv_apply (hu.differentiable (by norm_num)).differentiableOn
    (by intro he; norm_num at he)
  intro v
  have hh : ContDiffOn ℝ 2 (fun x => fderiv ℝ u x v) Ω := by
    intro x hx
    exact (moore_directional_C2At hn hα hα1 u f hu hf V H D hV hH hD hΩ hPDE hPD v x hx).contDiffWithinAt
  apply hh.congr
  intro x hx
  rw [fderivWithin_of_isOpen hΩ hx]

end OAI.Analysis.PDE.Nonlinear
