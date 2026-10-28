import OAI.Analysis.PDE.Dirichlet.Uniform.BoundaryC2
import OAI.Analysis.PDE.Dirichlet.LogData

open Set
open scoped Topology Matrix ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- Data-only global real-Hessian estimate on a compact regular sublevel.
The unknown appears only after the uniform constant has been chosen. -/
theorem uniform_hessian_bound {n : ℕ}
    {r B₀ F : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF : ContDiff ℝ 2 F)
    (hK : IsCompact {x | r x ≤ 0}) (hKne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hFpos : ∀ x, r x ≤ 0 → 0 < F x) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 4 u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x ∈ interior {x | r x ≤ 0},
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x ≤ 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) x‖ ≤ C := by
  have hn : 1 ≤ n + 1 := by omega
  obtain ⟨B, hB, hbnd⟩ := uniform_boundary_hessian_bound hr (hB₀.of_le (by norm_num))
    (hF.of_le (by norm_num)) hK hKne hreg hFpos hr₀ hbase hdet hconvex
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hKne hF.continuous.continuousOn
  have hm := hFpos y hy
  obtain ⟨M, hM, hFM⟩ := exists_compact_norm_bound hF.continuous hK
  obtain ⟨L, hL, hlog⟩ := exists_log_second_directional_bound hF hK hFpos
  obtain ⟨R, hR, hrR⟩ := exists_compact_norm_bound hr.continuous hK
  let c := (L * M) / (r₀ * (F y / (2 * (M ^ 2 + 1))))
  let d : ℝ := Fintype.card (Fin (n + 1) × Fin 4)
  let H := d ^ 2 * ((d + 2) * (B + c * R))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨B + H + 1, by positivity, ?_⟩
  intro u hu huz hup hueq x hx
  have hboundary := hbnd u (hu.of_le (by norm_num)) huz hup hueq
  have hbd : ∀ x ∈ {x | r x ≤ 0}, x ∉ interior {x | r x ≤ 0} → r x = 0 :=
    fun _ hx hxi ↦ sublevel_boundary_zero hr.continuous hx hxi
  by_cases hxi : x ∈ interior {x | r x ≤ 0}
  · have hest := quaternionic_hessian_norm_estimate hn hK (hB₀.add hu)
      (hr.of_le (by norm_num)) hup
      (fun z hz ↦ hueq z (interior_subset (s := {x | r x ≤ 0}) hz))
      hm hM.le hr₀ hL.le hB.le
      (fun z hz ↦ ⟨hmin (interior_subset hz), (le_abs_self _).trans
        (by simpa only [Real.norm_eq_abs] using hFM z (interior_subset hz))⟩)
      (fun z hz ↦ hconvex z (interior_subset (s := {x | r x ≤ 0}) hz))
      (fun v z hz ↦ hlog z (interior_subset hz) v)
      (by
        intro v z hz hzi
        rw [directionalDerivative_twice ((hB₀.add hu).of_le (by norm_num))]
        calc
          fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) z v v ≤
              |fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) z v v| := le_abs_self _
          _ ≤ ‖fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) z‖ * ‖v‖ * ‖v‖ := bilinear_abs_le _ _ _
          _ ≤ B * ‖v‖ * ‖v‖ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hboundary z (hbd z hz hzi)) (norm_nonneg v)) (norm_nonneg v)
          _ = B * ‖v‖ ^ 2 := by ring)
      hbd (fun _ hz ↦ hz) x hxi
    change ‖fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) x‖ ≤
      d ^ 2 * ((d + 2) * (B - c * r x)) at hest
    have hrx : -r x ≤ R := (neg_le_abs _).trans
      (by simpa only [Real.norm_eq_abs] using hrR x hx)
    have hinner : B - c * r x ≤ B + c * R := by
      nlinarith [mul_le_mul_of_nonneg_left hrx hc]
    have hHess : ‖fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) x‖ ≤ H :=
      hest.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinner (by positivity)) (sq_nonneg d))
    linarith
  · exact (hboundary x (hbd x hx hxi)).trans (by linarith)

end OAI.Analysis.PDE.Dirichlet
