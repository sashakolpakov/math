import OAI.Analysis.PDE.Dirichlet.AllMixed
import OAI.Analysis.PDE.Dirichlet.FullNormal

open Set Filter
open scoped Topology InnerProductSpace ComplexOrder MatrixOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem exists_compact_second_derivative_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C := by
  have hc : Continuous (fun x ↦ ‖fderiv ℝ (fderiv ℝ f) x‖) :=
    (((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous).norm
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc.continuousOn
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro x hx
  exact (hC (mem_image_of_mem _ hx)).trans (by linarith [le_max_left C 0])

/-- Full boundary second-derivative control from scalar barriers and the
mixed estimate. All remaining constants are obtained from fixed compact data. -/
theorem boundary_hessian_bound_from_mixed_of_fixed_bounds {n : ℕ}
    {r B₀ : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 2 r)
    (hB₀ : ContDiff ℝ 2 B₀)
    {K₀ Kᵣ : ℝ} (hK₀ : 0 < K₀) (hKᵣ : 0 < Kᵣ)
    (hD₀ : ∀ x, r x = 0 → ‖fderiv ℝ (fderiv ℝ B₀) x‖ ≤ K₀)
    (hDᵣ : ∀ x, r x = 0 → ‖fderiv ℝ (fderiv ℝ r) x‖ ≤ Kᵣ)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {b B r₀ M F : ℝ} (hb : 0 < b) (hbB : b ≤ B) (hr₀ : 0 < r₀) (hM : 0 ≤ M)
    (hbase : ∀ x, r x = 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hconvex : ∀ x, r x = 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 2 u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x ≤ 0 → B * r x ≤ u x ∧ u x ≤ b * r x) →
      (∀ x, r x = 0 → ∀ v, fderiv ℝ r x v = 0 →
        |fderiv ℝ (fderiv ℝ u) x (covectorNormal (fderiv ℝ r x)) v| ≤ M * ‖v‖) →
      (∀ x, r x = 0 →
        |OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)| ≤ F) →
      ∀ x, r x = 0 → ‖fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) x‖ ≤ C := by
  have hB : 0 ≤ B := hb.le.trans hbB
  obtain ⟨C, hC, hfull⟩ := full_hessian_bound_of_tangential_data n
    (K₀ + B * Kᵣ) (K₀ + M) (b * r₀) F
    (show 0 ≤ K₀ + B * Kᵣ by positivity) (show 0 ≤ K₀ + M by positivity)
    (mul_pos hb hr₀)
  refine ⟨C, hC, ?_⟩
  intro u hu huz hub hum hud x hx
  let ν := covectorNormal (fderiv ℝ r x)
  have hg := hreg x hx
  have hν : ‖ν‖ = 1 := covectorNormal_unit hg
  have hnormal : fderiv ℝ r x = ‖fderiv ℝ r x‖ • innerSL ℝ ν := covectorNormal_form hg
  have hzero : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0 :=
    Eventually.of_forall (fun y hy ↦ huz y (hy.trans hx))
  obtain ⟨a, hba, haB, hfactor⟩ := boundary_gradient_factor_of_barriers
    (hu.differentiable (by norm_num) x) (hr.differentiable (by norm_num) x)
    (huz x hx) hx hg hb.le hbB hub (Eventually.of_forall (fun _ hy ↦ hy.le))
  have htangent : ∀ v, ⟪ν, v⟫_ℝ = 0 → fderiv ℝ r x v = 0 := by
    intro v hv
    have he := congrArg (fun l : CoordinateSpace (n + 1) 4 →L[ℝ] ℝ ↦ l v) hnormal
    simpa only [smul_apply, innerSL_apply_apply, smul_eq_mul, hv, mul_zero] using he
  apply hfull _ x ν (hB₀.add hu).contDiffAt hν
  · intro v w hv hw
    have ht := boundary_tangent_hessian_bound hB₀ hr hu hg hzero hfactor
      (hb.le.trans hba) haB (htangent v hv) (htangent w hw)
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (add_le_add (hD₀ x hx) (mul_le_mul_of_nonneg_left (hDᵣ x hx) hB))
        (norm_nonneg v)) (norm_nonneg w))
  · intro v hv
    rw [second_fderiv_add hB₀ hu]
    simp only [add_apply]
    calc
      |fderiv ℝ (fderiv ℝ B₀) x ν v + fderiv ℝ (fderiv ℝ u) x ν v| ≤
          |fderiv ℝ (fderiv ℝ B₀) x ν v| + |fderiv ℝ (fderiv ℝ u) x ν v| := abs_add_le _ _
      _ ≤ K₀ * ‖v‖ + M * ‖v‖ := add_le_add
        ((bilinear_abs_le _ ν v).trans (by
          rw [hν, mul_one]
          exact mul_le_mul_of_nonneg_right (hD₀ x hx) (norm_nonneg v)))
        (hum x hx v (htangent v hv))
      _ = (K₀ + M) * ‖v‖ := (add_mul _ _ _).symm
  · intro z hz
    exact boundary_quaternionHessian_coercive hB₀ hr hu hg hzero hfactor hnormal
      hb.le hba hr₀.le (hbase x hx) (hconvex x hx) z hz
  · exact hud x hx

/-- Compact-sublevel version of the fixed-data boundary estimate. -/
theorem boundary_hessian_bound_from_mixed {n : ℕ}
    {r B₀ : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 2 r)
    (hB₀ : ContDiff ℝ 2 B₀) (hK : IsCompact {x | r x ≤ 0})
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {b B r₀ M F : ℝ} (hb : 0 < b) (hbB : b ≤ B) (hr₀ : 0 < r₀) (hM : 0 ≤ M)
    (hbase : ∀ x, r x = 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hconvex : ∀ x, r x = 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 2 u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x ≤ 0 → B * r x ≤ u x ∧ u x ≤ b * r x) →
      (∀ x, r x = 0 → ∀ v, fderiv ℝ r x v = 0 →
        |fderiv ℝ (fderiv ℝ u) x (covectorNormal (fderiv ℝ r x)) v| ≤ M * ‖v‖) →
      (∀ x, r x = 0 →
        |OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)| ≤ F) →
      ∀ x, r x = 0 → ‖fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) x‖ ≤ C := by
  have hS : IsCompact {x | r x = 0} := hK.of_isClosed_subset
    (isClosed_eq hr.continuous continuous_const) (fun _ hx ↦ le_of_eq hx)
  obtain ⟨K₀, hK₀, hD₀⟩ := exists_compact_second_derivative_bound hB₀ hS
  obtain ⟨Kᵣ, hKᵣ, hDᵣ⟩ := exists_compact_second_derivative_bound hr hS
  exact boundary_hessian_bound_from_mixed_of_fixed_bounds hr hB₀ hK₀ hKᵣ hD₀ hDᵣ
    hreg hb hbB hr₀ hM hbase hconvex

end OAI.Analysis.PDE.Dirichlet
