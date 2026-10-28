import OAI.Analysis.PDE.Dirichlet.CoerciveData
import OAI.Analysis.PDE.Dirichlet.Boundary.Gradient

open Set Filter
open scoped Topology Matrix ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem exists_compact_norm_bound {X V : Type*} [TopologicalSpace X]
    [SeminormedAddCommGroup V] {f : X → V} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hf.norm.continuousOn
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro x hx
  exact (hC (mem_image_of_mem _ hx)).trans (by linarith [le_max_left C 0])

theorem sublevel_boundary_zero {X : Type*} [TopologicalSpace X]
    {r : X → ℝ} (hr : Continuous r) {x : X} (hx : r x ≤ 0)
    (hxi : x ∉ interior {y | r y ≤ 0}) : r x = 0 := by
  by_contra hn
  have hlt : r x < 0 := lt_of_le_of_ne hx hn
  apply hxi
  apply mem_interior.mpr
  refine ⟨{y | r y < 0}, fun y (hy : r y < 0) ↦ hy.le, ?_, hlt⟩
  exact isOpen_lt hr continuous_const

/-- The gradient constant is chosen before the solution: it depends only on
the fixed data and scalar barrier constants. -/
theorem uniform_gradient_bound_from_barriers {n : ℕ} (hn : 1 ≤ n)
    {r B₀ F : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 2 r)
    (hB₀ : ContDiff ℝ 3 B₀) (hF : ContDiff ℝ 1 F)
    (hK : IsCompact {x | r x ≤ 0}) (hKne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hFpos : ∀ x, r x ≤ 0 → 0 < F x)
    {b B r₀ : ℝ} (hb : 0 ≤ b) (hbB : b ≤ B) (hr₀ : 0 < r₀)
    (hconvex : ∀ x ∈ interior {x | r x ≤ 0},
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin n) (Fin n) OAI.Analysis.Calculus.Quaternion.Q))).PosSemidef) :
    ∃ G : ℝ, 0 < G ∧ ∀ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ 3 u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x ≤ 0 → B * r x ≤ u x ∧ u x ≤ b * r x) →
      (∀ x ∈ interior {x | r x ≤ 0},
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x ∈ interior {x | r x ≤ 0},
        OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ x, r x ≤ 0 → ‖fderiv ℝ u x‖ ≤ G := by
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hKne hF.continuous.continuousOn
  have hm := hFpos y hy
  obtain ⟨U, hU, hFU⟩ := exists_compact_norm_bound hF.continuous hK
  obtain ⟨L, hL, hFL⟩ := exists_compact_norm_bound
    (hF.fderiv_right (m := 0) (by norm_num)).continuous hK
  obtain ⟨D₀, hD₀, hBD⟩ := exists_compact_norm_bound
    (hB₀.fderiv_right (m := 0) (by norm_num)).continuous hK
  obtain ⟨Dᵣ, hDᵣ, hrD⟩ := exists_compact_norm_bound
    (hr.fderiv_right (m := 0) (by norm_num)).continuous hK
  obtain ⟨R, hR, hrR⟩ := exists_compact_norm_bound hr.continuous hK
  let A := D₀ + B * Dᵣ
  let c := L / (r₀ * (F y / (2 * (U ^ 2 + 1))))
  have hB : 0 ≤ B := hb.trans hbB
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨A + c * R + D₀ + 1, by positivity, ?_⟩
  intro u hu huz hub hup hueq x hx
  have hbd : ∀ z ∈ {z | r z ≤ 0}, z ∉ interior {z | r z ≤ 0} → r z = 0 :=
    fun _ hz hzi ↦ sublevel_boundary_zero hr.continuous hz hzi
  have hgrad := quaternionic_gradient_norm_estimate hn hK (hB₀.add hu) hr
    (hF.differentiable (by norm_num)).differentiableOn hup hueq hm hr₀ hL.le hA
    (fun z hz ↦ ⟨hmin (interior_subset hz), (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using hFU z (interior_subset hz))⟩)
    hconvex (fun z hz ↦ hFL z (interior_subset hz))
    (by
      intro z hz hzi
      have hzr := hbd z hz hzi
      exact (boundary_gradient_norm_add_of_barriers
        (hB₀.differentiable (by norm_num) z) (hu.differentiable (by norm_num) z)
        (hr.differentiable (by norm_num) z) (huz z hzr) hzr (hreg z hzr)
        hb hbB hub (Eventually.of_forall (fun _ ht ↦ ht.le))).trans
          (add_le_add (hBD z hz) (mul_le_mul_of_nonneg_left (hrD z hz) hB))) hbd
    (fun _ hz ↦ hz) x hx
  change ‖fderiv ℝ (fun z ↦ B₀ z + u z) x‖ ≤ A - c * r x at hgrad
  have hrx : -r x ≤ R := (neg_le_abs _).trans (by simpa only [Real.norm_eq_abs] using hrR x hx)
  have hsplit : fderiv ℝ u x = fderiv ℝ (fun z ↦ B₀ z + u z) x - fderiv ℝ B₀ x := by
    change fderiv ℝ u x = fderiv ℝ (B₀ + u) x - fderiv ℝ B₀ x
    rw [fderiv_add (hB₀.differentiable (by norm_num) x) (hu.differentiable (by norm_num) x)]
    abel
  rw [hsplit]
  have hnorm := (norm_sub_le (fderiv ℝ (fun z ↦ B₀ z + u z) x) (fderiv ℝ B₀ x)).trans
    (add_le_add hgrad (hBD x hx))
  nlinarith [mul_le_mul_of_nonneg_left hrx hc]

end OAI.Analysis.PDE.Dirichlet
