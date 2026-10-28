import OAI.Analysis.PDE.Dirichlet.BoundedGradient
import OAI.Analysis.PDE.Dirichlet.BoundedPeriodicMixed
import OAI.Analysis.PDE.Dirichlet.Periodic.Mixed
import OAI.Analysis.PDE.Dirichlet.Periodic.Domain
import OAI.Analysis.PDE.Dirichlet.Periodic.Barriers
import OAI.Analysis.PDE.Dirichlet.Boundary.C2

open Set Module
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem uniform_boundary_hessian_bound_bounded_density_lattice {n : ℕ}
    (e : CoordinateSpace (n + 1) 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 3 B₀)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {b B r₀ m U L : ℝ} (hm : 0 < m) (hU : 0 ≤ U) (hL : 0 ≤ L) (hb : 0 < b) (hbB : b ≤ B) (hr₀ : 0 < r₀)
    (hbase : ∀ x, r x = 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 1 F →
      (∀ x, r x ≤ 0 → m ≤ F x) → (∀ x, r x ≤ 0 → F x ≤ U) →
      (∀ x, r x ≤ 0 → ‖fderiv ℝ F x‖ ≤ L) →
      ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 3 u →
      LatticePeriodic e lat u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x ≤ 0 → B * r x ≤ u x ∧ u x ≤ b * r x) →
      (∀ x, r x < 0 →
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ x, r x = 0 → ‖fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) x‖ ≤ C := by
  have hn : 1 ≤ n + 1 := by omega
  have hr2 : ContDiff ℝ 2 r := hr.of_le (by norm_num)
  have hB2 : ContDiff ℝ 2 B₀ := hB₀.of_le (by norm_num)
  obtain ⟨G, hG, hgrad⟩ := uniform_gradient_bound_from_bounded_densities_lattice hn e lat hK hr2 hB₀
    hrper hBper hbounded hreg hb.le hbB hr₀ (fun x hx ↦ hconvex x hx.le) hm hU hL
  let κ := m / (2 * (U ^ 2 + 1))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hci : ∀ x ∈ interior {x | r x ≤ 0},
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef :=
    fun x hx ↦ hconvex x (interior_subset (s := {x | r x ≤ 0}) hx)
  obtain ⟨M, hM, hmixed⟩ := uniform_mixed_hessian_bound_bounded_density_lattice hn e lat hK hr hB₀
    hrper hbounded hreg hL hb.le hbB hG.le hκ hr₀ hci
  obtain ⟨D₀, hD₀, hBD⟩ := exists_lattice_second_derivative_bound e lat hK hr.continuous
    hrper hbounded hB2 hBper
  obtain ⟨Dᵣ, hDᵣ, hrD⟩ := exists_lattice_second_derivative_bound e lat hK hr.continuous
    hrper hbounded hr2 hrper
  obtain ⟨C, hC, hfull⟩ := boundary_hessian_bound_from_mixed_of_fixed_bounds hr2 hB2 hD₀ hDᵣ
    (fun x hx ↦ hBD x hx.le) (fun x hx ↦ hrD x hx.le) hreg hb hbB hr₀ hM.le hbase
    (fun x hx ↦ hconvex x hx.le) (F := U)
  refine ⟨C, hC, ?_⟩
  intro F hF hmin hFU hFL u hu huper huz hub hup hueq
  have hupi : ∀ x ∈ interior {x | r x ≤ 0},
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef :=
    fun x hx ↦ hup x (neg_of_mem_interior_regular_sublevel hreg hx)
  have hug := hgrad F hF hmin hFU hFL u hu huper huz hub hup (fun x hx ↦ hueq x hx.le)
  have hutr : ∀ x ∈ interior {x | r x ≤ 0},
      κ ≤ OAI.LinearAlgebra.Moore.mooreDifferential (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) 1 := by
    intro x hx
    have hxD : r x ≤ 0 := interior_subset (s := {x | r x ≤ 0}) hx
    have hupper : F x ≤ U := hFU x hxD
    have h := mooreDifferential_one_lower hn
      (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) (hupi x hx)
      (M := U)
      (by rw [hueq x hxD]; exact hupper)
    rw [hueq x hxD] at h
    exact (div_le_div_of_nonneg_right (hmin x hxD) (by positivity)).trans h
  apply hfull u (hu.of_le (by norm_num)) huz hub
    (hmixed F hF hFL u hu huper huz hub hug hupi hutr hueq)
  intro x hx
  rw [hueq x hx.le]
  rw [abs_of_pos (hm.trans_le (hmin x hx.le))]
  exact hFU x hx.le

end OAI.Analysis.PDE.Dirichlet
