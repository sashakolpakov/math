import OAI.Analysis.PDE.Dirichlet.Boundary.C2
import OAI.Analysis.PDE.Dirichlet.DataGradient
import OAI.Analysis.PDE.Dirichlet.DataBarriers

open Set
open scoped Topology Matrix ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- A uniform full boundary C² estimate, derived from fixed data and scalar
barriers. Neither a gradient estimate nor a mixed/normal second-derivative
estimate is an input to this theorem. -/
theorem uniform_boundary_hessian_bound_from_barriers {n : ℕ}
    {r B₀ F : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 3 B₀) (hF : ContDiff ℝ 1 F)
    (hK : IsCompact {x | r x ≤ 0}) (hKne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hFpos : ∀ x, r x ≤ 0 → 0 < F x)
    {b B r₀ : ℝ} (hb : 0 < b) (hbB : b ≤ B) (hr₀ : 0 < r₀)
    (hbase : ∀ x, r x = 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 3 u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x ≤ 0 → B * r x ≤ u x ∧ u x ≤ b * r x) →
      (∀ x ∈ interior {x | r x ≤ 0},
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x ≤ 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ x, r x = 0 → ‖fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) x‖ ≤ C := by
  have hn : 1 ≤ n + 1 := by omega
  have hr2 : ContDiff ℝ 2 r := hr.of_le (by norm_num)
  have hB2 : ContDiff ℝ 2 B₀ := hB₀.of_le (by norm_num)
  have hci : ∀ x ∈ interior {x | r x ≤ 0},
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef :=
    fun x hx ↦ hconvex x (interior_subset (s := {x | r x ≤ 0}) hx)
  obtain ⟨G, hG, hgrad⟩ := uniform_gradient_bound_from_barriers hn hr2 hB₀ hF hK hKne
    hreg hFpos hb.le hbB hr₀ hci
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hKne hF.continuous.continuousOn
  obtain ⟨U, hU, hFU⟩ := exists_compact_norm_bound hF.continuous hK
  let κ := F y / (2 * (U ^ 2 + 1))
  have hκ : 0 < κ := div_pos (hFpos y hy) (by positivity)
  obtain ⟨M, hM, hmix⟩ := uniform_mixed_hessian_bound hn hr hB₀ hF hK hreg
    hb.le hbB hG.le hκ hr₀ hci
  obtain ⟨C, hC, hfull⟩ := boundary_hessian_bound_from_mixed hr2 hB2 hK hreg
    hb hbB hr₀ hM.le (F := U) hbase (fun x hx ↦ hconvex x hx.le)
  refine ⟨C, hC, ?_⟩
  intro u hu huz hub hup hueq
  have hgr := hgrad u hu huz hub hup
    (fun x hx ↦ hueq x (interior_subset (s := {x | r x ≤ 0}) hx))
  have htrace : ∀ x ∈ interior {x | r x ≤ 0},
      κ ≤ OAI.LinearAlgebra.Moore.mooreDifferential (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) 1 := by
    intro x hx
    have heq := hueq x (interior_subset (s := {x | r x ≤ 0}) hx)
    have hm : F y ≤ OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) := by
      rw [heq]
      exact hmin (interior_subset hx)
    have hmax : OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) ≤ U := by
      rw [heq]
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hFU x (interior_subset hx))
    exact (div_le_div_of_nonneg_right hm (by positivity)).trans
      (mooreDifferential_one_lower hn _ (hup x hx) hmax)
  apply hfull u (hu.of_le (by norm_num)) huz hub (hmix u hu huz hub hgr hup htrace hueq)
  intro x hx
  rw [hueq x hx.le]
  simpa only [Real.norm_eq_abs] using hFU x hx.le

/-- The complete data-only boundary C² a priori estimate on a compact regular
sublevel. Scalar barriers, C¹ control, the adapted mixed bound and the
determinant/cofactor pure-normal bound are all derived inside the proof. -/
theorem uniform_boundary_hessian_bound {n : ℕ}
    {r B₀ F : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 3 B₀) (hF : ContDiff ℝ 1 F)
    (hK : IsCompact {x | r x ≤ 0}) (hKne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hFpos : ∀ x, r x ≤ 0 → 0 < F x) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 3 u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x ∈ interior {x | r x ≤ 0},
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x ≤ 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ x, r x = 0 → ‖fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) x‖ ≤ C := by
  have hn : 1 ≤ n + 1 := by omega
  have hr2 : ContDiff ℝ 2 r := hr.of_le (by norm_num)
  have hB2 : ContDiff ℝ 2 B₀ := hB₀.of_le (by norm_num)
  have hR : ∀ x ∈ {x | r x ≤ 0}, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef := by
    intro x hx
    have hu : (OAI.LinearAlgebra.Moore.complexify (r₀ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosDef := by
      rw [OAI.LinearAlgebra.Moore.complexify_real_smul, OAI.LinearAlgebra.Moore.complexify_one]
      exact Matrix.PosDef.one.smul hr₀
    simpa only [← OAI.LinearAlgebra.Moore.complexify_add, sub_add_cancel] using
      Matrix.PosDef.posSemidef_add (hconvex x hx) hu
  have hbd : ∀ x ∈ {x | r x ≤ 0}, x ∉ interior {x | r x ≤ 0} → r x = 0 :=
    fun _ hx hxi ↦ sublevel_boundary_zero hr.continuous hx hxi
  obtain ⟨b, B, hb, hbB, hbar⟩ := uniform_dirichlet_solution_barriers hn hK hKne
    hB2 hr2 F hF.continuous hbase hR hdet hFpos hbd
  obtain ⟨C, hC, hbound⟩ := uniform_boundary_hessian_bound_from_barriers hr hB₀ hF hK hKne
    hreg hFpos hb hbB hr₀ (fun x hx ↦ hbase x hx.le) hconvex
  refine ⟨C, hC, ?_⟩
  intro u hu huz hup hueq
  apply hbound u hu huz
    (hbar u (hu.of_le (by norm_num)) hup
      (fun x hx ↦ hueq x (interior_subset (s := {x | r x ≤ 0}) hx))
      (fun x hx hxi ↦ huz x (hbd x hx hxi))) hup hueq

end OAI.Analysis.PDE.Dirichlet
