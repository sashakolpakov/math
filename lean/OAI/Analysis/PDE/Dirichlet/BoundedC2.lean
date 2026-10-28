import OAI.Analysis.PDE.Dirichlet.BoundedBoundaryC2
import OAI.Analysis.PDE.Dirichlet.BoundedBarriers
import OAI.Analysis.PDE.Dirichlet.Periodic.LogData

open Set Module
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Global data-only real-Hessian estimate for periodic solutions. The
compactness assumption concerns only the transverse closure, not the lifted
domain; the equation is assumed only in its strict interior. -/
theorem uniform_hessian_bound_bounded_density_lattice {n : ℕ}
    (e : CoordinateSpace (n + 1) 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 4 B₀)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {r₀ m M L₁ L : ℝ} (hr₀ : 0 < r₀) (hm : 0 < m) (hM : 0 ≤ M)
    (hL₁ : 0 ≤ L₁) (hL : 0 ≤ L)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 2 F →
      (∀ x, r x ≤ 0 → m ≤ F x) → (∀ x, r x ≤ 0 → F x ≤ M) →
      (∀ x, r x ≤ 0 → ‖fderiv ℝ F x‖ ≤ L₁) →
      (∀ x, r x ≤ 0 → ∀ v, -L * ‖v‖ ^ 2 ≤
        deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0) →
      ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 4 u →
      LatticePeriodic e lat u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x < 0 →
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) x‖ ≤ C := by
  have hn : 1 ≤ n + 1 := by omega
  have hr2 : ContDiff ℝ 2 r := hr.of_le (by norm_num)
  have hB2 : ContDiff ℝ 2 B₀ := hB₀.of_le (by norm_num)
  have hR : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef := by
    intro x hx
    have hu : (OAI.LinearAlgebra.Moore.complexify (r₀ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosDef := by
      rw [OAI.LinearAlgebra.Moore.complexify_real_smul, OAI.LinearAlgebra.Moore.complexify_one]
      exact Matrix.PosDef.one.smul hr₀
    simpa only [← OAI.LinearAlgebra.Moore.complexify_add, sub_add_cancel] using
      Matrix.PosDef.posSemidef_add (hconvex x hx) hu
  obtain ⟨b, B, hb, hbB, hbar⟩ := uniform_solution_barriers_bounded_density_lattice hn e lat hK hne
    hB2 hr2 hbounded hBper hrper hbase hR hdet (U := M) hm
  obtain ⟨D, hD, hbnd⟩ := uniform_boundary_hessian_bound_bounded_density_lattice e lat hK hr
    (hB₀.of_le (by norm_num)) hrper hBper hbounded hreg hm hM hL₁ hb hbB hr₀
    (fun x hx ↦ hbase x hx.le) hconvex
  obtain ⟨R, hRpos, hrR⟩ := exists_lattice_norm_bound e lat hK hr.continuous
    hrper hbounded hr.continuous.continuousOn hrper
  let c := (L * M) / (r₀ * (m / (2 * (M ^ 2 + 1))))
  let d : ℝ := Fintype.card (Fin (n + 1) × Fin 4)
  let H := d ^ 2 * ((d + 2) * (D + c * R))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨D + H + 1, by positivity, ?_⟩
  intro F hF hmin hFM hFL hlog u hu huper huz hup hueq x hx
  have hψ : ContDiff ℝ 4 (fun y ↦ B₀ y + u y) := hB₀.add hu
  have heqD : ∀ z, r z ≤ 0 →
      OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) z) = F z :=
    equality_on_regular_sublevel_of_interior (hr.of_le (by norm_num)) hreg
      (continuous_mooreHessian OAI.Analysis.Calculus.Quaternion.fourSlots (hψ.of_le (by norm_num)))
      hF.continuous (fun z hz ↦ hueq z (neg_of_mem_interior_regular_sublevel hreg hz))
  have hub := hbar F hmin hFM u (hu.of_le (by norm_num)) huper hup hueq huz
  have hboundary := hbnd F (hF.of_le (by norm_num)) hmin hFM hFL u (hu.of_le (by norm_num)) huper huz hub hup heqD
  by_cases hx0 : r x = 0
  · exact (hboundary x hx0).trans (by linarith)
  have hxneg : r x < 0 := lt_of_le_of_ne hx hx0
  have hrx : -r x ≤ R := (neg_le_abs _).trans
    (by simpa only [Real.norm_eq_abs] using hrR x hx)
  have hinner : D - c * r x ≤ D + c * R := by
    nlinarith [mul_le_mul_of_nonneg_left hrx hc]
  have hnorm : ‖fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) x‖ ≤ H := by
    apply hessian_norm_le_of_quaternion_and_upper (hψ.of_le (by norm_num)).contDiffAt
      (hup x hxneg).posSemidef (show 0 ≤ D + c * R by positivity)
    intro v
    have hbdir (z) (hz : r z = 0) :
        directionalDerivative (directionalDerivative (fun y ↦ B₀ y + u y) v) v z ≤ D * ‖v‖ ^ 2 := by
      rw [directionalDerivative_twice (hψ.of_le (by norm_num))]
      calc
        _ ≤ |fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) z v v| := le_abs_self _
        _ ≤ ‖fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) z‖ * ‖v‖ * ‖v‖ := bilinear_abs_le _ _ _
        _ ≤ D * ‖v‖ * ‖v‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hboundary z hz) (norm_nonneg v)) (norm_nonneg v)
        _ = _ := by ring
    have hv := quaternionic_second_directional_estimate_lattice hn e lat hK hψ hr2 hrper
      (hBper.add huper) hbounded hup hueq v hm hM hr₀ (mul_nonneg hL (sq_nonneg ‖v‖))
      (fun z hz ↦ ⟨hmin z hz.le, hFM z hz.le⟩)
      (fun z hz ↦ hconvex z hz.le)
      (fun z hz ↦ by simpa only [neg_mul] using hlog z hz.le v) hbdir x hx
    rw [directionalDerivative_twice (hψ.of_le (by norm_num))] at hv
    have hv' : fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) x v v ≤ (D - c * r x) * ‖v‖ ^ 2 := by
      convert hv using 1 ; dsimp [c] ; ring
    exact hv'.trans (mul_le_mul_of_nonneg_right hinner (sq_nonneg _))
  exact hnorm.trans (by linarith)

end OAI.Analysis.PDE.Dirichlet
