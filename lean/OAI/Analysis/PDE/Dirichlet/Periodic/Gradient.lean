import OAI.Analysis.PDE.Dirichlet.Periodic.Interior
import OAI.Analysis.PDE.Dirichlet.Periodic.Data
import OAI.Analysis.PDE.Dirichlet.DataGradient

open Set Filter Module
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- A data-only global gradient bound on the lifted periodic domain. -/
theorem uniform_gradient_bound_from_barriers_lattice {n : ℕ} (hn : 1 ≤ n)
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C)
    {r B₀ F : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 2 r)
    (hB₀ : ContDiff ℝ 3 B₀) (hF : ContDiff ℝ 1 F)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hFper : LatticePeriodic e lat F)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hFpos : ∀ x, r x ≤ 0 → 0 < F x)
    {b B r₀ : ℝ} (hb : 0 ≤ b) (hbB : b ≤ B) (hr₀ : 0 < r₀)
    (hconvex : ∀ x, r x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin n) (Fin n) Q))).PosSemidef) :
    ∃ G : ℝ, 0 < G ∧ ∀ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ 3 u →
      LatticePeriodic e lat u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x ≤ 0 → B * r x ≤ u x ∧ u x ≤ b * r x) →
      (∀ x, r x < 0 →
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x < 0 →
        OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ x, r x ≤ 0 → ‖fderiv ℝ u x‖ ≤ G := by
  obtain ⟨m, hm, hmin⟩ := exists_lattice_positive_lower e lat hC hr.continuous
    hrper hbounded hne hF.continuous.continuousOn hFper hFpos
  obtain ⟨U, hU, hFU⟩ := exists_lattice_norm_bound e lat hC hr.continuous
    hrper hbounded hF.continuous.continuousOn hFper
  obtain ⟨L, hL, hFL⟩ := exists_lattice_norm_bound e lat hC hr.continuous hrper hbounded
    (hF.fderiv_right (m := 0) (by norm_num)).continuous.continuousOn hFper.fderiv
  obtain ⟨D₀, hD₀, hBD⟩ := exists_lattice_norm_bound e lat hC hr.continuous hrper hbounded
    (hB₀.fderiv_right (m := 0) (by norm_num)).continuous.continuousOn hBper.fderiv
  obtain ⟨Dᵣ, hDᵣ, hrD⟩ := exists_lattice_norm_bound e lat hC hr.continuous hrper hbounded
    (hr.fderiv_right (m := 0) (by norm_num)).continuous.continuousOn hrper.fderiv
  obtain ⟨R, hR, hrR⟩ := exists_lattice_norm_bound e lat hC hr.continuous
    hrper hbounded hr.continuous.continuousOn hrper
  let A := D₀ + B * Dᵣ
  let c := L / (r₀ * (m / (2 * (U ^ 2 + 1))))
  have hB : 0 ≤ B := hb.trans hbB
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨A + c * R + D₀ + 1, by positivity, ?_⟩
  intro u hu huper huz hub hup hueq x hx
  have hbd (z) (hz : r z = 0) : ‖fderiv ℝ (fun w ↦ B₀ w + u w) z‖ ≤ A := by
    exact (boundary_gradient_norm_add_of_barriers
      (hB₀.differentiable (by norm_num) z) (hu.differentiable (by norm_num) z)
      (hr.differentiable (by norm_num) z) (huz z hz) hz (hreg z hz)
      hb hbB hub (Eventually.of_forall (fun _ ht ↦ ht.le))).trans
        (add_le_add (hBD z hz.le) (mul_le_mul_of_nonneg_left (hrD z hz.le) hB))
  have hgrad : ‖fderiv ℝ (fun z ↦ B₀ z + u z) x‖ ≤ A - c * r x := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by
      have := mul_nonpos_of_nonneg_of_nonpos hc hx
      linarith)
    intro v
    have hd (z) (hz : r z < 0) : |directionalDerivative F v z| ≤ L * ‖v‖ := by
      exact (ContinuousLinearMap.le_opNorm (fderiv ℝ F z) v).trans
        (mul_le_mul_of_nonneg_right (hFL z hz.le) (norm_nonneg v))
    have hbv (z) (hz : r z = 0) :
        |directionalDerivative (fun w ↦ B₀ w + u w) v z| ≤ A * ‖v‖ := by
      exact (ContinuousLinearMap.le_opNorm (fderiv ℝ (fun w ↦ B₀ w + u w) z) v).trans
        (mul_le_mul_of_nonneg_right (hbd z hz) (norm_nonneg v))
    have hv := quaternionic_gradient_estimate_lattice hn e lat hC (hB₀.add hu) hr
      (hF.differentiable (by norm_num)).differentiableOn hrper (hBper.add huper)
      hbounded hup hueq v hm hr₀ (mul_nonneg hL.le (norm_nonneg v))
      (fun z hz ↦ ⟨hmin z hz.le, (le_abs_self _).trans
        (by simpa only [Real.norm_eq_abs] using hFU z hz.le)⟩)
      hconvex hd hbv x hx
    change |directionalDerivative (fun z ↦ B₀ z + u z) v x| ≤ _
    convert hv using 1 ; dsimp [c] ; ring
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
