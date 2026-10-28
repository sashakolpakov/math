import OAI.Analysis.PDE.Dirichlet.Uniform.Mixed

open Set Metric
open scoped Topology ComplexOrder MatrixOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem linear_bound_on_kernel_of_unit_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l g : E →L[ℝ] ℝ) {C : ℝ}
    (h : ∀ v, g v = 0 → ‖v‖ ≤ 1 → |l v| ≤ C) :
    ∀ v, g v = 0 → |l v| ≤ C * ‖v‖ := by
  intro v hv
  by_cases hz : v = 0
  · simp [hz]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w, norm_smul, hn.ne']
  have hgw : g w = 0 := by simp [w, hv]
  have hb := h w hgw hw.le
  have heq : l v = ‖v‖ * l w := by
    simp only [w, map_smul, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  rw [heq, abs_mul, abs_of_pos hn]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hn.le

/-- The compact family is the full boundary times the unit ball of real
directions. Homogeneity gives the mixed bound for every tangent vector. -/
theorem uniform_mixed_hessian_bound {n : ℕ} (hn : 1 ≤ n)
    {r B₀ F : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 3 B₀) (hF : ContDiff ℝ 1 F)
    (hK : IsCompact {x | r x ≤ 0}) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {b B G κ r₀ : ℝ} (hb : 0 ≤ b) (hbB : b ≤ B) (hG : 0 ≤ G) (hκ : 0 < κ) (hr₀ : 0 < r₀)
    (hconvex : ∀ x ∈ interior {x | r x ≤ 0},
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin n) (Fin n) Q))).PosSemidef) :
    ∃ M : ℝ, 0 < M ∧ ∀ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ 3 u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x ≤ 0 → B * r x ≤ u x ∧ u x ≤ b * r x) →
      (∀ x, r x ≤ 0 → ‖fderiv ℝ u x‖ ≤ G) →
      (∀ x ∈ interior {x | r x ≤ 0},
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x ∈ interior {x | r x ≤ 0},
        κ ≤ OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) 1) →
      (∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ x, r x = 0 → ∀ v, fderiv ℝ r x v = 0 →
        |fderiv ℝ (fderiv ℝ u) x (covectorNormal (fderiv ℝ r x)) v| ≤ M * ‖v‖ := by
  let S := {x | r x = 0}
  have hS : IsCompact S := hK.of_isClosed_subset
    (isClosed_eq hr.continuous continuous_const) (fun _ hx ↦ le_of_eq hx)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : CompactSpace (closedBall (0 : CoordinateSpace n 4) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let P := S × closedBall (0 : CoordinateSpace n 4) 1
  let z : P → CoordinateSpace n 4 := fun p ↦ p.1.1
  let e : P → CoordinateSpace n 4 := fun p ↦ p.2.1
  have hz : Continuous z := continuous_subtype_val.comp continuous_fst
  have he : Continuous e := continuous_subtype_val.comp continuous_snd
  have hcenter : ∀ p, r (z p) = 0 := fun p ↦ p.1.2
  obtain ⟨M, hM, hbound⟩ := compact_family_mixed_hessian_bound hn hr hB₀ hF hreg
    hz he hcenter hb hbB hG hκ hr₀ hconvex
  refine ⟨M, hM, ?_⟩
  intro u hu huz hub hug hup hutr hueq x hx
  apply linear_bound_on_kernel_of_unit_ball (fderiv ℝ (fderiv ℝ u) x (covectorNormal (fderiv ℝ r x)))
    (fderiv ℝ r x)
  intro v hv hnv
  have hv' : v ∈ closedBall (0 : CoordinateSpace n 4) 1 := by simpa using hnv
  exact hbound u hu huz hub hug hup hutr hueq (⟨x, hx⟩, ⟨v, hv'⟩) hv

end OAI.Analysis.PDE.Dirichlet
