import OAI.Analysis.PDE.Dirichlet.Boundary.Quadratic
import OAI.Analysis.PDE.Dirichlet.Boundary.Centered
import OAI.Analysis.PDE.Dirichlet.Boundary.Data
import OAI.Analysis.PDE.Dirichlet.BoundedForcing

open Set Filter Metric
open scoped Topology ComplexOrder MatrixOrder Matrix InnerProductSpace

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- A uniform mixed boundary estimate for a compact family of centers and
directions. All forcing and boundary constants are derived from fixed data. -/
theorem compact_family_mixed_hessian_bound_bounded_density
    {P : Type*} [TopologicalSpace P] [CompactSpace P] {n : ℕ} (hn : 1 ≤ n)
    {r B₀ : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 3 B₀)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {z e : P → CoordinateSpace n 4} (hz : Continuous z) (he : Continuous e)
    (hcenter : ∀ p, r (z p) = 0) {b B G κ r₀ L₀ : ℝ}
    (hL₀ : 0 ≤ L₀) (hb : 0 ≤ b) (hbB : b ≤ B) (hG : 0 ≤ G) (hκ : 0 < κ) (hr₀ : 0 < r₀)
    (hconvex : ∀ x ∈ interior {x | r x ≤ 0},
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin n) (Fin n) Q))).PosSemidef) :
    ∃ M : ℝ, 0 < M ∧ ∀ F : CoordinateSpace n 4 → ℝ, ContDiff ℝ 1 F →
      (∀ x, r x ≤ 0 → ‖fderiv ℝ F x‖ ≤ L₀) →
      ∀ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ 3 u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x ≤ 0 → B * r x ≤ u x ∧ u x ≤ b * r x) →
      (∀ x, r x ≤ 0 → ‖fderiv ℝ u x‖ ≤ G) →
      (∀ x ∈ interior {x | r x ≤ 0},
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x ∈ interior {x | r x ≤ 0},
        κ ≤ OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) 1) →
      (∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ p, fderiv ℝ r (z p) (e p) = 0 →
        |fderiv ℝ (fderiv ℝ u) (z p) (covectorNormal (fderiv ℝ r (z p))) (e p)| ≤ M := by
  have hr2 : ContDiff ℝ 2 r := hr.of_le (by norm_num)
  let K : Set (CoordinateSpace n 4) :=
    (fun p : P × CoordinateSpace n 4 ↦ z p.1 + p.2) ''
      (univ ×ˢ closedBall 0 1) ∩ {x | r x ≤ 0}
  have hK : IsCompact K :=
    (((isCompact_univ : IsCompact (univ : Set P)).prod (isCompact_closedBall 0 1)).image
      ((hz.comp continuous_fst).add continuous_snd)).inter_right
        (isClosed_le hr.continuous continuous_const)
  have hKm (p : P) (y : CoordinateSpace n 4) (hy : r y ≤ 0) (hball : ‖y - z p‖ ≤ 1) :
      y ∈ K := by
    refine ⟨⟨(p, y - z p), ⟨mem_univ p, ?_⟩, ?_⟩, hy⟩
    · simpa only [mem_closedBall, dist_zero_right] using hball
    · dsimp
      abel
  have hregp := fun p ↦ hreg (z p) (hcenter p)
  let R : P → Matrix (Fin n) (Fin n) Q := fun p ↦ boundaryRotation r (z p) (e p)
  let A : P → CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 :=
    fun p ↦ boundaryFieldLinear r (z p) (e p)
  let t : P → CoordinateSpace n 4 := fun p ↦ boundaryFieldTranslation r (z p) (e p)
  have hR : Continuous R := continuous_boundaryRotation hr2 hz he hregp
  have hA : Continuous A := continuous_realMatrixAction.comp (continuous_realRepresentation hR)
  have ht : Continuous t := he.sub (hA.clm_apply hz)
  have hskew : ∀ p, (R p)ᴴ = -R p := fun p ↦ (adaptedRotation_spec (hregp p) _ _).1
  obtain ⟨C, hC, hforce⟩ := exists_bounded_density_rigid_forcing hB₀ ht hR hskew hK hκ hL₀
  obtain ⟨D, hD, hquad⟩ := exists_compact_boundary_quadratic hr hz he hregp
  obtain ⟨L, hL, hsize⟩ := exists_compact_family_affine_size_bound ht hA hK
  have hnorm : Continuous (fun p ↦ ‖fderiv ℝ r (z p)‖) :=
    ((hr2.fderiv_right (m := 1) (by norm_num)).continuous.comp hz).norm
  obtain ⟨N₀, hN₀⟩ := (isCompact_univ : IsCompact (univ : Set P)).bddAbove_image hnorm.continuousOn
  let N := max N₀ 0 + 1
  have hN : 0 < N := by dsimp [N]; positivity
  have hNbound : ∀ p, ‖fderiv ℝ r (z p)‖ ≤ N := by
    intro p
    have h := hN₀ (mem_image_of_mem _ (mem_univ p))
    exact h.trans (by dsimp [N]; linarith [le_max_left N₀ 0])
  have hB : 0 ≤ B := hb.trans hbB
  let c := (C + 8 * (B * D + G * L)) / r₀
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c * N, mul_pos hc hN, ?_⟩
  intro F hF hFL u hu huz hub hug hup hutr hueq p hep
  let x := z p
  let ν := covectorNormal (fderiv ℝ r x)
  have hnear (y : CoordinateSpace n 4) :
      ∀ᶠ w in 𝓝 y, r w < 0 → w ∈ {x | r x ≤ 0} :=
    Eventually.of_forall fun _ hw ↦ hw.le
  obtain ⟨a, hba, haB, hfac⟩ := boundary_gradient_factor_of_barriers
    (hu.differentiable (by norm_num) x) (hr2.differentiable (by norm_num) x)
    (huz x (hcenter p)) (hcenter p) (hregp p) hb hbB hub (hnear x)
  have hnormal : fderiv ℝ r x ν = ‖fderiv ℝ r x‖ := by
    have h := congrArg (fun l : CoordinateSpace n 4 →L[ℝ] ℝ ↦ l ν)
      (covectorNormal_form (hregp p))
    simpa [ν, x, innerSL_apply_apply, covectorNormal_unit (hregp p)] using h
  have hrot : fderiv ℝ r x (A p ν) = 0 := (adaptedRotation_jet (hregp p) _ _).1
  have hneg : fderiv ℝ r x (-ν) < 0 := by
    rw [map_neg, hnormal]
    exact neg_neg_of_pos (norm_pos_iff.mpr (hregp p))
  have hrotneg : fderiv ℝ r x (A p (-ν)) = 0 := by rw [map_neg, map_neg, hrot, neg_zero]
  have hboundary : ∀ y, r y ≤ 0 → ‖y - x‖ ≤ 1 → r y = 0 →
      |affineDerivative u (e p - A p x) (A p) y| ≤ B * D * ‖y - x‖ ^ 2 := by
    intro y hy hyx hry
    have hbnd := affineDerivative_abs_le_of_barriers (e p - A p x) (A p)
      (hu.differentiable (by norm_num) y) (hr2.differentiable (by norm_num) y)
      (huz y hry) hry (hreg y hry) hb hbB hub (hnear y)
    have hq := hquad p (hcenter p) hep y hyx hry
    exact hbnd.trans (by simpa only [x, A, boundaryFieldTranslation, mul_assoc] using
      mul_le_mul_of_nonneg_left hq hB)
  have hforcing : ∀ y ∈ interior {x | r x ≤ 0}, ‖y - x‖ ≤ 1 →
      |mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y))
        (affineDerivative u (e p - A p x) (A p)) y| ≤
        C * OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) y) 1 := by
    intro y hy hyball
    have heq : (fun w ↦ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun v ↦ B₀ v + u v) w)) =ᶠ[𝓝 y] F := by
      filter_upwards [mem_interior_iff_mem_nhds.mp hy] with w hw
      exact hueq w hw
    exact hforce F hF (fun w hw ↦ hFL w hw.2) p u hu y (hKm p y (interior_subset (s := {x | r x ≤ 0}) hy) hyball)
      (hup y hy) (hutr y hy) heq
  have h := boundary_mixed_hessian_centered hn (mul_nonneg hB hD.le) (mul_nonneg hG hL.le)
    hC.le hr₀ hu hr2 (hcenter p) hfac hep hrotneg hneg hup hconvex hforcing hboundary
    (fun y hy hyball ↦ hsize u G hG (fun w hw ↦ hug w hw.2) p y (hKm p y hy hyball))
  have hbound : |fderiv ℝ (fderiv ℝ u) x ν (e p)| ≤ c * ‖fderiv ℝ r x‖ := by
    have hnormal' : fderiv ℝ r (z p) ν = ‖fderiv ℝ r (z p)‖ := hnormal
    simpa only [x, map_neg, neg_apply, abs_neg, hnormal', neg_mul_neg, c] using h
  exact hbound.trans (mul_le_mul_of_nonneg_left (hNbound p) hc.le)

end OAI.Analysis.PDE.Dirichlet
