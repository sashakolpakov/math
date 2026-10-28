import OAI.Analysis.PDE.Elliptic.Boundary.HalfPatch

/-! The full closed half-ball, including its spherical edge, is the
closure of the positive open half-ball. -/

noncomputable section
open Set Metric
namespace OAI.Analysis.PDE.Elliptic

variable {m : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)

def positiveCoordinateHalfPatch (k : Fin m) : Set X :=
  ball 0 (1/2) ∩ {x | 0 < x k}

theorem isOpen_positiveCoordinateHalfPatch (k : Fin m) :
    IsOpen (positiveCoordinateHalfPatch k) :=
  isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))

theorem convex_positiveCoordinateHalfPatch (k : Fin m) :
    Convex ℝ (positiveCoordinateHalfPatch k) := by
  apply (convex_ball (0 : X) (1/2)).inter
  intro x hx y hy a b ha hb hab
  change 0 < a*x k+b*y k
  have hp : 0 < a ∨ 0 < b := by
    rcases eq_or_lt_of_le ha with h | h
    · right
      linarith
    · exact Or.inl h
  rcases hp with hp | hp
  · exact add_pos_of_pos_of_nonneg (mul_pos hp hx) (mul_nonneg hb hy.le)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg ha hx.le) (mul_pos hp hy)

theorem closure_positiveCoordinateHalfPatch (k : Fin m) :
    closure (positiveCoordinateHalfPatch k) = closedCoordinateHalfPatch k 0 (1/2) := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro x hx
      exact ⟨ball_subset_closedBall hx.1, (show 0 < x k from hx.2).le⟩
    · exact (isCompact_closedCoordinateHalfPatch k 0 (1/2)).isClosed
  · intro x hx
    have hxnorm : ‖x‖ ≤ (1/2 : ℝ) := by simpa only [mem_closedBall, dist_zero_right] using hx.1
    have hxk : 0 ≤ x k := hx.2
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let t : ℝ := min (ε/2) (1/2)
    have ht : 0 < t := lt_min (by positivity) (by norm_num)
    have ht1 : t ≤ (1/2 : ℝ) := min_le_right _ _
    have hte : t ≤ ε/2 := min_le_left _ _
    have ht0 : 0 ≤ 1-t := by linarith
    let q : X := (1/4 : ℝ) • EuclideanSpace.single k (1 : ℝ)
    have hq : ‖q‖ = (1/4 : ℝ) := by simp [q, norm_smul]
    have hqk : q k = (1/4 : ℝ) := by simp [q]
    let y : X := (1-t) • x+t • q
    have hynorm : ‖y‖ < (1/2 : ℝ) := by
      calc
        ‖y‖ ≤ ‖(1-t) • x‖+‖t • q‖ := norm_add_le _ _
        _ = (1-t)*‖x‖+t*(1/4) := by rw [norm_smul, norm_smul, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_pos ht, hq]
        _ ≤ (1-t)*(1/2)+t*(1/4) := by gcongr
        _ < 1/2 := by linarith
    have hyk : 0 < y k := by
      change 0 < (1-t)*x k+t*q k
      rw [hqk]
      exact add_pos_of_nonneg_of_pos (mul_nonneg ht0 hxk) (mul_pos ht (by norm_num))
    have hdiff : y-x = t • (q-x) := by dsimp only [y]; module
    have hdist : dist x y < ε := by
      rw [dist_comm, dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      calc
        t*‖q-x‖ ≤ t*(‖q‖+‖x‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) ht.le
        _ ≤ t*((1/4)+(1/2)) := by rw [hq]; gcongr
        _ < ε := by linarith
    exact ⟨y, ⟨by simpa only [mem_ball, dist_zero_right] using hynorm, hyk⟩, hdist⟩

section Isometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def positiveIsometryHalfPatch (e : X ≃ₗᵢ[ℝ] E) (k : Fin m) : Set E :=
  e.symm ⁻¹' positiveCoordinateHalfPatch k

theorem isOpen_positiveIsometryHalfPatch (e : X ≃ₗᵢ[ℝ] E) (k : Fin m) :
    IsOpen (positiveIsometryHalfPatch e k) :=
  (isOpen_positiveCoordinateHalfPatch k).preimage e.symm.continuous

theorem convex_positiveIsometryHalfPatch (e : X ≃ₗᵢ[ℝ] E) (k : Fin m) :
    Convex ℝ (positiveIsometryHalfPatch e k) := by
  intro x hx y hy a b ha hb hab
  change e.symm (a • x+b • y) ∈ positiveCoordinateHalfPatch k
  rw [map_add, map_smul, map_smul]
  exact convex_positiveCoordinateHalfPatch k hx hy ha hb hab

theorem closure_positiveIsometryHalfPatch (e : X ≃ₗᵢ[ℝ] E) (k : Fin m) :
    closure (positiveIsometryHalfPatch e k) = e.symm ⁻¹' closedCoordinateHalfPatch k 0 (1/2) := by
  have h := e.symm.toHomeomorph.preimage_closure (positiveCoordinateHalfPatch k)
  change e.symm ⁻¹' closure (positiveCoordinateHalfPatch k) =
    closure (e.symm ⁻¹' positiveCoordinateHalfPatch k) at h
  rw [positiveIsometryHalfPatch, ← h, closure_positiveCoordinateHalfPatch]

theorem isCompact_closure_positiveIsometryHalfPatch (e : X ≃ₗᵢ[ℝ] E) (k : Fin m) :
    IsCompact (closure (positiveIsometryHalfPatch e k)) := by
  rw [closure_positiveIsometryHalfPatch]
  have heq : e.symm ⁻¹' closedCoordinateHalfPatch k 0 (1/2) =
      e '' closedCoordinateHalfPatch k 0 (1/2) := by
    ext x
    constructor
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, e.symm_apply_apply] using hy
  rw [heq]
  exact (isCompact_closedCoordinateHalfPatch k 0 (1/2)).image e.continuous

theorem diameter_positiveIsometryHalfPatch (e : X ≃ₗᵢ[ℝ] E) (k : Fin m) :
    ∀ x ∈ closure (positiveIsometryHalfPatch e k),
      ∀ y ∈ closure (positiveIsometryHalfPatch e k), ‖x-y‖ ≤ 1 := by
  intro x hx y hy
  rw [closure_positiveIsometryHalfPatch] at hx hy
  have hxnorm : ‖x‖ ≤ (1/2 : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right, e.symm.norm_map] using hx.1
  have hynorm : ‖y‖ ≤ (1/2 : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right, e.symm.norm_map] using hy.1
  exact (norm_sub_le x y).trans (by linarith)

theorem halfPatch_subset_isometry_closure (e : X ≃ₗᵢ[ℝ] E) (k : Fin m) :
    closedCoordinateHalfPatch k 0 (1/2) ⊆ e ⁻¹' closure (positiveIsometryHalfPatch e k) := by
  intro x hx
  rw [mem_preimage, closure_positiveIsometryHalfPatch, mem_preimage, e.symm_apply_apply]
  exact hx

theorem positive_halfBall_mem_isometry_patch (e : X ≃ₗᵢ[ℝ] E) (k : Fin m)
    {x : X} (hx : x ∈ ball 0 (1/8)) (hxk : 0 < x k) :
    e x ∈ positiveIsometryHalfPatch e k := by
  change e.symm (e x) ∈ positiveCoordinateHalfPatch k
  rw [e.symm_apply_apply]
  exact ⟨ball_subset_ball (by norm_num) hx, hxk⟩

end Isometry
end OAI.Analysis.PDE.Elliptic
