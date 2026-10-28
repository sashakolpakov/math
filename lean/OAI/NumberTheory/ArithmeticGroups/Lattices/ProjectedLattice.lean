import OAI.NumberTheory.ArithmeticGroups.Lattices.ShortestVector

/-! # Projected Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ProjectedLattice.Construction

noncomputable section

/-! Projection along a shortest vector preserves lattice discreteness and gives
a uniform lower bound for the lengths of nonzero projected vectors. -/

open scoped Classical
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def perpendicularProjection (v : E) : E →L[ℝ] (Submodule.span ℝ ({v} : Set E))ᗮ :=
  (Submodule.span ℝ ({v} : Set E))ᗮ.orthogonalProjectionOnto

def projectedLattice (Λ : Submodule ℤ E) (v : E) :
    Submodule ℤ (Submodule.span ℝ ({v} : Set E))ᗮ :=
  Λ.map ((perpendicularProjection v).toLinearMap.restrictScalars ℤ)

@[simp] theorem perpendicularProjection_self (v : E) : perpendicularProjection v v = 0 := by
  apply Subtype.ext
  exact Submodule.starProjection_orthogonalComplement_singleton_eq_zero v

theorem projection_reduced_lift (Λ : Submodule ℤ E) {v : E} (hv : v ∈ Λ)
    {x : E} (hx : x ∈ Λ) :
    ∃ y ∈ Λ, perpendicularProjection v y = perpendicularProjection v x ∧
      ‖y‖ ≤ ‖perpendicularProjection v x‖ + ‖v‖ / 2 := by
  let W : Submodule ℝ E := Submodule.span ℝ {v}
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (W.starProjection_apply_mem x)
  let m : ℤ := round t
  let y : E := x - m • v
  have hymem : y ∈ Λ := Λ.sub_mem hx (Λ.smul_mem m hv)
  have hyp : perpendicularProjection v y = perpendicularProjection v x := by
    simp [y]
  have hy : y = (perpendicularProjection v x).val + (t - (m : ℝ)) • v := by
    change x - m • v = Wᗮ.starProjection x + (t - (m : ℝ)) • v
    rw [Submodule.starProjection_orthogonal_val, ← ht, sub_smul, Int.cast_smul_eq_zsmul]
    abel
  refine ⟨y, hymem, hyp, ?_⟩
  rw [hy]
  calc
    ‖(perpendicularProjection v x).val + (t - (m : ℝ)) • v‖ ≤
        ‖(perpendicularProjection v x).val‖ + ‖(t - (m : ℝ)) • v‖ := norm_add_le _ _
    _ ≤ ‖perpendicularProjection v x‖ + ‖v‖ / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      have hb := mul_le_mul_of_nonneg_right (abs_sub_round t) (norm_nonneg v)
      change ‖perpendicularProjection v x‖ + |t - (m : ℝ)| * ‖v‖ ≤ _
      linarith

theorem shortest_vector_projection_gap (Λ : Submodule ℤ E) {v : E} (hv : v ∈ Λ)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖v‖ ≤ ‖x‖)
    {w : (Submodule.span ℝ ({v} : Set E))ᗮ} (hw : w ∈ projectedLattice Λ v)
    (hw0 : w ≠ 0) : ‖v‖ ≤ 2 * ‖w‖ := by
  obtain ⟨x, hx, rfl⟩ := hw
  obtain ⟨y, hy, hyp, hybound⟩ := projection_reduced_lift Λ hv hx
  have hy0 : y ≠ 0 := by
    intro he
    apply hw0
    simpa [he] using hyp.symm
  have h := hmin y hy hy0
  change ‖v‖ ≤ 2 * ‖perpendicularProjection v x‖
  linarith

theorem projected_lattice_discrete (Λ : Submodule ℤ E) {v : E} (hv : v ∈ Λ)
    (hv0 : v ≠ 0) (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖v‖ ≤ ‖x‖) :
    DiscreteTopology (projectedLattice Λ v) := by
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  have he : ({0} : Set (projectedLattice Λ v)) = Metric.ball 0 (‖v‖ / 2) := by
    ext w
    simp only [Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simpa using half_pos (norm_pos_iff.mpr hv0)
    · intro hw
      by_contra hw0
      have h := shortest_vector_projection_gap Λ hv hmin w.property
        (show w.val ≠ 0 from fun he => hw0 (Subtype.ext he))
      change ‖v‖ ≤ 2 * ‖w‖ at h
      linarith
  rw [he]
  exact Metric.isOpen_ball

theorem projected_lattice_full (Λ : Submodule ℤ E)
    (hΛ : Submodule.span ℝ (Λ : Set E) = ⊤) (v : E) :
    Submodule.span ℝ (projectedLattice Λ v : Set (Submodule.span ℝ ({v} : Set E))ᗮ) = ⊤ := by
  rw [projectedLattice, Submodule.map_coe, LinearMap.coe_restrictScalars,
    ← Submodule.map_span, hΛ, Submodule.map_top]
  apply LinearMap.range_eq_top.mpr
  intro y
  refine ⟨y.val, ?_⟩
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self y

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ProjectedLattice.Construction
