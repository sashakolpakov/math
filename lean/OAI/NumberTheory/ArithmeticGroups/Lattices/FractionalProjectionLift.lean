import OAI.NumberTheory.ArithmeticGroups.Lattices.ProjectedLattice

/-! # Fractional Projection Lift -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.FractionalProjectionLift.Construction

noncomputable section

/-! Integral reduction along a lattice vector makes its coefficient
lie in the interval [-1/2, 1/2], while preserving orthogonal projection. -/

theorem projection_fractional_lift
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Λ : Submodule ℤ E) {v : E} (hv : v ∈ Λ) {x : E} (hx : x ∈ Λ) :
    ∃ y ∈ Λ, ∃ c : ℝ, |c| ≤ 1 / 2 ∧
      y = (ProjectedLattice.Construction.perpendicularProjection v x).val + c • v ∧
      ProjectedLattice.Construction.perpendicularProjection v y = ProjectedLattice.Construction.perpendicularProjection v x := by
  let W : Submodule ℝ E := Submodule.span ℝ {v}
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (W.starProjection_apply_mem x)
  let m : ℤ := round t
  refine ⟨x - m • v, Λ.sub_mem hx (Λ.smul_mem m hv), t - (m : ℝ), abs_sub_round t, ?_, ?_⟩
  · change x - m • v = Wᗮ.starProjection x + (t - (m : ℝ)) • v
    rw [Submodule.starProjection_orthogonal_val, ← ht, sub_smul, Int.cast_smul_eq_zsmul]
    abel
  · simp

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.FractionalProjectionLift.Construction
