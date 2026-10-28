import OAI.RepresentationTheory.Theta.Geometric.CompactLattice

/-! # Unitary Automorphy Rigidity -/

namespace OAI.RepresentationTheory.Theta.Geometric.UnitaryAutomorphyRigidity

noncomputable section

/-! A holomorphic function with unitary lattice automorphy is constant.
A nonzero such function forces its lattice character to be trivial. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (L : AddSubgroup V) [CompactSpace (V ⧸ L)]
    (f : V → ℂ)

def periodicNormDescent (q : V ⧸ L) : ℝ := ‖f (Quotient.out q)‖

variable (hperiod : ∀ (l : L) z, ‖f (z + l.val)‖ = ‖f z‖)

include hperiod

omit [NormedSpace ℂ V] [CompactSpace (V ⧸ L)] in
theorem periodicNormDescent_mk (z : V) : periodicNormDescent L f (QuotientAddGroup.mk z) = ‖f z‖ := by
  have hq : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk z : V ⧸ L)) : V ⧸ L) =
      QuotientAddGroup.mk z := Quotient.out_eq _
  let l : L := ⟨Quotient.out (QuotientAddGroup.mk z : V ⧸ L) - z,
    QuotientAddGroup.eq_iff_sub_mem.mp hq⟩
  have he : z + l.val = Quotient.out (QuotientAddGroup.mk z : V ⧸ L) := by dsimp [l]; abel
  exact (congrArg (fun w => ‖f w‖) he).symm.trans (hperiod l z)

omit [NormedSpace ℂ V] [CompactSpace (V ⧸ L)] in
theorem periodicNormDescent_continuous (hf : Continuous f) : Continuous (periodicNormDescent L f) := by
  apply (QuotientAddGroup.isQuotientMap_mk L).continuous_iff.mpr
  have H : periodicNormDescent L f ∘ QuotientAddGroup.mk = fun z => ‖f z‖ :=
    funext (periodicNormDescent_mk L f hperiod)
  rw [H]
  exact hf.norm

omit [NormedSpace ℂ V] in
theorem normPeriodic_bounded (hf : Continuous f) : Bornology.IsBounded (Set.range f) := by
  obtain ⟨C, hC⟩ := (isCompact_range (periodicNormDescent_continuous L f hperiod hf)).isBounded.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C, ?_⟩
  rintro _ ⟨z, rfl⟩
  have H := hC (periodicNormDescent L f (QuotientAddGroup.mk z)) (Set.mem_range_self _)
  rwa [periodicNormDescent_mk L f hperiod, norm_norm] at H

theorem normPeriodic_holomorphic_constant (hf : Differentiable ℂ f) (z w : V) : f z = f w :=
  hf.apply_eq_apply_of_bounded (normPeriodic_bounded L f hperiod hf.continuous) z w

omit hperiod in
theorem unitaryAutomorphy_trivial (χ : L → ℂ) (hχ : ∀ l, ‖χ l‖ = 1)
    (hf : Differentiable ℂ f) (htrans : ∀ (l : L) z, f (z + l.val) = χ l * f z)
    (hf0 : f 0 ≠ 0) (l : L) : χ l = 1 := by
  have hnorm : ∀ (m : L) z, ‖f (z + m.val)‖ = ‖f z‖ := by
    intro m z
    rw [htrans, norm_mul, hχ, one_mul]
  have H : χ l * f 0 = 1 * f 0 := by
    rw [one_mul, ← htrans]
    exact normPeriodic_holomorphic_constant L f hnorm hf _ _
  exact mul_right_cancel₀ hf0 H

end

end OAI.RepresentationTheory.Theta.Geometric.UnitaryAutomorphyRigidity
