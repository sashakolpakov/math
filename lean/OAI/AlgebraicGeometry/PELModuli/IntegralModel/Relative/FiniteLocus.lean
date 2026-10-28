import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteFiberDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.RelativeFiniteNeighborhood

/-! # Finite Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteLocus

noncomputable section

/-! The open finite-family locus classifies finiteness after every
scheme base change. In particular, geometric fibers detect membership. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B T : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ B)
variable [IsProper f] [IsProper q]

theorem relativeMorphismBaseChange_isFinite_iff_range (g : T ⟶ B) :
    IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g) ↔
      Set.range g ⊆ (Proper.RelativeFiniteNeighborhood.properRelativeFiniteOpen f q : Set B) := by
  constructor
  · intro h b hb
    apply (Proper.RelativeFiniteNeighborhood.mem_properRelativeFiniteOpen f q b).mpr
    intro y hy
    apply (MaximalFiniteOpen.mem_maximalFiniteOpen f y).mpr
    apply exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y
    apply FiniteFiberDescent.finite_target_fiber_of_finite_baseChange f q g h y
    exact hy.symm ▸ hb
  · exact Proper.RelativeFiniteNeighborhood.relativeMorphismBaseChange_isFinite_of_range_subset f q g

theorem relativeMorphismBaseChange_isFinite_iff_unique_lift (g : T ⟶ B) :
    IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g) ↔
      ∃! h : T ⟶ (Proper.RelativeFiniteNeighborhood.properRelativeFiniteOpen f q).toScheme,
        h ≫ (Proper.RelativeFiniteNeighborhood.properRelativeFiniteOpen f q).ι = g := by
  rw [relativeMorphismBaseChange_isFinite_iff_range]
  constructor
  · intro h
    have hr : Set.range g ⊆ Set.range (Proper.RelativeFiniteNeighborhood.properRelativeFiniteOpen f q).ι := by
      rw [Scheme.Opens.range_ι]
      exact h
    let k := IsOpenImmersion.lift (Proper.RelativeFiniteNeighborhood.properRelativeFiniteOpen f q).ι g hr
    have hk : k ≫ (Proper.RelativeFiniteNeighborhood.properRelativeFiniteOpen f q).ι = g := IsOpenImmersion.lift_fac _ _ _
    exact ⟨k, hk, fun l hl =>
      (cancel_mono (Proper.RelativeFiniteNeighborhood.properRelativeFiniteOpen f q).ι).mp (hl.trans hk.symm)⟩
  · rintro ⟨h, hh, _⟩ b ⟨t, rfl⟩
    rw [← hh]
    exact (h t).property

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteLocus
