import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeIsomorphismOpen
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.IsomorphismFieldDescent

/-! # Relative Isomorphism Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeIsomorphismLocus

noncomputable section

/-! For a proper family morphism with flat source over the base, the
relative isomorphism open has its exact universal property on every scheme test. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B : Scheme.{u}} [IsLocallyNoetherian Y]
variable (f : X ⟶ Y) (q : Y ⟶ B) [IsProper f] [Flat (f ≫ q)] [IsProper q]

theorem properRelative_isIso_baseChange_iff_range {T : Scheme.{u}} (g : T ⟶ B) :
    IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g) ↔
      Set.range g ⊆ (RelativeIsomorphismOpen.properRelativeIsomorphismOpen f q : Set B) := by
  constructor
  · intro h b hb
    obtain ⟨t, rfl⟩ := hb
    exact (RelativeIsomorphismOpen.properRelativeIsomorphismOpen_fiber_iff f q (g t)).mpr
      (Relative.IsomorphismFieldDescent.relativeMorphismBaseChange_isIso_at_image_point f q g h t)
  · exact RelativeIsomorphismOpen.properRelativeIsomorphismOpen_isIso_of_range f q g

theorem properRelative_isIso_baseChange_iff_unique_lift {T : Scheme.{u}} (g : T ⟶ B) :
    IsIso (Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g) ↔
      ∃! h : T ⟶ (RelativeIsomorphismOpen.properRelativeIsomorphismOpen f q).toScheme,
        h ≫ (RelativeIsomorphismOpen.properRelativeIsomorphismOpen f q).ι = g := by
  rw [properRelative_isIso_baseChange_iff_range]
  constructor
  · intro h
    have hr : Set.range g ⊆ Set.range (RelativeIsomorphismOpen.properRelativeIsomorphismOpen f q).ι := by
      rw [Scheme.Opens.range_ι]
      exact h
    let k := IsOpenImmersion.lift (RelativeIsomorphismOpen.properRelativeIsomorphismOpen f q).ι g hr
    have hk : k ≫ (RelativeIsomorphismOpen.properRelativeIsomorphismOpen f q).ι = g :=
      IsOpenImmersion.lift_fac _ _ _
    exact ⟨k, hk, fun l hl =>
      (cancel_mono (RelativeIsomorphismOpen.properRelativeIsomorphismOpen f q).ι).mp (hl.trans hk.symm)⟩
  · rintro ⟨h, hh, _⟩ b ⟨t, rfl⟩
    rw [← hh]
    exact (h t).property

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeIsomorphismLocus
