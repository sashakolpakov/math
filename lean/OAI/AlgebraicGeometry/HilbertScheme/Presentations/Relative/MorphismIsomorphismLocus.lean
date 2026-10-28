import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FiniteFlatIsomorphismRepresentation

/-! # Morphism Isomorphism Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus

noncomputable section

/-! The relative isomorphism locus applies to the actual canonical map
between the two base-changed total spaces. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B T : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ B) (g : T ⟶ B)

def relativeMorphismBaseChange : pullback (f ≫ q) g ⟶ pullback q g :=
  pullback.map (f ≫ q) g q g f (𝟙 T) (𝟙 B) (by simp) (by simp)

theorem relativeMorphismBaseChange_eq :
    relativeMorphismBaseChange f q g =
      (pullbackRightPullbackFstIso q g f).inv ≫ pullback.snd f (pullback.fst q g) := by
  apply pullback.hom_ext
  · simpa only [relativeMorphismBaseChange, pullback.map, pullback.lift_fst, Category.assoc] using
      (pullbackRightPullbackFstIso_inv_snd_fst q g f).symm
  · simpa only [relativeMorphismBaseChange, pullback.map, pullback.lift_snd, Category.comp_id, Category.assoc] using
      (pullbackRightPullbackFstIso_inv_snd_snd q g f).symm

theorem relativeMorphismBaseChange_isIso_iff :
    IsIso (relativeMorphismBaseChange f q g) ↔ IsIso (pullback.snd f (pullback.fst q g)) := by
  rw [relativeMorphismBaseChange_eq]
  exact isIso_comp_left_iff _ _

variable [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] [IsProper q]

theorem relativeMorphismBaseChange_isIso_iff_range :
    IsIso (relativeMorphismBaseChange f q g) ↔
      Set.range g ⊆ (Proper.FiniteFlatIsomorphismLocus.properFiniteFlatIsomorphismOpen f q : Set B) := by
  rw [relativeMorphismBaseChange_isIso_iff, Proper.FiniteFlatIsomorphismLocus.properFiniteFlat_isIso_pullback_iff_range]

theorem relativeMorphismBaseChange_isIso_iff_unique_lift :
    IsIso (relativeMorphismBaseChange f q g) ↔
      ∃! h : T ⟶ (Proper.FiniteFlatIsomorphismLocus.properFiniteFlatIsomorphismOpen f q).toScheme,
        h ≫ (Proper.FiniteFlatIsomorphismLocus.properFiniteFlatIsomorphismOpen f q).ι = g := by
  rw [relativeMorphismBaseChange_isIso_iff, Proper.FiniteFlatIsomorphismLocus.properFiniteFlat_isIso_pullback_iff_unique_lift]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus
