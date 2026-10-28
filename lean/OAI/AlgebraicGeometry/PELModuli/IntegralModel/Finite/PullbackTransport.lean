import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Restrict

/-! # Pullback Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PullbackTransport

noncomputable section

/-! Finiteness under iterated and open base changes, retaining the
actual pullback projections used by relative section morphisms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {W X Y B T : Scheme.{u}}

theorem finite_pullback_snd_iff_fst (f : X ⟶ B) (g : Y ⟶ B) :
    IsFinite (pullback.snd f g) ↔ IsFinite (pullback.fst g f) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
    (pullbackSymmetry g f).hom, pullbackSymmetry_hom_comp_snd]

theorem finite_pullback_fst_iterated_iff (g : Y ⟶ B) (f : X ⟶ B) (h : W ⟶ Y) :
    IsFinite (pullback.fst h (pullback.fst g f)) ↔ IsFinite (pullback.fst (h ≫ g) f) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
    (pullbackRightPullbackFstIso g f h).hom, pullbackRightPullbackFstIso_hom_fst]

theorem finite_pullback_fst_open_iff (f : X ⟶ Y) (U : Y.Opens) :
    IsFinite (pullback.fst U.ι f) ↔ IsFinite (f ∣_ U) := by
  rw [← (isPullback_morphismRestrict f U).isoPullback_inv_fst]
  exact MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) _ _

theorem finite_pullback_fst_of_range_subset_open (f : X ⟶ Y)
    (U : Y.Opens) [IsFinite (f ∣_ U)] (g : T ⟶ Y) (h : Set.range g ⊆ (U : Set Y)) :
    IsFinite (pullback.fst g f) := by
  have hr : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact h
  let k := IsOpenImmersion.lift U.ι g hr
  have hk : k ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  let : IsFinite (pullback.fst U.ι f) := (finite_pullback_fst_open_iff f U).mpr inferInstance
  have hi : IsFinite (pullback.fst (k ≫ U.ι) f) :=
    (finite_pullback_fst_iterated_iff U.ι f k).mp inferInstance
  exact hk ▸ hi

theorem relativeMorphismBaseChange_isFinite_iff (f : X ⟶ Y) (q : Y ⟶ B) (g : T ⟶ B) :
    IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g) ↔ IsFinite (pullback.snd f (pullback.fst q g)) := by
  rw [HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange_eq]
  exact MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) _ _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PullbackTransport
