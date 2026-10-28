import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPullbackIsomorphism

/-! # On Open Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.OnOpenBaseChange

noncomputable section

/-! Every base change whose target image lies in an isomorphism open
is itself an isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y T : Scheme.{u}} (f : X ⟶ Y)

theorem isIso_pullback_fst_of_range_subset_isomorphism_open
    (U : Y.Opens) [IsIso (f ∣_ U)] (g : T ⟶ Y) (h : Set.range g ⊆ (U : Set Y)) :
    IsIso (pullback.fst g f) := by
  have hr : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact h
  let k := IsOpenImmersion.lift U.ι g hr
  have hk : k ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  let : IsIso (pullback.fst U.ι f) := (OpenPullbackIsomorphismTransport.isIso_pullback_fst_open_iff f U).mpr inferInstance
  have hi : IsIso (pullback.fst (k ≫ U.ι) f) :=
    (IteratedPullbackIsomorphism.isIso_pullback_fst_iterated_iff U.ι f k).mp inferInstance
  exact hk ▸ hi

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.OnOpenBaseChange
