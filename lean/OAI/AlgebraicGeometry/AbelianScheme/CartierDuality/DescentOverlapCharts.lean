import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicInvariantDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OpenInvariant

/-! # Descent Overlap Charts -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DescentOverlapCharts.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: ordinary invariant sheaves on actual cartesian open charts
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

universe u

section Category

variable {C : Type*} [Category C] [HasPullbacks C]
    {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') (s : Y' ⟶ Y) (t : X' ⟶ X)
    (w : t ≫ f = f' ≫ s)

/-- The canonical map between the two actual kernel pairs. -/
def overlapMap : pullback f' f' ⟶ pullback f f := pullback.map f' f' f f t t s w.symm w.symm

theorem overlapMap_fst : overlapMap f f' s t w ≫ pullback.fst f f = pullback.fst f' f' ≫ t :=
  pullback.lift_fst _ _ _

theorem overlapMap_snd : overlapMap f f' s t w ≫ pullback.snd f f = pullback.snd f' f' ≫ t :=
  pullback.lift_snd _ _ _

/-- Restricting a cartesian cover restricts its entire scheme-theoretic overlap. -/
theorem overlapMap_isPullback (sq : IsPullback t f' f s) :
    IsPullback (overlapMap f f' s t w) (pullback.snd f' f') (pullback.snd f f) t := by
  have outer := (IsPullback.of_hasPullback f' f').paste_horiz sq
  rw [← w, ← overlapMap_fst f f' s t w] at outer
  exact outer.of_right (overlapMap_snd f f' s t w) (IsPullback.of_hasPullback f f)

end Category

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (s : Y' ⟶ Y) (t : X' ⟶ X) (w : t ≫ f = f' ≫ s)
    [IsOpenImmersion s] [IsOpenImmersion t] (sq : IsPullback t f' f s)

include sq in
/-- A cartesian open square has exactly the inverse-image open as its source range. -/
theorem openSquare_range : t.opensRange = f ⁻¹ᵁ s.opensRange := by
  have hi := sq.isoPullback_hom_fst
  apply TopologicalSpace.Opens.ext
  change Set.range t = _
  rw [← hi]
  change Set.range ((pullback.fst f s) ∘ sq.isoPullback.hom) = _
  have he : Function.Surjective sq.isoPullback.hom := sq.isoPullback.hom.homeomorph.surjective
  rw [Set.range_comp, Set.range_eq_univ.mpr he, Set.image_univ]
  exact IsOpenImmersion.range_pullbackFst s f

include sq in
omit [IsOpenImmersion s] in
theorem overlapMap_isOpenImmersion : IsOpenImmersion (overlapMap f f' s t w) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (overlapMap_isPullback f f' s t w sq).flip (inferInstanceAs (IsOpenImmersion t))

variable (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))

/-- The ordinary descent datum on the actual cartesian open chart. -/
def openChartDatum : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f') :=
  Picard.PoincareBundle.Ordinary.SquareGluing.pulledDatum f f' t s w D

/-- The actual invariant sheaf restricts to the invariant on the chart. -/
def ordinaryInvariantOpenIso :
    (Scheme.Modules.restrictFunctor s).obj (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryInvariantSheaf f D) ≅
      Picard.PoincareBundle.Geometric.CechInvariant.ordinaryInvariantSheaf f' (openChartDatum f f' s t w D) := by
  have := overlapMap_isOpenImmersion f f' s t w sq
  exact Picard.PoincareBundle.Ordinary.OpenInvariant.invariantIso f (pullback.fst f f) (pullback.snd f f) pullback.condition
    f' (pullback.fst f' f') (pullback.snd f' f') pullback.condition s t (overlapMap f f' s t w)
    w (overlapMap_fst f f' s t w) (overlapMap_snd f f' s t w) D
    (openSquare_range f f' s t sq).ge
    (openSquare_range (pullback.snd f f) (pullback.snd f' f') t (overlapMap f f' s t w)
      (overlapMap_isPullback f f' s t w sq)).ge

include sq in
/-- Effectivity of the chart datum detects the restricted original recovery map. -/
theorem ordinaryComparison_open_isIso_iff :
    IsIso ((Scheme.Modules.restrictFunctor t).map (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryComparison f D)) ↔
      IsIso (Picard.PoincareBundle.Geometric.CechInvariant.ordinaryComparison f' (openChartDatum f f' s t w D)) := by
  have := overlapMap_isOpenImmersion f f' s t w sq
  exact Picard.PoincareBundle.Ordinary.OpenInvariant.comparison_map_isIso_iff f
    (pullback.fst f f) (pullback.snd f f) pullback.condition
    f' (pullback.fst f' f') (pullback.snd f' f') pullback.condition s t (overlapMap f f' s t w)
    w (overlapMap_fst f f' s t w) (overlapMap_snd f f' s t w) D
    (openSquare_range f f' s t sq).ge
    (openSquare_range (pullback.snd f f) (pullback.snd f' f') t (overlapMap f f' s t w)
      (overlapMap_isPullback f f' s t w sq)).ge

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DescentOverlapCharts.Construction.LineDescent
