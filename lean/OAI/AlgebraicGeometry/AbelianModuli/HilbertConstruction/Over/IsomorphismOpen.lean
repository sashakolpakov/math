import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.IsomorphismComparison
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeIsomorphismLocus

/-! # Isomorphism Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsomorphismOpen

noncomputable section

/-! A proper family morphism with flat source has an actual open base exactly classifying when its arbitrary pullback is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def overIsomorphismOpen {S : Scheme.{u}} {X Y : Over S} [IsProper Y.hom] (j : X ⟶ Y) : S.Opens :=
  HilbertScheme.Presentations.Proper.RelativeIsomorphismOpen.properRelativeIsomorphismOpen j.left Y.hom

theorem overIsomorphismOpen_pullback_iff
    {S T : Scheme.{u}} {X Y : Over S}
    [IsProper X.hom] [Flat X.hom] [IsProper Y.hom] [IsLocallyNoetherian Y.left]
    (j : X ⟶ Y) (c : T ⟶ S) :
    IsIso ((Over.pullback c).map j) ↔ Set.range c ⊆ overIsomorphismOpen j := by
  have : IsProper (j.left ≫ Y.hom) := j.w.symm ▸ (inferInstanceAs (IsProper X.hom))
  have : IsProper j.left := IsProper.of_comp j.left Y.hom
  have : Flat (j.left ≫ Y.hom) := j.w.symm ▸ (inferInstanceAs (Flat X.hom))
  exact (Relative.IsomorphismComparison.overPullback_map_isIso_iff_relativeMorphismBaseChange j c).trans
    (HilbertScheme.Presentations.Proper.RelativeIsomorphismLocus.properRelative_isIso_baseChange_iff_range j.left Y.hom c)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsomorphismOpen
