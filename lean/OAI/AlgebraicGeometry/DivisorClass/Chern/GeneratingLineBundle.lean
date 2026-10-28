import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RegularLineBundle
import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.CocyclePullback

/-! # Generating Line Bundle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingLineBundle

noncomputable section

/-! An actual projective scheme morphism constructs a native algebraic line bundle on its original source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- This is the sheaf of compatible regular coordinates of the pulled-back
projective cocycle. No algebraization or Chern-class equality is an input. -/
def generatingAlgebraicLineBundle (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {n : ℕ}
    (g : P.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver) : Line.Bundles.AlgebraicLineBundle P :=
  Regular.LineBundle.regularCocycleAlgebraicLineBundle P
    (Regular.CocyclePullback.regularCocyclePullback (Projective.RegularLineBundle.projectiveRegularLineCocycle n) g.left)

def generatingAlgebraicLineBundle_frame (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {n : ℕ}
    (g : P.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver) (i : Fin (n + 1)) :
    (generatingAlgebraicLineBundle P g).sheaf.restrict
        (g.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).ι ≅
      Line.Bundles.Construction.structureModule (g.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i).toScheme :=
  Regular.LineBundle.regularLineModuleNativeIso (Regular.CocyclePullback.regularCocyclePullback (Projective.RegularLineBundle.projectiveRegularLineCocycle n) g.left) i

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingLineBundle
