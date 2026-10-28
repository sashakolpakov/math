import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameAtPoint
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FieldPointFactors
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineTransitionPowers

/-! # Line Field Frames -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineFieldFrames

noncomputable section

/-! Each standard line-bundle frame gives a frame of the same module
at the common field-valued point. Overlap restrictions give these exact frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)))

def projectiveLineFieldFrame (i : Fin (n + 1)) :
    (Scheme.Modules.pullback (FunctionFieldPoint.projectiveFunctionFieldPoint K n)).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))) :=
  FrameAtPoint.frameAtPoint (FieldPointFactors.projectiveCoordinateFieldPoint K i) (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).ι
    (FunctionFieldPoint.projectiveFunctionFieldPoint K n) (FieldPointFactors.projectiveCoordinateFieldPoint_inclusion K i) (ChartLineFrames.projectiveOpenLineFrame K i L)

theorem projectiveLineFieldFrame_left (i j : Fin (n + 1)) :
    FrameAtPoint.frameAtPoint (FieldPointFactors.projectiveDoubleFieldPoint K i j) (OverlapSectionUnits.projectiveDoubleOpen K i j).ι
      (FunctionFieldPoint.projectiveFunctionFieldPoint K n) (FieldPointFactors.projectiveDoubleFieldPoint_inclusion K i j)
        (LineTransitionPowers.projectiveLineOverlapLeftFrame K L i j) = projectiveLineFieldFrame K L i :=
  FrameAtPoint.frameAtPoint_restrict ((OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_left)
    (FieldPointFactors.projectiveDoubleFieldPoint K i j) (FieldPointFactors.projectiveCoordinateFieldPoint K i) (FunctionFieldPoint.projectiveFunctionFieldPoint K n)
    (FieldPointFactors.projectiveDoubleFieldPoint_inclusion K i j) (FieldPointFactors.projectiveCoordinateFieldPoint_inclusion K i)
    (ChartLineFrames.projectiveOpenLineFrame K i L)

theorem projectiveLineFieldFrame_right (i j : Fin (n + 1)) :
    FrameAtPoint.frameAtPoint (FieldPointFactors.projectiveDoubleFieldPoint K i j) (OverlapSectionUnits.projectiveDoubleOpen K i j).ι
      (FunctionFieldPoint.projectiveFunctionFieldPoint K n) (FieldPointFactors.projectiveDoubleFieldPoint_inclusion K i j)
        (LineTransitionPowers.projectiveLineOverlapRightFrame K L i j) = projectiveLineFieldFrame K L j :=
  FrameAtPoint.frameAtPoint_restrict ((OverlapSectionUnits.projectiveDoubleOpen_eq_inf K i j).le.trans inf_le_right)
    (FieldPointFactors.projectiveDoubleFieldPoint K i j) (FieldPointFactors.projectiveCoordinateFieldPoint K j) (FunctionFieldPoint.projectiveFunctionFieldPoint K n)
    (FieldPointFactors.projectiveDoubleFieldPoint_inclusion K i j) (FieldPointFactors.projectiveCoordinateFieldPoint_inclusion K j)
    (ChartLineFrames.projectiveOpenLineFrame K j L)

theorem projectiveLineFieldFrame_transition (i j : Fin (n + 1)) :
    FrameTransitionCocycles.frameTransitionValue (projectiveLineFieldFrame K L i) (projectiveLineFieldFrame K L j) =
      (FieldPointFactors.projectiveDoubleFieldPoint K i j).appTop
        (FrameTransitionCocycles.frameTransitionValue (LineTransitionPowers.projectiveLineOverlapLeftFrame K L i j) (LineTransitionPowers.projectiveLineOverlapRightFrame K L i j)) := by
  rw [← projectiveLineFieldFrame_left K L i j, ← projectiveLineFieldFrame_right K L i j]
  exact FrameAtPoint.frameTransitionValue_frameAtPoint _ _ _ _ _ _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineFieldFrames
