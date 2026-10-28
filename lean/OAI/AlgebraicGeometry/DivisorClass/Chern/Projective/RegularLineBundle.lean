import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RegularRatioCocycle
import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.LineBundle
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveScheme

/-! # Regular Line Bundle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RegularLineBundle

noncomputable section

/-! The actual projective algebraic line bundle with transition functions `Xᵢ / Xⱼ`. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Coordinates relative to the generating section `Xᵢ` change to those
relative to `Xⱼ` by the regular unit `Xᵢ / Xⱼ`. -/
def projectiveRegularTransition (n : ℕ) (i j : Fin (n + 1))
    (W : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens)
    (hWi : W ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) (hWj : W ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j) :
    Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, W)ˣ where
  val := RegularRatios.projectiveRegularRatio n j i W hWj
  inv := RegularRatios.projectiveRegularRatio n i j W hWi
  val_inv := (RegularRatioCocycle.projectiveRegularRatio_mul n j i j W hWj hWi).trans
    (RegularRatioCocycle.projectiveRegularRatio_self n j W hWj)
  inv_val := (RegularRatioCocycle.projectiveRegularRatio_mul n i j i W hWi hWj).trans
    (RegularRatioCocycle.projectiveRegularRatio_self n i W hWi)

def projectiveRegularLineCocycle (n : ℕ) : Regular.FunctionGluing.RegularLineCocycle (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (Fin (n + 1)) where
  domain := Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n
  covers := Foundations.Scheme.ProjectiveCoordinateCover.iSup_projectiveCoordinateOpen n
  transition := projectiveRegularTransition n
  restrict _ _ _ _ _ _ _ := rfl
  refl i W hi := by
    apply Units.ext
    exact RegularRatioCocycle.projectiveRegularRatio_self n i W hi
  cocycle i j k W hi hj hk := by
    apply Units.ext
    change RegularRatios.projectiveRegularRatio n j i W hj * RegularRatios.projectiveRegularRatio n k j W hk =
      RegularRatios.projectiveRegularRatio n k i W hk
    rw [mul_comm]
    exact RegularRatioCocycle.projectiveRegularRatio_mul n k j i W hk hj

/-- The native module sheaf is locally trivial by the constructed regular frames. -/
def projectiveAlgebraicLineBundle (n : ℕ) :
    Line.Bundles.AlgebraicLineBundle (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation :=
  Regular.LineBundle.regularCocycleAlgebraicLineBundle _ (projectiveRegularLineCocycle n)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RegularLineBundle
