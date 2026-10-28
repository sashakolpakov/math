import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionPullbackFrame
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineFramePullbackSquare
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterFamilySource

/-! # Torsion Parameter Line -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionParameterLine.Construction

noncomputable section

/-! The torsion Poincare family is the actual line on the base-changed
abelian scheme used by CartierDuality's parameterized character construction. Its
line class and multiplication-pullback frame retain the original data. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

def poincareTorsionParameterLine {Q : Over (Spec (.of k))} (t : Q ⟶ D.abelian.scheme) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback Q.hom).obj A.scheme).left :=
  (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t).pullback (pullbackSymmetry Q.hom A.scheme.hom).inv

omit [IsAlgClosed k] in
theorem poincareTorsionParameterLine_class {Q : Over (Spec (.of k))} (t : Q ⟶ D.abelian.scheme) :
    CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass A.scheme Q (poincareTorsionParameterLine D t) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A.scheme Q)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullbackSymmetry Q.hom A.scheme.hom).inv
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t))) = _
  rw [CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_eq_symmetry, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    Iso.hom_inv_id, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]

omit [IsAlgClosed k] in
theorem poincareParameterMultiplication_square (Q : Over (Spec (.of k))) (n : ℕ) :
    ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)).left ≫ (pullbackSymmetry Q.hom A.scheme.hom).inv =
      (pullbackSymmetry Q.hom A.scheme.hom).inv ≫ (TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n).left := by
  have hs := FrobeniusKernel.ParameterFamilySource.Construction.parameterFamilyMap_source ((𝟙 A.scheme) ^ n) Q
  rw [CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_eq_symmetry] at hs
  have hi := congrArg (fun f => (pullbackSymmetry Q.hom A.scheme.hom).inv ≫ f ≫
    (pullbackSymmetry Q.hom A.scheme.hom).inv) hs
  simpa [Category.assoc, TorsionPullbackFrame.Construction.poincareFamilyMultiplication] using hi.symm

def poincareTorsionParameterPullbackFrame {Q : Over (Spec (.of k))}
    (t : Q ⟶ D.abelian.scheme) (n : ℕ) (ht : t ^ n = 1) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback Q.hom).obj A.scheme).left ≅
      ((poincareTorsionParameterLine D t).pullback ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)).left).sheaf :=
  LineFramePullbackSquare.Construction.lineFramePullbackSquare (TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n).left
    ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)).left (pullbackSymmetry Q.hom A.scheme.hom).inv
    (poincareParameterMultiplication_square (A := A) Q n) (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t)
    (TorsionPullbackFrame.Construction.poincareTorsionFamilyPullbackFrame D t n ht)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.TorsionParameterLine.Construction
