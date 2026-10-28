import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.FamilyScalarFrame
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DescentComposite
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DescentFrameRatio
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions

/-! # Family Scalar Ratio -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.FamilyScalarRatio.Construction

noncomputable section

/-! The scalar of the torsion Poincare family is the ratio of its
actual scalar frames, evaluated in their common Poincare fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {Q : Over (Spec (.of k))} [IsAffine Q.left]
  (t : Q ⟶ D.abelian.scheme) (n : ℕ) (ht : t ^ n = 1)

omit [IsAlgClosed k] [IsAffine Q.left] in
theorem poincareFamilyMultiplication_parameter {R : Over (Spec (.of k))}
    (q x : R ⟶ Q ⊗ A.scheme) (hx : x ≫ TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n = q) :
    x ≫ fst Q A.scheme = q ≫ fst Q A.scheme := by
  have h := congrArg (fun a => a ≫ fst Q A.scheme) hx
  simpa only [Category.assoc, TorsionPullbackFrame.Construction.poincareFamilyMultiplication, tensorHom_fst, Category.comp_id] using h

omit [IsAlgClosed k] [IsAffine Q.left] in
theorem poincareFamilyScalarPoint_of_image {R : Over (Spec (.of k))}
    (q x : R ⟶ Q ⊗ A.scheme) (hx : x ≫ TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n = q) :
    x ≫ FamilyScalarFrame.Construction.poincareFamilyScalarPoint D t n = q ≫ lift (fst Q A.scheme ≫ t) (snd Q A.scheme) := by
  unfold FamilyScalarFrame.Construction.poincareFamilyScalarPoint
  rw [← TorsionPullbackFrame.Construction.poincareFamilyMultiplication_point D t n, ← Category.assoc, hx]

set_option backward.isDefEq.respectTransparency false in
theorem poincareFamilyDescentScalar_frameRatio {R : Over (Spec (.of k))}
    (q x y : R ⟶ Q ⊗ A.scheme)
    (hx : x ≫ TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n = q)
    (hy : y ≫ TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n = q) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n).left
      (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t).sheaf) (TorsionPullbackFrame.Construction.poincareTorsionFamilyPullbackFrame D t n ht).symm
      q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (Picard.PoincareBundle.Line.FrameUnits.frameRatio
      (Picard.PoincareBundle.GlobalPullbackFrame.atPoint (FamilyScalarFrame.Construction.poincareFamilyScalarPoint D t n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
        (FamilyScalarFrame.Construction.poincareFamilyScalarFrame D t n ht) x
        (q ≫ lift (fst Q A.scheme ≫ t) (snd Q A.scheme))
        (poincareFamilyScalarPoint_of_image D t n q x hx))
      (Picard.PoincareBundle.GlobalPullbackFrame.atPoint (FamilyScalarFrame.Construction.poincareFamilyScalarPoint D t n) (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
        (FamilyScalarFrame.Construction.poincareFamilyScalarFrame D t n ht) y
        (q ≫ lift (fst Q A.scheme ≫ t) (snd Q A.scheme))
        (poincareFamilyScalarPoint_of_image D t n q y hy)) : Γ(R.left, ⊤)) := by
  have : IsIso (fst Q A.scheme).left.appTop := Picard.Homomorphisms.ProperGroupFunctions.Construction.properGroupProduct_appTop_isIso A.scheme Q
  have hb : x ≫ fst Q A.scheme = y ≫ fst Q A.scheme :=
    (poincareFamilyMultiplication_parameter n q x hx).trans
      (poincareFamilyMultiplication_parameter n q y hy).symm
  have hc := Canonical.DescentComposite.Construction.canonicalDescentScalar_composite (fst Q A.scheme).left
    (ConcreteCategory.bijective_of_isIso (fst Q A.scheme).left.appTop).surjective
    (TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n).left
    (lift (fst Q A.scheme ≫ t) (snd Q A.scheme)).left
    (FamilyScalarFrame.Construction.poincareFamilyScalarPoint D t n).left
    (congrArg Over.Hom.left (TorsionPullbackFrame.Construction.poincareFamilyMultiplication_point D t n)) D.poincare
    (FamilyScalarFrame.Construction.poincareFamilyScalarFrame D t n ht).symm (TorsionPullbackFrame.Construction.poincareTorsionFamilyPullbackFrame D t n ht).symm
    q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy)
    (congrArg Over.Hom.left hb)
  exact hc.trans (Canonical.DescentFrameRatio.Construction.canonicalDescentScalar_eq_frameRatio (FamilyScalarFrame.Construction.poincareFamilyScalarPoint D t n) D.poincare
    (FamilyScalarFrame.Construction.poincareFamilyScalarFrame D t n ht) (q ≫ lift (fst Q A.scheme ≫ t) (snd Q A.scheme)) x y
    (poincareFamilyScalarPoint_of_image D t n q x hx) (poincareFamilyScalarPoint_of_image D t n q y hy))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.FamilyScalarRatio.Construction
