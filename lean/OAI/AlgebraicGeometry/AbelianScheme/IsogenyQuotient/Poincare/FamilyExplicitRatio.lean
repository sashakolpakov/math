import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.FamilyScalarRatio
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ScalarFrameTarget

/-! # Family Explicit Ratio -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.FamilyExplicitRatio.Construction

noncomputable section

/-! An explicit ratio of torsion Poincare scalar frames computes the
family descent scalar at any prescribed common target point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {Q : Over (Spec (.of k))} [IsAffine Q.left]
  (t : Q ⟶ D.abelian.scheme) (n : ℕ) (ht : t ^ n = 1)

theorem poincareFamilyDescentScalar_explicit {R : Over (Spec (.of k))}
    (q x y : R ⟶ Q ⊗ A.scheme)
    (hx : x ≫ TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n = q)
    (hy : y ≫ TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n = q)
    (r : R ⟶ D.abelian.scheme ⊗ A.scheme)
    (hr : q ≫ lift (fst Q A.scheme ≫ t) (snd Q A.scheme) = r) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (TorsionPullbackFrame.Construction.poincareFamilyMultiplication (A := A) Q n).left
      (TorsionPullbackFrame.Construction.poincareTorsionFamilyLine D t).sheaf) (TorsionPullbackFrame.Construction.poincareTorsionFamilyPullbackFrame D t n ht).symm
      q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (Picard.PoincareBundle.Line.FrameUnits.frameRatio
      (ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo D n (x ≫ fst Q A.scheme ≫ t) (x ≫ snd Q A.scheme)
        (FamilyScalarFrame.Construction.poincareFamilyDualCoordinate_pow D t n ht x) r
        ((FamilyScalarFrame.Construction.poincareFamilyScalarPoint_comp D t n x).symm.trans
          ((FamilyScalarRatio.Construction.poincareFamilyScalarPoint_of_image D t n q x hx).trans hr)))
      (ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo D n (y ≫ fst Q A.scheme ≫ t) (y ≫ snd Q A.scheme)
        (FamilyScalarFrame.Construction.poincareFamilyDualCoordinate_pow D t n ht y) r
        ((FamilyScalarFrame.Construction.poincareFamilyScalarPoint_comp D t n y).symm.trans
          ((FamilyScalarRatio.Construction.poincareFamilyScalarPoint_of_image D t n q y hy).trans hr))) : Γ(R.left, ⊤)) := by
  cases hr
  exact (FamilyScalarRatio.Construction.poincareFamilyDescentScalar_frameRatio D t n ht q x y hx hy).trans
    (congrArg Units.val (congrArg₂ Picard.PoincareBundle.Line.FrameUnits.frameRatio
      (ScalarFrameTarget.Construction.poincareFamilyScalarFrame_atPoint_explicit D n t ht x _
        (FamilyScalarRatio.Construction.poincareFamilyScalarPoint_of_image D t n q x hx))
      (ScalarFrameTarget.Construction.poincareFamilyScalarFrame_atPoint_explicit D n t ht y _
        (FamilyScalarRatio.Construction.poincareFamilyScalarPoint_of_image D t n q y hy))))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.FamilyExplicitRatio.Construction
