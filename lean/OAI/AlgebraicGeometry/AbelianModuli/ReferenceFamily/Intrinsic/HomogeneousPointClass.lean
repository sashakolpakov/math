import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPointLine
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClosedSheafification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Picard

/-! # Homogeneous Point Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousPointClass

noncomputable section

/-! An actual homogeneous family gives sections of the original
homogeneous Picard sheaf at complex parameter points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {d : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme d Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (hQ : A.IsHomogeneousPicardClass P (HilbertConstruction.Line.Bundles.LineBundle.classOf Q))

def nativeHomogeneousPointFamilyClass (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) :
    A.homogeneousPicardPresheaf.obj (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) :=
  ⟨HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (x ⊗ₘ 𝟙 A.scheme).left), hQ.pullback A x⟩

def nativeHomogeneousPointPicardClass (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) :
    A.homogeneousPicardSheaf.obj.obj (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) :=
  (toSheafify (Scheme.fppfTopology.over Foundations.Scheme.ProjectiveSpace.complexBase) A.homogeneousPicardPresheaf).app
    (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) (nativeHomogeneousPointFamilyClass A Q hQ x)

theorem nativeHomogeneousPointPicardClass_eq_iff (x y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) :
    nativeHomogeneousPointPicardClass A Q hQ x = nativeHomogeneousPointPicardClass A Q hQ y ↔
      HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (x ⊗ₘ 𝟙 A.scheme).left) =
        HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (y ⊗ₘ 𝟙 A.scheme).left) := by
  constructor
  · intro h
    exact congrArg Subtype.val ((ClosedSheafification.fppf_toSheafify_bijective_at_algClosed (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
      A.homogeneousPicardPresheaf).injective h)
  · intro h
    exact congrArg ((toSheafify (Scheme.fppfTopology.over Foundations.Scheme.ProjectiveSpace.complexBase) A.homogeneousPicardPresheaf).app
      (.op (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))) (Subtype.ext h)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousPointClass
