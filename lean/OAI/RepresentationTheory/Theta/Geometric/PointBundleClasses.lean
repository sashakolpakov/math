import OAI.RepresentationTheory.Theta.Geometric.DifferencePicardClasses
import OAI.RepresentationTheory.Theta.Geometric.ConstantPicardPullback
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicTranslation

/-! # Point Bundle Classes -/

namespace OAI.RepresentationTheory.Theta.Geometric.PointBundleClasses

noncomputable section

/-! Actual line classes on an abelian variety obtained by fixing a
complex parameter, with recovery from the native difference bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

def pointParameterMap {A P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) : A ⟶ P ⊗ A :=
  lift (Over.mkIdTerminal.from A ≫ p) (𝟙 A)

def pointBundleClass {A P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.left :=
  Picard.PicardPullback.picardPullback (pointParameterMap (A := A) p).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q)

theorem pointParameterMap_baseChange {A P R : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : P ⟶ R) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) :
    pointParameterMap (A := A) p ≫ (f ⊗ₘ 𝟙 A) = pointParameterMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [pointParameterMap, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map]

theorem pointBundleClass_baseChange {A P R : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (R ⊗ A).left) (f : P ⟶ R) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) :
    pointBundleClass (Q.pullback (f ⊗ₘ 𝟙 A).left) p = pointBundleClass Q (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) := by
  unfold pointBundleClass
  rw [show AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (f ⊗ₘ 𝟙 A).left) =
    Picard.PicardPullback.picardPullback (f ⊗ₘ 𝟙 A).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) from rfl, Picard.PicardPullback.picardPullback_comp]
  exact congrArg (fun h => Picard.PicardPullback.picardPullback h (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q))
    (congrArg Over.Hom.left (pointParameterMap_baseChange f p))

theorem pointBundleClass_congr {A P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q R : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left) (e : Q.sheaf ≅ R.sheaf) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P) :
    pointBundleClass Q p = pointBundleClass R p :=
  congrArg (Picard.PicardPullback.picardPullback (pointParameterMap (A := A) p).left) (Quotient.sound ⟨e⟩)

theorem pointDifferenceBundle_class {d : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.scheme) :
    pointBundleClass (AbelianDifferenceBundle.abelianDifferenceBundle A L) p =
      Picard.PicardPullback.picardPullback (DifferenceBundleTranslation.groupTranslation A.scheme p).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)⁻¹ := by
  have H := Picard.PicardPullback.algebraicDifferenceBundle_pullback_class L (fst A.scheme A.scheme).left
    (snd A.scheme A.scheme).left μ[A.scheme].left (pointParameterMap p).left
  have hmul : pointParameterMap p ≫ μ[A.scheme] = DifferenceBundleTranslation.groupTranslation A.scheme p := by
    change lift (Over.mkIdTerminal.from A.scheme ≫ p) (𝟙 A.scheme) ≫ μ[A.scheme] =
      (𝟙 A.scheme) * (Over.mkIdTerminal.from A.scheme ≫ p)
    exact mul_comm _ _
  have hfst : pointParameterMap p ≫ fst A.scheme A.scheme = Over.mkIdTerminal.from A.scheme ≫ p :=
    lift_fst _ _
  have hsnd : pointParameterMap p ≫ snd A.scheme A.scheme = 𝟙 A.scheme := lift_snd _ _
  rw [show (pointParameterMap p).left ≫ μ[A.scheme].left = (DifferenceBundleTranslation.groupTranslation A.scheme p).left from
    congrArg Over.Hom.left hmul,
    show (pointParameterMap p).left ≫ (fst A.scheme A.scheme).left =
      (Over.mkIdTerminal.from A.scheme).left ≫ p.left from congrArg Over.Hom.left hfst,
    show (pointParameterMap p).left ≫ (snd A.scheme A.scheme).left = 𝟙 A.scheme.left from
      congrArg Over.Hom.left hsnd,
    ConstantPicardPullback.picardPullback_constant ℂ, inv_one, mul_one, Picard.PicardPullback.picardPullback_id] at H
  exact H

end

end OAI.RepresentationTheory.Theta.Geometric.PointBundleClasses
