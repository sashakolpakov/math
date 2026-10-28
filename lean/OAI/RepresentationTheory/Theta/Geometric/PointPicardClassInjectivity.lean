import OAI.RepresentationTheory.Theta.Geometric.PointBundleClasses
import OAI.RepresentationTheory.Theta.Geometric.Normalized.ParameterClassEquality
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

/-! # Point Picard Class Injectivity -/

namespace OAI.RepresentationTheory.Theta.Geometric.PointPicardClassInjectivity

noncomputable section

/-! Separation of the actual pointwise line bundles gives separation
in both the relative and homogeneous Picard sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem pointBundleClass_eq_of_parameterLineClass_eq {A P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left) (p q : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P)
    (h : ParameterizedPicardClass.parameterLineClass Q p = ParameterizedPicardClass.parameterLineClass Q q) : PointBundleClasses.pointBundleClass Q p = PointBundleClasses.pointBundleClass Q q := by
  let b := (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
  have H := congrArg (Picard.PicardPullback.picardPullback (PointBundleClasses.pointParameterMap (A := A) b).left) h
  have hp := PointBundleClasses.pointBundleClass_baseChange Q p b
  have hq := PointBundleClasses.pointBundleClass_baseChange Q q b
  exact hp.symm.trans (H.trans hq)

theorem parameterPicardClass_complex_injective {d : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    {P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (e : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    (hinj : Function.Injective (PointBundleClasses.pointBundleClass Q)) :
    Function.Injective (fun p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P => ParameterizedPicardClass.parameterPicardClass Q p) := by
  let : CompactSpace (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).left := inferInstanceAs (CompactSpace AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
  let : QuasiSeparatedSpace (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).left := inferInstanceAs (QuasiSeparatedSpace AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
  intro p q h
  apply hinj
  exact pointBundleClass_eq_of_parameterLineClass_eq Q p q
    ((Normalized.ParameterClassEquality.parameterPicard_eq_iff_lineClass_eq A Q e p q).mp h)

theorem parameterHomogeneousPicardClass_complex_injective {d : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    {P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (hQ : A.IsHomogeneousPicardClass P (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q))
    (hinj : Function.Injective (fun p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P => ParameterizedPicardClass.parameterPicardClass Q p)) :
    Function.Injective (fun p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P => ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass A Q hQ p) := by
  intro p q h
  apply hinj
  have H := congrArg (A.homogeneousPicardSheafInclusion.hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))) h
  simpa only [ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget] using H

end

end OAI.RepresentationTheory.Theta.Geometric.PointPicardClassInjectivity
