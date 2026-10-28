import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.FiniteTypePicardUniversality
import OAI.RepresentationTheory.Theta.Geometric.Dual.PicardData

/-! # All Test Picard Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The actual reference theta family represents the original homogeneous
Picard sheaf on every complex test scheme, including arbitrary nonreduced bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.Dual.PicardData

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP) (D : DualModel.ReferenceDualModel F hP)

theorem AlgebraicModel.ReferenceAlgebraicModel.referenceHomogeneousParameterMap_isIso
    (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (eQ : (Q.pullback (lift (𝟙 D.abelianScheme.scheme)
      (1 : D.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅
        HilbertConstruction.Line.Bundles.structureModule D.abelianScheme.scheme.left)
    (hinj : ∀ T : Over Foundations.Scheme.ProjectiveSpace.complexBase,
      Function.Injective (fun a : T ⟶ D.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q a))
    (hQ : M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme (HilbertConstruction.Line.Bundles.LineBundle.classOf Q))
    (hcomplex : Function.Surjective
      (fun a : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ D.abelianScheme.scheme =>
        RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass M.abelianScheme Q hQ a)) :
    IsIso (RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.homogeneousParameterMap M.abelianScheme Q hQ) := by
  let : IsProper M.abelian.toOver.hom := M.abelian.variety.presentation.projective.isProper
  let : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
  let : GeometricallyConnected M.abelian.toOver.hom := (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian).connected
  let : GeometricallyIntegral M.abelian.toOver.hom :=
    Quotients.FiniteDescent.AbelianGeometric.Construction.AbelianGeometricIntegral.geometricallyIntegral M.abelian.toOver
  let Qr : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine M.abelian.toOver D.abelianScheme.scheme := ⟨Q, eQ⟩
  exact RepresentationTheory.Theta.Geometric.HomogeneousPicardUniversality.homogeneousParameterMap_isIso M.abelian D.abelianScheme Qr hinj hQ hcomplex
    M.referenceStructureH1_finrank_le_dimension

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
