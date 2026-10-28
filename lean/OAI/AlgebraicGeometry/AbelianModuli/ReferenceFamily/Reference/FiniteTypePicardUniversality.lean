import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.StructureBound
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel
import OAI.RepresentationTheory.Theta.Geometric.Picard.FiniteTypeUniversality
import OAI.RepresentationTheory.Theta.Geometric.Picard.ComparisonParameter
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AbelianGeometric

/-! # Finite Type Picard Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The constructed algebraic H1 bound makes the actual reference
Picard comparison an isomorphism over every finite-type test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP) (D : DualModel.ReferenceDualModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.finiteTypePicard_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.finiteTypePicard_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance AlgebraicModel.ReferenceAlgebraicModel.finiteTypePicard_proper : IsProper M.abelian.toOver.hom :=
  M.abelian.variety.presentation.projective.isProper
local instance AlgebraicModel.ReferenceAlgebraicModel.finiteTypePicard_geometricallyIntegral : GeometricallyIntegral M.abelian.toOver.hom := by
  let : GeometricallyConnected M.abelian.toOver.hom := (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian).connected
  exact Quotients.FiniteDescent.AbelianGeometric.Construction.AbelianGeometricIntegral.geometricallyIntegral M.abelian.toOver

local instance AlgebraicModel.ReferenceAlgebraicModel.finiteTypePicard_testNoetherian (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType T.hom] :
    IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
local instance AlgebraicModel.ReferenceAlgebraicModel.finiteTypePicard_productNoetherian (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType T.hom] :
    IsLocallyNoetherian (D.abelianScheme.scheme ⊗ T).left := by
  let : LocallyOfFiniteType (snd D.abelianScheme.scheme T).left :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd D.abelianScheme.scheme.hom T.hom))
  exact LocallyOfFiniteType.isLocallyNoetherian (snd D.abelianScheme.scheme T).left

variable {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType T.hom]
    (Q : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine M.abelian.toOver D.abelianScheme.scheme)
    (L : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine M.abelian.toOver T)
    (hinj : ∀ U : Over Foundations.Scheme.ProjectiveSpace.complexBase, Function.Injective (Q.relativeValue (T := U)))
    (hQ : M.abelianScheme.IsHomogeneousPicardClass D.abelianScheme.scheme (HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle))
    (hL : M.abelianScheme.IsHomogeneousPicardClass T (HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle))
    (hcomplex : Function.Surjective
      (fun a : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ D.abelianScheme.scheme =>
        RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass M.abelianScheme Q.bundle hQ a))

include hL hcomplex hinj in
theorem AlgebraicModel.ReferenceAlgebraicModel.referencePicardParameterProjection_isIso :
    IsIso (RepresentationTheory.Theta.Geometric.Picard.ParameterComparison.picardParameterProjection Q L).left :=
  RepresentationTheory.Theta.Geometric.Picard.FiniteTypeUniversality.picardParameterProjection_isIso_of_complex_classification M.abelian D.abelianScheme Q L hinj
    hQ hL hcomplex M.referenceStructureH1_finrank_le_dimension

include hL hcomplex hinj in
theorem AlgebraicModel.ReferenceAlgebraicModel.exists_unique_finiteType_picard_parameter :
    ∃! a : T ⟶ D.abelianScheme.scheme, Q.relativeValue a = L.relativeValue (𝟙 T) := by
  let := M.referencePicardParameterProjection_isIso D Q L hinj hQ hL hcomplex
  exact RepresentationTheory.Theta.Geometric.Picard.ComparisonParameter.existsUnique_picard_parameter_of_comparison_isIso Q L (hinj T)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
