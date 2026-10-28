import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ParameterTangentCohomology
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterClassScalars
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality

/-! # Parameter Tangent Linear -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ParameterTangentLinear

noncomputable section

/-! The actual normalized Picard parameter family induces a
complex-linear injective map from its native tangent space to algebraic H1. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    [IsIntegral P.left] [Smooth P.hom] [LocallyOfFiniteType A.scheme.hom] [IsReduced A.scheme.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ A.scheme).left))]
    (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eP : (Q.pullback (lift (1 : A.scheme ⟶ P) (𝟙 A.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

local notation "ModelP" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension P.hom) → ℂ)
local instance nativeParameterH1ComplexModule : Module ℂ (SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1) :=
  StructureComplexScalars.structureH1ComplexModule A.scheme

theorem nativeParameterTangentClass_smul (c : ℂ) (v : ModelP) :
    ParameterTangentCohomology.nativeParameterTangentClass A Q eP (c • v) = c • ParameterTangentCohomology.nativeParameterTangentClass A Q eP v := by
  have h : SchemeDualTangent.nativeSchemeTangentDualEquiv P 1 (c • v) = Dual.ParameterClassScalars.dualPointScale c (SchemeDualTangent.nativeSchemeTangentDualEquiv P 1 v) :=
    Subtype.ext (SchemeDualNaturality.nativeSchemeTangentDual_scale P 1 c v)
  exact (congrArg (Dual.ParameterDeformationClass.dualParameterDeformationClass Q eP) h).trans (Dual.ParameterClassScalars.dualParameterDeformationClass_scalar Q eP c _)

def nativeParameterTangentLinear
    (eA : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule P.left)
    (hmul : ∀ x y : LieRanks.dualNumberTest ℂ ⟶ P,
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (x * y) = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q x * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q y) :
    ModelP →ₗ[ℂ] SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1 where
  toFun := ParameterTangentCohomology.nativeParameterTangentClass A Q eP
  map_add' := ParameterTangentCohomology.nativeParameterTangentClass_add A Q eP eA hmul
  map_smul' := nativeParameterTangentClass_smul A Q eP

theorem nativeParameterTangentLinear_injective
    (eA : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule P.left)
    (hmul : ∀ x y : LieRanks.dualNumberTest ℂ ⟶ P,
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (x * y) = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q x * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q y)
    (hinj : Function.Injective (fun t : LieRanks.dualNumberTest ℂ ⟶ P => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t)) :
    Function.Injective (nativeParameterTangentLinear A Q eP eA hmul) :=
  ParameterTangentCohomology.nativeParameterTangentClass_injective A Q eP hinj

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ParameterTangentLinear
