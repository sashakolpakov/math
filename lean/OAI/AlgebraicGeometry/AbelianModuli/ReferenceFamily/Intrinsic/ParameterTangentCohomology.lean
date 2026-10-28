import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterClassAddition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualAddition

/-! # Parameter Tangent Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ParameterTangentCohomology

noncomputable section

/-! The actual parameter family's native tangent map takes values
in algebraic H1, preserves addition, and detects tangent directions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    [IsIntegral P.left] [Smooth P.hom] [LocallyOfFiniteType A.scheme.hom] [IsReduced A.scheme.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ A.scheme).left))]
    (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eP : (Q.pullback (lift (1 : A.scheme ⟶ P) (𝟙 A.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

local notation "ModelP" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension P.hom) → ℂ)

def nativeParameterTangentClass (v : ModelP) : SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.scheme.left) 1 :=
  Dual.ParameterDeformationClass.dualParameterDeformationClass Q eP (SchemeDualTangent.nativeSchemeTangentDualEquiv P 1 v)

theorem nativeParameterTangentClass_add
    (eA : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule P.left)
    (hmul : ∀ x y : LieRanks.dualNumberTest ℂ ⟶ P,
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (x * y) = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q x * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q y)
    (u v : ModelP) : nativeParameterTangentClass A Q eP (u + v) =
      nativeParameterTangentClass A Q eP u + nativeParameterTangentClass A Q eP v := by
  have h : SchemeDualTangent.nativeSchemeTangentDualEquiv P 1 (u + v) =
      Dual.ParameterClassAddition.dualPointProduct (SchemeDualTangent.nativeSchemeTangentDualEquiv P 1 u) (SchemeDualTangent.nativeSchemeTangentDualEquiv P 1 v) :=
    Subtype.ext (SchemeDualAddition.nativeSchemeTangentDual_add P u v)
  exact (congrArg (Dual.ParameterDeformationClass.dualParameterDeformationClass Q eP) h).trans
    (Dual.ParameterClassAddition.dualParameterDeformationClass_mul A Q eP eA _ _ (hmul _ _))

theorem nativeParameterTangentClass_injective
    (hinj : Function.Injective (fun t : LieRanks.dualNumberTest ℂ ⟶ P => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t)) :
    Function.Injective (nativeParameterTangentClass A Q eP) :=
  (Dual.ParameterDeformationClass.dualParameterDeformationClass_injective Q eP hinj).comp (SchemeDualTangent.nativeSchemeTangentDualEquiv P 1).injective

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ParameterTangentCohomology
