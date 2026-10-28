import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassScalarCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterDeformationClass

/-! # Parameter Class Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterClassScalars

noncomputable section

/-! The actual parameter deformation class respects native
precomposition by the dual-number scalar endomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

def dualPointScale {P : Over Foundations.Scheme.ProjectiveSpace.complexBase} [MonObj P] (c : ℂ) (t : DualOpen.Lifts.DualSchemePoints P 1) : DualOpen.Lifts.DualSchemePoints P 1 :=
  ⟨LieRanks.dualNumberScalar ℂ c ≫ t.val, by rw [← Category.assoc, Scalars.dualNumberScalar_origin, t.property]⟩

variable {A P : Over Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P] (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left)
    (e : (Q.pullback (lift (1 : A ⟶ P) (𝟙 A)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule A.left)

theorem dualParameterLineKernel_scalar (c : ℂ) (t : DualOpen.Lifts.DualSchemePoints P 1) :
    ParameterLineKernel.dualParameterLineKernel Q e (dualPointScale c t) = DualLine.KernelScalarPullback.dualLineKernelScalar A c (ParameterLineKernel.dualParameterLineKernel Q e t) :=
  Subtype.ext (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_naturality Q t.val (LieRanks.dualNumberScalar ℂ c)).symm

theorem dualParameterDeformationClass_scalar [LocallyOfFiniteType A.hom] [IsReduced A.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ A).left))]
    (c : ℂ) (t : DualOpen.Lifts.DualSchemePoints P 1) :
    let := StructureComplexScalars.structureH1ComplexModule A
    ParameterDeformationClass.dualParameterDeformationClass Q e (dualPointScale c t) = c • ParameterDeformationClass.dualParameterDeformationClass Q e t := by
  let := StructureComplexScalars.structureH1ComplexModule A
  exact (congrArg (DualLine.ClassKernel.dualLineKernelCohomology A) (dualParameterLineKernel_scalar Q e c t)).trans
    (DualLine.ClassScalarCompatibility.dualLineKernelCohomology_scalar A c (ParameterLineKernel.dualParameterLineKernel Q e t))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterClassScalars
