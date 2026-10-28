import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterLineKernel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.ClassKernel

/-! # Parameter Deformation Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterDeformationClass

noncomputable section

/-! The actual parameter-family infinitesimal class takes values in
the original algebraic H1 and detects distinct infinitesimal parameters. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {A P : Over Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P] [LocallyOfFiniteType A.hom] [IsReduced A.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ A).left))]
    (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left)
    (e : (Q.pullback (lift (1 : A ⟶ P) (𝟙 A)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule A.left)

def dualParameterDeformationClass (t : DualOpen.Lifts.DualSchemePoints P 1) : SheafCohomology.AffineH.Projective.H (HilbertConstruction.Line.Bundles.structureModule A.left) 1 :=
  DualLine.ClassKernel.dualLineKernelCohomology A (ParameterLineKernel.dualParameterLineKernel Q e t)

theorem dualParameterDeformationClass_injective
    (hinj : Function.Injective (fun t : LieRanks.dualNumberTest ℂ ⟶ P => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t)) :
    Function.Injective (dualParameterDeformationClass Q e) := by
  intro a b h
  apply ParameterLineKernel.dualParameterLineKernel_injective Q e hinj
  apply DualLine.ClassKernel.dualLineKernelClassHom_injective A
  exact congrArg Multiplicative.ofAdd h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterDeformationClass
