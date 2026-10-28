import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ParameterLineMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterDeformationClass

/-! # Parameter Class Addition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterClassAddition

noncomputable section

/-! The actual cohomology class of a normalized parameter family
adds under multiplication of its original dual-number test points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

def dualPointProduct {P : Over Foundations.Scheme.ProjectiveSpace.complexBase} [MonObj P] (x y : DualOpen.Lifts.DualSchemePoints P 1) : DualOpen.Lifts.DualSchemePoints P 1 :=
  ⟨x.val * y.val, by rw [MonObj.comp_mul, x.property, y.property, one_mul]⟩

variable {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eP : (Q.pullback (lift (1 : A.scheme ⟶ P) (𝟙 A.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule A.scheme.left)
    (eA : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule P.left)

include eA in
theorem dualParameterLineKernel_mul (x y : DualOpen.Lifts.DualSchemePoints P 1)
    (h : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (x.val * y.val) =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q x.val * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q y.val) :
    ParameterLineKernel.dualParameterLineKernel Q eP (dualPointProduct x y) =
      ParameterLineKernel.dualParameterLineKernel Q eP x * ParameterLineKernel.dualParameterLineKernel Q eP y := by
  let : CompactSpace (LieRanks.dualNumberTest ℂ).left := inferInstanceAs (CompactSpace (Spec (.of (DualNumber ℂ))))
  let : QuasiSeparatedSpace (LieRanks.dualNumberTest ℂ).left :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of (DualNumber ℂ))))
  exact Subtype.ext (ParameterLineMultiplication.parameterLineClass_mul_of_picard A Q eA x.val y.val h)

variable [LocallyOfFiniteType A.scheme.hom] [IsReduced A.scheme.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ A.scheme).left))]

include eA in
theorem dualParameterDeformationClass_mul (x y : DualOpen.Lifts.DualSchemePoints P 1)
    (h : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (x.val * y.val) =
      RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q x.val * RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q y.val) :
    ParameterDeformationClass.dualParameterDeformationClass Q eP (dualPointProduct x y) =
      ParameterDeformationClass.dualParameterDeformationClass Q eP x + ParameterDeformationClass.dualParameterDeformationClass Q eP y :=
  (congrArg (DualLine.ClassKernel.dualLineKernelCohomology A.scheme) (dualParameterLineKernel_mul A Q eP eA x y h)).trans
    (DualLine.ClassKernel.dualLineKernelCohomology_mul A.scheme (ParameterLineKernel.dualParameterLineKernel Q eP x) (ParameterLineKernel.dualParameterLineKernel Q eP y))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ParameterClassAddition
