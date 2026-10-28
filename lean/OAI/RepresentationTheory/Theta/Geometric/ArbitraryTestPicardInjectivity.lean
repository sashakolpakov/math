import OAI.RepresentationTheory.Theta.Geometric.ArbitraryTestPicardKernel
import OAI.RepresentationTheory.Theta.Geometric.Picard.HomKernelInjectivity

/-! # Arbitrary Test Picard Injectivity -/

namespace OAI.RepresentationTheory.Theta.Geometric.ArbitraryTestPicardInjectivity

noncomputable section

/-! The additive normalized Picard family separates arbitrary
complex test schemes, with no finiteness or reducedness restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem parameterPicardClass_arbitraryTest_injective
    {n : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj P]
    [LocallyOfFiniteType P.hom] [IsSeparated P.hom]
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eQ : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    (hinj : Function.Injective (fun t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t))
    (hpoints : Function.Injective (fun t : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P => ParameterizedPicardClass.parameterPicardClass Q t))
    (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (rho : (T ⟶ P) →* AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A.scheme T)
    (hrho : ∀ r, rho r = ParameterizedPicardClass.parameterPicardClass Q r) :
    Function.Injective (fun r : T ⟶ P => ParameterizedPicardClass.parameterPicardClass Q r) :=
  Picard.HomKernelInjectivity.parameterPicardClass_injective_of_hom_kernel Q rho hrho
    (ArbitraryTestPicardKernel.parameterPicardClass_arbitraryTest_kernel A Q eQ hinj hpoints T)

end

end OAI.RepresentationTheory.Theta.Geometric.ArbitraryTestPicardInjectivity
