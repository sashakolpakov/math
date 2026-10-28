import OAI.AlgebraicGeometry.Picard.ThetaConstruction.Homomorphism
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.InfinitesimalKernel
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualPointSeparation
import OAI.RepresentationTheory.Theta.Geometric.Dual.PicardInjectivity

/-! # Dual Injectivity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual descended lattice-dual Picard family separates every
pair of native dual-number parameters, at every complex base point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel F} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel F}

open OAI.RepresentationTheory.Theta.Geometric.Dual.PicardInjectivity

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.parameterPicardClass_dual_injective (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP)) (hdeg : V.degree = U.degree + 1)
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ z, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period z) = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension
      (U.projectiveMap z))
    (hg' : ∀ z, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period z) = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension
      (V.projectiveMap z))
    (hcube : RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)) = 1)
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)).sheaf)
    (eA : (Q.pullback (lift (𝟙 N.abelianScheme.scheme)
      (1 : N.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule N.abelianScheme.scheme.left)
    (eB : (Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ N.abelianScheme.scheme)
      (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left) :
    Function.Injective (fun t : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ N.abelianScheme.scheme => RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q t) := by
  apply RepresentationTheory.Theta.Geometric.Dual.PicardInjectivity.parameterPicardClass_dual_injective_of_hom Q
    (p.parameterPicardHom (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) hcube Q recover (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ))
    (fun _ => rfl)
  · exact RepresentationTheory.Theta.Geometric.PointPicardClassInjectivity.parameterPicardClass_complex_injective M.abelianScheme Q eA
      (p.pointBundleClass_injective hP U V hdeg f g hf hg' hcube Q recover)
  · exact p.parameterPicardClass_infinitesimal_kernel_trivial U V hdeg f g hf hg' Q recover eA eB

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
