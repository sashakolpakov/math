import OAI.AlgebraicGeometry.Picard.ThetaConstruction.Infinitesimal
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.InfinitesimalLift

/-! # Infinitesimal Kernel -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual descended Picard family has no nontrivial native
dual-number point in its infinitesimal kernel at the origin. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel F} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel F}

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.parameterPicardClass_infinitesimal_kernel_trivial (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (PolarizationFactor.Geometric.polarizationFactor F hP)) (hdeg : V.degree = U.degree + 1)
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ z, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period z) = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension
      (U.projectiveMap z))
    (hg' : ∀ z, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period z) = ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension
      (V.projectiveMap z))
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)).sheaf)
    (eA : (Q.pullback (lift (𝟙 N.abelianScheme.scheme)
      (1 : N.abelianScheme.scheme ⟶ M.abelianScheme.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule N.abelianScheme.scheme.left)
    (eB : (Q.pullback (lift (1 : M.abelianScheme.scheme ⟶ N.abelianScheme.scheme)
      (𝟙 M.abelianScheme.scheme)).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule M.abelianScheme.scheme.left)
    (v : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints N.abelian.toOver 1)
    (hv : RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q v.val = RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q
      (1 : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ N.abelianScheme.scheme)) : v.val = 1 := by
  obtain ⟨r, hr, ⟨u⟩⟩ := p.exists_infinitesimal_translation_comparison
    (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left) Q recover eA eB v hv
  have hr0 := M.nativeInfinitesimalTheta_eq_one U V hdeg f g hf hg' r u
  rw [hr0, MonObj.one_comp] at hr
  exact hr.symm

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
