import OAI.RepresentationTheory.Theta.Geometric.DescendedPicardHomomorphism
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualDifferenceDescent

/-! # Homomorphism -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual lattice-dual Picard parameter map is a group homomorphism
on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel F} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel F}

open OAI.RepresentationTheory.Theta.Geometric.DescendedPicardHomomorphism

def IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.parameterPicardHom (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
    (hcube : RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1)
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf)
    (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) : (T ⟶ N.abelianScheme.scheme) →* AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections M.abelianScheme.scheme T :=
  RepresentationTheory.Theta.Geometric.DescendedPicardHomomorphism.descendedParameterPicardHom M.abelianScheme p.isogeny.hom L
    (fun _ a b c => RepresentationTheory.Theta.Geometric.Cubical.ClassPullback.nativeCubeClass_pullback M.abelian (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) hcube a b c) Q recover T

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
