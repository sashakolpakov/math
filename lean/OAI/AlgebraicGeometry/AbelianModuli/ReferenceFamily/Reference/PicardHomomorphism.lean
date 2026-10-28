import OAI.RepresentationTheory.Theta.Geometric.DescendedPicardHomomorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DifferenceDescent

/-! # Picard Homomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! The actual lattice-dual Picard parameter map is a group homomorphism
on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {N : DualModel.ReferenceDualModel F hP}

open OAI.RepresentationTheory.Theta.Geometric.DescendedPicardHomomorphism

def IsogenyKernel.ReferenceLatticeIsogeny.parameterPicardHom (p : IsogenyKernel.ReferenceLatticeIsogeny M N)
    (L : HilbertConstruction.Line.Bundles.LineBundle M.abelianScheme.scheme.left)
    (hcube : RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass.nativeCubeDefect M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1)
    (Q : HilbertConstruction.Line.Bundles.LineBundle (N.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme L).sheaf)
    (T : Over Foundations.Scheme.ProjectiveSpace.complexBase) : (T ⟶ N.abelianScheme.scheme) →* HilbertConstruction.Picard.PicardSheaf.PicardSections M.abelianScheme.scheme T :=
  RepresentationTheory.Theta.Geometric.DescendedPicardHomomorphism.descendedParameterPicardHom M.abelianScheme p.isogeny.hom L
    (fun _ a b c => RepresentationTheory.Theta.Geometric.Cubical.ClassPullback.nativeCubeClass_pullback M.abelian (HilbertConstruction.Line.Bundles.LineBundle.classOf L) hcube a b c) Q recover T

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
