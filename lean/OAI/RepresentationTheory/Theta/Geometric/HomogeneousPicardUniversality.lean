import OAI.RepresentationTheory.Theta.Geometric.HomogeneousPicardLocalSurjectivity
import OAI.RepresentationTheory.Theta.Geometric.HomogeneousParameterEmbedding
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Homogeneous Picard Universality -/

namespace OAI.RepresentationTheory.Theta.Geometric.HomogeneousPicardUniversality

noncomputable section

/-! The actual homogeneous parameter map is an isomorphism of sheaves
on all complex test schemes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem homogeneousParameterMap_isIso (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    [IsProper A.toOver.hom] [Smooth A.toOver.hom] [GeometricallyIntegral A.toOver.hom]
    {n : ℕ} (N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (Q : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver N.scheme)
    (hQ : ∀ U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, Function.Injective (Q.relativeValue (T := U)))
    (hhomQ : (AbelianScheme.abelianSchemeOfVariety A).IsHomogeneousPicardClass N.scheme (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle))
    (hcomplex : Function.Surjective
      (fun a : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ N.scheme =>
        ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ a))
    (hH1 : letI := AlgebraicGeometry.SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
      Module.finrank ℂ (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1) ≤ n) :
    IsIso (ParameterizedHomogeneousPicard.homogeneousParameterMap (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ) := by
  let J := Scheme.fppfTopology.over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase
  let f : J.uliftYoneda.{1}.obj N.scheme ⟶ (AbelianScheme.abelianSchemeOfVariety A).homogeneousPicardSheaf :=
    ⟨ParameterizedHomogeneousPicard.homogeneousParameterMap (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ⟩
  have hm : Mono f.hom := HomogeneousParameterEmbedding.homogeneousParameterMap_mono (AbelianScheme.abelianSchemeOfVariety A)
    Q.bundle hhomQ hQ
  have : Mono f := (sheafToPresheaf _ _).mono_of_mono_map hm
  have : Presheaf.IsLocallySurjective J f.hom :=
    HomogeneousPicardLocalSurjectivity.homogeneousParameterMap_locallySurjective A N Q hQ hhomQ hcomplex hH1
  have : IsIso f := isIso_of_mono_of_epi f
  exact inferInstanceAs (IsIso ((sheafToPresheaf _ _).map f))

end

end OAI.RepresentationTheory.Theta.Geometric.HomogeneousPicardUniversality
