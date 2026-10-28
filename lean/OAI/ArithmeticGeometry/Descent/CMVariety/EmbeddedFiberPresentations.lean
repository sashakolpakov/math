import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedAbelianVarieties
import OAI.ArithmeticGeometry.Descent.CMVariety.StandardModuli
import OAI.ArithmeticGeometry.Descent.CMVariety.PulledBackPresentations

/-! # Embedded Fiber Presentations -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.EmbeddedFiberPresentations.Abelian

noncomputable section

/-! The retained projective embedding supplies actual complex abelian
presentations at every point of the arithmetic family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedAbelianVarieties

def embeddedAbelianFiberPresentation
    {R : Type} [CommRing R] {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of R)))
    (n : ℕ) (i : A.scheme ⟶ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n) [IsClosedImmersion i.left]
    (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of R)) : StandardModuli.Abelian.ComplexAbelianPresentation (A.pullback p) := by
  let φ : R →+* ℂ := (Spec.preimage p).hom
  have hp : Spec.map (CommRingCat.ofHom φ) = p := Spec.map_preimage p
  let F := Over.pullback p
  let G := (A.pullback p).scheme
  let eP : F.obj (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n) ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ n :=
    Models.Scheme.Constructions.Foundations.baseChangeCongr hp.symm _ ≪≫ (AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientModels.Coefficients.affineProjectiveBaseChangeIso φ n).symm
  have : IsIso eP.hom.left := ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).mapIso eP).isIso_hom
  have : IsClosedImmersion (F.map i).left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) p i inferInstance
  let j : G ⟶ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace ℂ n := F.map i ≫ eP.hom
  have : IsClosedImmersion j.left :=
    inferInstanceAs (IsClosedImmersion ((F.map i).left ≫ eP.hom.left))
  let B := AlgebraicGeometry.PELModuli.IntegralModel.EmbeddedAbelianVarieties.embeddedAbelianVariety G n j
  exact {
    variety := B
    comparison := Iso.refl G
    comparison_group := inferInstanceAs (IsMonHom (𝟙 G)) }

end

end OAI.ArithmeticGeometry.Descent.CMVariety.EmbeddedFiberPresentations.Abelian
