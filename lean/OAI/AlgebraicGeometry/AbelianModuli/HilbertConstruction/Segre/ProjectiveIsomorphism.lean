import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProductLocalComparison

/-! # Projective Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectiveIsomorphism

noncomputable section

/-! The projective rank-one matrix scheme is the product of the two projective spaces. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) (n m : ℕ)

instance segreToProduct_isIso : IsIso (ProductComparison.segreToProduct R n m) := by
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme)
    (Projective.ProductChartCover.projectiveProductOpenCover R n m)).mpr
  intro p
  change ChartProjections.SegreProjectiveIndex.{u} n m at p
  have h := (ProductLocalComparison.segreToProduct_chart_isPullback R p).flip
  have hc : IsIso (h.isoPullback.inv ≫ (ProductChartScheme.segreProductChartSchemeIso R p).hom) := inferInstance
  change IsIso (pullback.snd (ProductComparison.segreToProduct R n m) (Projective.ProductChartCover.projectiveProductChartMap R p))
  exact (congrArg (fun f => IsIso f) h.isoPullback_inv_snd).mp hc

def segreProductSchemeIso : ProductComparison.segreEquationScheme R n m ≅
    pullback (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom (Projective.ProjectivePresentations.affineProjectiveSpace R m).hom :=
  asIso (ProductComparison.segreToProduct R n m)

def affineSegreEmbedding :
    pullback (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom (Projective.ProjectivePresentations.affineProjectiveSpace R m).hom ⟶
      Proj (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (ChartProjections.SegreProjectiveIndex.{u} n m) R) :=
  (segreProductSchemeIso R n m).inv ≫ ProjectiveScheme.segreProjectiveInclusion R

instance affineSegreEmbedding_isClosedImmersion : IsClosedImmersion (affineSegreEmbedding R n m) := by
  change IsClosedImmersion ((segreProductSchemeIso R n m).inv ≫ ProjectiveScheme.segreProjectiveInclusion R)
  exact IsClosedImmersion.comp _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectiveIsomorphism
