import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismSourcePolynomial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.GraphFiberCoordinates
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.BoundedEndomorphismTuples

/-! # Automorphism Presentations Graphs -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismPresentationsGraphs

noncomputable section

/-! The exact Presentations graph predicate holds for polarized automorphisms on
every test scheme lying in the corresponding source-polynomial stratum. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    {n : ℕ} (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left)
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.abelian.scheme ⨯ A.abelian.scheme))
    (hB : HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he)
      (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) B)

include hP hB in
theorem polarized_automorphism_e34_graph_polynomial_on_stratum
    (Q : Polynomial ℚ) (T : Over S)
    (hT : ∀ t : T.left, AutomorphismSourcePolynomial.polarizedAutomorphismGraphPolynomial
      (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) (T.hom t) = Q)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom)) :
    HilbertScheme.Presentations.Has.Core.HasFiberHilbertPolynomial B
      (HilbertScheme.Presentations.HomFunctor.Hom.graphFamily A.abelian.scheme A.abelian.scheme
        (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A.abelian T e.abelian.hom)) Q := by
  apply Presentations.GraphFiberCoordinates.graphFamily_hasFiberHilbertPolynomial_of_coordinates A.abelian.scheme A.abelian.scheme
    B (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A.abelian T e.abelian.hom) Q
  intro K _ a
  let t : Over S := Over.mk (a ≫ T.hom)
  let b : t ⟶ T := Over.homMk a rfl
  let e' := AutomorphismRestriction.restrictPolarizedAutomorphism A b e
  let c := EndomorphismHom.EndomorphismFamilies.homSourceSchemeIso A.abelian t
  let j := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B (a ≫ T.hom) e'.abelian.hom
  have : IsClosedImmersion j := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_closed A.abelian B _ _
  have hr : EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A.abelian t e'.abelian.hom =
      prod.map b (𝟙 A.abelian.scheme) ≫ EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A.abelian T e.abelian.hom := by
    rw [AutomorphismRestriction.restrictPolarizedAutomorphism_hom]
    exact EndomorphismHom.EndomorphismFamilies.relativeHom_restrict A.abelian b (Finite.Actions.GroupEndRing.ofHom _ e.abelian.hom)
  refine ⟨AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap (a ≫ T.hom) B.dimension, c.hom ≫ j,
    AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap_isPullback (a ≫ T.hom) B.dimension, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · change (c.hom ≫ (c.inv ≫
      (HilbertScheme.Presentations.HomFunctor.Hom.graph A.abelian.scheme A.abelian.scheme (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A.abelian t e'.abelian.hom)).left ≫
        Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding B (a ≫ T.hom))) ≫ _ = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_projective]
    rw [hr]
  · rw [Category.assoc, Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_over]
    exact EndomorphismHom.EndomorphismFamilies.homSourceSchemeIso_snd A.abelian t
  · rw [Scheme.Hom.ker_comp_of_isIso]
    have hp := AutomorphismSourcePolynomial.polarized_automorphism_field_graph_source_polynomial A P d hP s hs he B hB
      (a ≫ T.hom) e'
    have hQ : AutomorphismSourcePolynomial.polarizedAutomorphismGraphPolynomial (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he)
        ((a ≫ T.hom) (IsLocalRing.closedPoint K)) = Q := hT (a (IsLocalRing.closedPoint K))
    exact hQ ▸ hp

include hP hB in
theorem polarized_automorphism_inverse_pair_e34_graphs
    (Q : Polynomial ℚ) (T : Over S)
    (hT : ∀ t : T.left, AutomorphismSourcePolynomial.polarizedAutomorphismGraphPolynomial
      (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) (T.hom t) = Q)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback T.hom) (A.pullback T.hom)) :
    HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.abelian.scheme A.abelian.scheme 2 B (fun _ => Q)
      ((HilbertScheme.Presentations.Endomorphisms.Core.forgetGroupLaw A.abelian.scheme 2).app (op T)
        (Presentations.BoundedEndomorphismTuples.e34GroupEndTuple A.abelian T
          ![Finite.Actions.GroupEndRing.ofHom _ e.abelian.hom, Finite.Actions.GroupEndRing.ofHom _ e.abelian.inv])) := by
  intro i
  fin_cases i
  · exact polarized_automorphism_e34_graph_polynomial_on_stratum A P d hP s hs he B hB Q T hT e
  · exact polarized_automorphism_e34_graph_polynomial_on_stratum A P d hP s hs he B hB Q T hT e.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismPresentationsGraphs
