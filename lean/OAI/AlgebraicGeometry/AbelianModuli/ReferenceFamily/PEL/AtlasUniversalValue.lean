import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELActionFunctorDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AtlasCoverValues

/-! # Atlas Universal Value -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.AtlasUniversalValue

noncomputable section

/-! Construction of the actual universal PEL action on a noetherian
atlas from its local universal values and proved effective descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AtlasCoverValues.RepresentationAtlas
variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)

theorem exists_pel_atlas_universal_value {I : Type} {U : I → M.left.Opens}
    (D : ∀ i, Open.Representations.OpenRepresentation (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A) (U i))
    [IsNoetherian (RepresentationAtlasIs.RepresentationAtlas.scheme D)] :
    ∃ u : (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op (RepresentationAtlasIs.RepresentationAtlas.over D)),
      ∀ i, (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map (RepresentationAtlasIs.RepresentationAtlas.chartOver D i).op u = (D i).sectionValue := by
  let F := PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A
  obtain ⟨q, hq, _⟩ := Relative.PELActionFunctorDescent.existsUnique_pel_value_of_functor_matching P iotaO M A
    (RepresentationAtlasIs.RepresentationAtlas.structureMap D) (RepresentationAtlasIs.RepresentationAtlas.openCover D) (AtlasCoverValues.RepresentationAtlas.chartValue D)
    (fun i j T f h => AtlasCoverValues.RepresentationAtlas.chartValues_match D i j T f h)
  let v : F.obj (op (RepresentationAtlasIs.RepresentationAtlas.over D)) := q
  refine ⟨v, fun i => ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (F.map (AtlasCoverValues.RepresentationAtlas.chartComparison D i).hom.op)).injective
  change F.map (AtlasCoverValues.RepresentationAtlas.chartComparison D i).hom.op (F.map (RepresentationAtlasIs.RepresentationAtlas.chartOver D i).op v) = _
  rw [← F.map_comp_apply]
  have hi : (AtlasCoverValues.RepresentationAtlas.chartComparison D i).hom ≫ RepresentationAtlasIs.RepresentationAtlas.chartOver D i =
      PELModuli.IntegralModel.ActionCanonicalRestriction.ActionBaseChange.testInclusion (RepresentationAtlasIs.RepresentationAtlas.structureMap D) (AtlasCoverValues.RepresentationAtlas.chartTest D i) := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  change F.map ((AtlasCoverValues.RepresentationAtlas.chartComparison D i).hom ≫ RepresentationAtlasIs.RepresentationAtlas.chartOver D i).op v = AtlasCoverValues.RepresentationAtlas.chartValue D i
  rw [hi]
  exact hq i

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.AtlasUniversalValue
