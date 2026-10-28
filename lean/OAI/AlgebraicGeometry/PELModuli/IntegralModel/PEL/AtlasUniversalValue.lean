import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ActionFunctorDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.AtlasCoverValues

/-! # Atlas Universal Value -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.AtlasUniversalValue

noncomputable section

/-! Construction of the actual universal PEL action on a noetherian
atlas from its local universal values and proved effective descent. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.AtlasCoverValues.ReducedRepresentationAtlas
variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)

theorem exists_pel_atlas_universal_value {I : Type} {U : I → M.left.Opens}
    (D : ∀ i, Reduced.OpenRepresentations.ReducedOpenRepresentation (Relative.ActionFunctor.relativePELActionFunctor P iotaO M A) (U i))
    [IsNoetherian (Reduced.RepresentationAtlas.ReducedRepresentationAtlas.scheme D)] :
    ∃ u : (Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op (Reduced.RepresentationAtlas.ReducedRepresentationAtlas.over D)),
      ∀ i, (Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map (Reduced.RepresentationAtlas.ReducedRepresentationAtlas.chartOver D i).op u = (D i).sectionValue := by
  let F := Relative.ActionFunctor.relativePELActionFunctor P iotaO M A
  obtain ⟨q, hq, _⟩ := Relative.ActionFunctorDescent.existsUnique_pel_value_of_functor_matching P iotaO M A
    (Reduced.RepresentationAtlas.ReducedRepresentationAtlas.structureMap D) (Reduced.RepresentationAtlas.ReducedRepresentationAtlas.openCover D) (Reduced.AtlasCoverValues.ReducedRepresentationAtlas.chartValue D)
    (fun i j T _ f h => Reduced.AtlasCoverValues.ReducedRepresentationAtlas.chartValues_match D i j T f h)
  refine ⟨q, fun i => ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (F.map (Reduced.AtlasCoverValues.ReducedRepresentationAtlas.chartComparison D i).hom.op)).injective
  change F.map (Reduced.AtlasCoverValues.ReducedRepresentationAtlas.chartComparison D i).hom.op (F.map (Reduced.RepresentationAtlas.ReducedRepresentationAtlas.chartOver D i).op q) = _
  rw [← F.map_comp_apply]
  have hi : (Reduced.AtlasCoverValues.ReducedRepresentationAtlas.chartComparison D i).hom ≫ Reduced.RepresentationAtlas.ReducedRepresentationAtlas.chartOver D i =
      ActionCanonicalRestriction.ActionBaseChange.testInclusion (Reduced.RepresentationAtlas.ReducedRepresentationAtlas.structureMap D) (Reduced.AtlasCoverValues.ReducedRepresentationAtlas.chartTest D i) := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  change F.map ((Reduced.AtlasCoverValues.ReducedRepresentationAtlas.chartComparison D i).hom ≫ Reduced.RepresentationAtlas.ReducedRepresentationAtlas.chartOver D i).op q = Reduced.AtlasCoverValues.ReducedRepresentationAtlas.chartValue D i
  rw [hi]
  exact hq i

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.AtlasUniversalValue
