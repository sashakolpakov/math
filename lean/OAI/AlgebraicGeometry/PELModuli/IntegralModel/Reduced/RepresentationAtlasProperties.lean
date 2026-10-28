import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.RepresentationAtlas
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Representation Atlas Properties -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.RepresentationAtlasProperties

noncomputable section

/-! Finiteness and separation descend from the constructed parameter charts
along their recovered base-open pullback squares. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace ReducedRepresentationAtlas
variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, OpenRepresentations.ReducedOpenRepresentation F (U i))

theorem chartBase_property (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (i : I) (h : P (D i).space.hom) : P (RepresentationAtlas.ReducedRepresentationAtlas.chartBase D i) := by
  have hp : IsPullback (RepresentationAtlas.ReducedRepresentationAtlas.chartBase D i) (𝟙 (D i).space.left)
      (U i).ι (D i).space.hom :=
    IsOpenImmersion.isPullback_lift_id (D i).space.hom (U i).ι _
  exact IsZariskiLocalAtTarget.of_isPullback (P := P) hp.flip h

theorem structureMap_property (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hU : iSup U = ⊤) (h : ∀ i, P (D i).space.hom) : P (RepresentationAtlas.ReducedRepresentationAtlas.structureMap D) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := P) U hU
  intro i
  have hp := RepresentationAtlas.ReducedRepresentationAtlas.chart_isPullback D i
  have hq := isPullback_morphismRestrict (RepresentationAtlas.ReducedRepresentationAtlas.structureMap D) (U i)
  let e := hp.isoPullback ≪≫ hq.isoPullback.symm
  have he : e.hom ≫ (RepresentationAtlas.ReducedRepresentationAtlas.structureMap D ∣_ U i) = RepresentationAtlas.ReducedRepresentationAtlas.chartBase D i := by
    dsimp [e]
    rw [Category.assoc, hq.isoPullback_inv_fst, hp.isoPullback_hom_fst]
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := P) e.hom, he]
  exact chartBase_property D P i (h i)

theorem locallyOfFiniteType (hU : iSup U = ⊤)
    (h : ∀ i, LocallyOfFiniteType (D i).space.hom) : LocallyOfFiniteType (RepresentationAtlas.ReducedRepresentationAtlas.structureMap D) :=
  structureMap_property D (@LocallyOfFiniteType) hU h

theorem quasiCompact (hU : iSup U = ⊤)
    (h : ∀ i, QuasiCompact (D i).space.hom) : QuasiCompact (RepresentationAtlas.ReducedRepresentationAtlas.structureMap D) :=
  structureMap_property D (@QuasiCompact) hU h

theorem separated (hU : iSup U = ⊤)
    (h : ∀ i, IsSeparated (D i).space.hom) : IsSeparated (RepresentationAtlas.ReducedRepresentationAtlas.structureMap D) :=
  structureMap_property D (@IsSeparated) hU h

end ReducedRepresentationAtlas

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.RepresentationAtlasProperties
