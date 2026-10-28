import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentationAtlasIs
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Representation Atlas Properties -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentationAtlasProperties.RepresentationAtlas

noncomputable section

/-! Finiteness and separation descend from the constructed parameter charts
along their recovered base-open pullback squares. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, Open.Representations.OpenRepresentation F (U i))

theorem chartBase_property (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (i : I) (h : P (D i).space.hom) : P (RepresentationAtlasIs.RepresentationAtlas.chartBase D i) := by
  have hp : IsPullback (RepresentationAtlasIs.RepresentationAtlas.chartBase D i) (𝟙 (D i).space.left)
      (U i).ι (D i).space.hom :=
    IsOpenImmersion.isPullback_lift_id (D i).space.hom (U i).ι _
  exact IsZariskiLocalAtTarget.of_isPullback (P := P) hp.flip h

theorem structureMap_property (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hU : iSup U = ⊤) (h : ∀ i, P (D i).space.hom) : P (RepresentationAtlasIs.RepresentationAtlas.structureMap D) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := P) U hU
  intro i
  have hp := RepresentationAtlasIs.RepresentationAtlas.chart_isPullback D i
  have hq := isPullback_morphismRestrict (RepresentationAtlasIs.RepresentationAtlas.structureMap D) (U i)
  let e := hp.isoPullback ≪≫ hq.isoPullback.symm
  have he : e.hom ≫ (RepresentationAtlasIs.RepresentationAtlas.structureMap D ∣_ U i) = RepresentationAtlasIs.RepresentationAtlas.chartBase D i := by
    dsimp [e]
    rw [Category.assoc, hq.isoPullback_inv_fst, hp.isoPullback_hom_fst]
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := P) e.hom, he]
  exact chartBase_property D P i (h i)

theorem locallyOfFiniteType (hU : iSup U = ⊤)
    (h : ∀ i, LocallyOfFiniteType (D i).space.hom) : LocallyOfFiniteType (RepresentationAtlasIs.RepresentationAtlas.structureMap D) := by
  let : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType.{0})
      (Q := RingHom.FiniteType)
  exact structureMap_property D (@LocallyOfFiniteType) hU h

theorem quasiCompact (hU : iSup U = ⊤)
    (h : ∀ i, QuasiCompact (D i).space.hom) : QuasiCompact (RepresentationAtlasIs.RepresentationAtlas.structureMap D) := by
  let : IsZariskiLocalAtTarget (@QuasiCompact.{0}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  exact structureMap_property D (@QuasiCompact) hU h

theorem separated (hU : iSup U = ⊤)
    (h : ∀ i, IsSeparated (D i).space.hom) : IsSeparated (RepresentationAtlasIs.RepresentationAtlas.structureMap D) :=
  structureMap_property D (@IsSeparated) hU h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentationAtlasProperties.RepresentationAtlas
