import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedCoefficientChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.EmbeddedTorsionDetection

/-! # Polarized Coefficient Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PolarizedCoefficientChange

noncomputable section

/-! Coefficient change of an embedded polarized family has an actual
isomorphism with the saturated extended homogeneous presentation.
The isomorphism preserves the projection and transports its O(1)
identification to the canonical graph power of the new family. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R C : Type u} [CommRing R] [IsNoetherianRing R] [CommRing C]
variable {g N r : ℕ} {δ : Fin g → ℕ} {P : Polynomial ℚ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R r P)
variable (e : A.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal) (φ : R →+* C)

def embeddedCoefficientChangeIso :
    (A.pullback (Spec.map (CommRingCat.ofHom φ))).abelian.scheme ≅
      Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (I.coefficientChange φ).ideal :=
  (Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso e ≪≫ (I.coefficientChangeIso φ).symm

theorem embeddedCoefficientChangeIso_projection :
    (embeddedCoefficientChangeIso A I e φ).hom.left ≫ I.coefficientChangeMorphism φ =
      pullback.fst A.abelian.scheme.hom (Spec.map (CommRingCat.ofHom φ)) ≫ e.hom.left := by
  have he : (embeddedCoefficientChangeIso A I e φ).hom ≫ (I.coefficientChangeIso φ).hom =
      (Over.pullback (Spec.map (CommRingCat.ofHom φ))).map e.hom := by
    change (((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map e.hom) ≫
      (I.coefficientChangeIso φ).inv) ≫ (I.coefficientChangeIso φ).hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (embeddedCoefficientChangeIso A I e φ).hom.left ≫
    ((I.coefficientChangeIso φ).hom.left ≫ pullback.fst _ _) = _
  have hl : (embeddedCoefficientChangeIso A I e φ).hom.left ≫
      (I.coefficientChangeIso φ).hom.left =
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map e.hom).left :=
    congrArg Over.Hom.left he
  rw [← Category.assoc, hl]
  exact (Projective.PresentationBaseChange.overPullback_map_isPullback e.hom (Spec.map (CommRingCat.ofHom φ))).w.symm

def embeddedCoefficientChangeTwistingIso
    (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback e.hom.left).sheaf ≅
      (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf) :
    ((ProjectiveTwisting.Bundle.projectiveTwistingBundle (I.coefficientChange φ).ideal 1).pullback
      (embeddedCoefficientChangeIso A I e φ).hom.left).sheaf ≅
        ((A.pullback (Spec.map (CommRingCat.ofHom φ))).graphBundle.tensorPower
          (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf := by
  let f := Spec.map (CommRingCat.ofHom φ)
  let π := pullback.fst A.abelian.scheme.hom f
  let B := A.pullback f
  let a := (embeddedCoefficientChangeIso A I e φ).hom.left
  let m := I.coefficientChangeMorphism φ
  let L := ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1
  exact (Scheme.Modules.pullback a).mapIso (I.coefficientChangeTwistingIso φ).symm ≪≫
    (Scheme.Modules.pullbackComp a m).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (embeddedCoefficientChangeIso_projection A I e φ)).app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp π e.hom.left).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullback π).mapIso eL ≪≫
    A.graphBundle.powerBaseChangeIso π (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ) ≪≫
    (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).mapIso
      (A.graphBundle_baseChangeIso f).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PolarizedCoefficientChange
