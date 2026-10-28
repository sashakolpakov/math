import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SubsiteSlices
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceStructure

/-! # Slice Sheaves -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.SliceSheaves

noncomputable section

/-!
# IntegralComparison: bounded crystalline slice sheaves are the original slice sheaves
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (U : Site.Objects (p := p) (J := J) (δ := δ) f n)

abbrev SliceSheaf := Sheaf ((Site.topology f n).over U) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))

def equivalence : CrystallinePrincipal.Extension.SliceSheaf U.obj ≌ SliceSheaf f n U := by
  let P : ObjectProperty (BigCrystallineSite.Object p B J δ f) := Site.property f n
  let e := Incoming.SubsiteSlices.equivalence P (fun α => Site.property_of_hom f n α) U
  have : e.symm.inverse.IsDenseSubsite ((Site.topology f n).over U) (BigCrystallineSite.Object.topology.over U.obj) :=
    Incoming.SubsiteSlices.post_isDenseSubsite P (fun α => Site.property_of_hom f n α) U BigCrystallineSite.Object.topology
  exact e.symm.sheafCongr (BigCrystallineSite.Object.topology.over U.obj) ((Site.topology f n).over U)
    (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))

instance equivalence_additive : (equivalence f n U).functor.Additive where
  map_add := by intros; rfl

instance equivalence_linear : (equivalence f n U).functor.Linear (Crystalline.ExactRestriction.Coeff (B := B)) where
  map_smul := by intros; rfl

abbrev constantUnit : SliceSheaf f n U :=
  (constantSheaf ((Site.topology f n).over U) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).obj
    (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B)))

abbrev structureSheaf : SliceSheaf f n U :=
  ((Site.topology f n).overPullback (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) U).obj
    (CrystallineCohomology.structureSheaf f n)

def constantUnitIso : (equivalence f n U).functor.obj
    (CrystallinePrincipal.Constant.Comparison.constantUnit U.obj) ≅ constantUnit f n U := by
  let P : ObjectProperty (BigCrystallineSite.Object p B J δ f) := Site.property f n
  have : (Over.post (X := U) P.ι).IsDenseSubsite ((Site.topology f n).over U) (BigCrystallineSite.Object.topology.over U.obj) :=
    Incoming.SubsiteSlices.post_isDenseSubsite P (fun α => Site.property_of_hom f n α) U BigCrystallineSite.Object.topology
  exact ((Over.post (X := U) P.ι).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) ((Site.topology f n).over U) (BigCrystallineSite.Object.topology.over U.obj)).symm.app
      ((Functor.const (Over U.obj)ᵒᵖ).obj (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B))))

def structureSheafIso : (equivalence f n U).functor.obj
    (Crystalline.SliceStructure.structureSheaf U.obj) ≅ structureSheaf f n U :=
  Iso.refl _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.SliceSheaves
