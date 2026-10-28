import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductRing

/-! # Separated Product Geometry -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductGeometry

noncomputable section

/-!
# IntegralComparison: the crystalline product object over a separated scheme and its projections
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductRing
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductData

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
variable (U V : BigCrystallineSite.Object p B J δ f)

def fstResidue : U.ring ⧸ U.ideal →+* SeparatedProductRing.Ring f U V ⧸ SeparatedProductRing.ideal f U V :=
  Ideal.quotientMap (SeparatedProductRing.ideal f U V) (SeparatedProductRing.fstDP f U V).toRingHom
    (Ideal.map_le_iff_le_comap.mp (SeparatedProductRing.fstDP f U V).ideal_comp)

def sndResidue : V.ring ⧸ V.ideal →+* SeparatedProductRing.Ring f U V ⧸ SeparatedProductRing.ideal f U V :=
  Ideal.quotientMap (SeparatedProductRing.ideal f U V) (SeparatedProductRing.sndDP f U V).toRingHom
    (Ideal.map_le_iff_le_comap.mp (SeparatedProductRing.sndDP f U V).ideal_comp)

lemma residueEquiv_fst : (SeparatedProductRing.residueEquiv f U V).toRingHom.comp (fstResidue f U V) = (Spec.preimage (SeparatedProductData.closedFst f U V)).hom := by
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact SeparatedProductRing.residueEquiv_left f U V y

lemma residueEquiv_snd : (SeparatedProductRing.residueEquiv f U V).toRingHom.comp (sndResidue f U V) = (Spec.preimage (SeparatedProductData.closedSnd f U V)).hom := by
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact SeparatedProductRing.residueEquiv_right f U V y

def closedIso : Spec (CommRingCat.of (SeparatedProductRing.Ring f U V ⧸ SeparatedProductRing.ideal f U V)) ≅ Spec (SeparatedProductData.ClosedRing f U V) :=
  (Scheme.Spec.mapIso (SeparatedProductRing.residueEquiv f U V).toCommRingCatIso.op).symm

def fstClosed : Spec (CommRingCat.of (SeparatedProductRing.Ring f U V ⧸ SeparatedProductRing.ideal f U V)) ⟶
    Spec (CommRingCat.of (U.ring ⧸ U.ideal)) := Spec.map (CommRingCat.ofHom (fstResidue f U V))

def sndClosed : Spec (CommRingCat.of (SeparatedProductRing.Ring f U V ⧸ SeparatedProductRing.ideal f U V)) ⟶
    Spec (CommRingCat.of (V.ring ⧸ V.ideal)) := Spec.map (CommRingCat.ofHom (sndResidue f U V))

lemma fstClosed_eq : fstClosed f U V = (closedIso f U V).hom ≫ Spec.map (CommRingCat.ofHom ((Spec.preimage (SeparatedProductData.closedFst f U V)).hom)) := by
  have hr : fstResidue f U V = (SeparatedProductRing.residueEquiv f U V).symm.toRingHom.comp ((Spec.preimage (SeparatedProductData.closedFst f U V)).hom) := by
    apply RingHom.ext
    intro x
    apply (SeparatedProductRing.residueEquiv f U V).injective
    exact (DFunLike.congr_fun (residueEquiv_fst f U V) x).trans
      ((SeparatedProductRing.residueEquiv f U V).apply_symm_apply _).symm
  change Spec.map (CommRingCat.ofHom (fstResidue f U V)) =
    Spec.map (CommRingCat.ofHom (SeparatedProductRing.residueEquiv f U V).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ((Spec.preimage (SeparatedProductData.closedFst f U V)).hom))
  rw [← Spec.map_comp]
  exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) hr

lemma sndClosed_eq : sndClosed f U V = (closedIso f U V).hom ≫ Spec.map (CommRingCat.ofHom ((Spec.preimage (SeparatedProductData.closedSnd f U V)).hom)) := by
  have hr : sndResidue f U V = (SeparatedProductRing.residueEquiv f U V).symm.toRingHom.comp ((Spec.preimage (SeparatedProductData.closedSnd f U V)).hom) := by
    apply RingHom.ext
    intro x
    apply (SeparatedProductRing.residueEquiv f U V).injective
    exact (DFunLike.congr_fun (residueEquiv_snd f U V) x).trans
      ((SeparatedProductRing.residueEquiv f U V).apply_symm_apply _).symm
  change Spec.map (CommRingCat.ofHom (sndResidue f U V)) =
    Spec.map (CommRingCat.ofHom (SeparatedProductRing.residueEquiv f U V).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ((Spec.preimage (SeparatedProductData.closedSnd f U V)).hom))
  rw [← Spec.map_comp]
  exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) hr

lemma closed_square : fstClosed f U V ≫ U.mapToX = sndClosed f U V ≫ V.mapToX := by
  rw [fstClosed_eq, sndClosed_eq]
  change ((closedIso f U V).hom ≫ Spec.map (Spec.preimage (SeparatedProductData.closedFst f U V))) ≫ U.mapToX =
    ((closedIso f U V).hom ≫ Spec.map (Spec.preimage (SeparatedProductData.closedSnd f U V))) ≫ V.mapToX
  rw [Spec.map_preimage, Spec.map_preimage,
    Category.assoc, Category.assoc, (SeparatedProductData.closed_pullback f U V).w]

lemma fstClosed_naturality : fstClosed f U V ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk U.ideal)) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (SeparatedProductRing.ideal f U V))) ≫
      Spec.map (CommRingCat.ofHom (SeparatedProductRing.fstDP f U V).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (fstResidue f U V)) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk U.ideal)) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

variable (hp : 0 < p)

abbrev object : BigCrystallineSite.Object p B J δ f where
  ring := CommRingCat.of (SeparatedProductRing.Ring f U V)
  base := (SeparatedProductRing.fstDP f U V).toRingHom.comp U.base
  ideal := SeparatedProductRing.ideal f U V
  dividedPowers := SeparatedProductRing.dividedPowers f U V
  baseCompatible := (SeparatedProductRing.fstDP f U V).isDPMorphism.comp _ U.baseCompatible
  primeNilpotent := SeparatedProductRing.prime_nilpotent f U V
  nilIdeal _ hx := SeparatedProductRing.nilIdeal f U V hp hx
  mapToX := fstClosed f U V ≫ U.mapToX
  overBase := by
    rw [Category.assoc, U.overBase, ← Category.assoc, fstClosed_naturality,
      Category.assoc, ← Spec.map_comp]
    rfl

def fst : object f U V hp ⟶ U where
  ringMap := SeparatedProductRing.fstDP f U V
  overBase := rfl
  overX := rfl

def snd : object f U V hp ⟶ V where
  ringMap := SeparatedProductRing.sndDP f U V
  overBase := (SeparatedProductRing.base_agree f U V).symm
  overX := (closed_square f U V).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductGeometry
