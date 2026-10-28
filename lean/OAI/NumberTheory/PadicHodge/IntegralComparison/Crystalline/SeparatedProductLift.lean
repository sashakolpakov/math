import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductGeometry

/-! # Separated Product Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductLift

noncomputable section

/-!
# IntegralComparison: the universal property of crystalline products over separated schemes
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductData
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductGeometry OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductRing

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
variable (U V : BigCrystallineSite.Object p B J δ f) (hp : 0 < p)
variable {Z : BigCrystallineSite.Object p B J δ f} (γ : Z ⟶ U) (η : Z ⟶ V)

def closedLift : Spec (CommRingCat.of (Z.ring ⧸ Z.ideal)) ⟶ Spec (SeparatedProductData.ClosedRing f U V) :=
  (SeparatedProductData.closed_pullback f U V).lift (BigCrystallineSite.Object.closed.map γ) (BigCrystallineSite.Object.closed.map η) (γ.overX.trans η.overX.symm)

def quotientMap : SeparatedProductData.ClosedRing f U V →+* Z.ring ⧸ Z.ideal := (Spec.preimage (closedLift f U V γ η)).hom

lemma quotientMap_spec : Spec.map (CommRingCat.ofHom (quotientMap f U V γ η)) = closedLift f U V γ η :=
  Spec.map_preimage _

lemma quotientMap_left : (quotientMap f U V γ η).comp (Spec.preimage (SeparatedProductData.closedFst f U V)).hom =
    BigCrystallineSite.Object.quotientMap Z U γ.ringMap := by
  have he := (congrArg (fun t => t ≫ SeparatedProductData.closedFst f U V)
    (quotientMap_spec f U V γ η)).trans ((SeparatedProductData.closed_pullback f U V).lift_fst _ _ _)
  rw [← Spec.map_preimage (SeparatedProductData.closedFst f U V), ← Spec.map_comp] at he
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

lemma quotientMap_right : (quotientMap f U V γ η).comp (Spec.preimage (SeparatedProductData.closedSnd f U V)).hom =
    BigCrystallineSite.Object.quotientMap Z V η.ringMap := by
  have he := (congrArg (fun t => t ≫ SeparatedProductData.closedSnd f U V)
    (quotientMap_spec f U V γ η)).trans ((SeparatedProductData.closed_pullback f U V).lift_snd _ _ _)
  rw [← Spec.map_preimage (SeparatedProductData.closedSnd f U V), ← Spec.map_comp] at he
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

lemma leftReduction_eq : (SeparatedProductData.leftReduction f U V).toRingHom =
    (Spec.preimage (SeparatedProductData.closedFst f U V)).hom.comp (Ideal.Quotient.mk U.ideal) := by
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun (SeparatedProductData.residueReduction_left f U V) (Ideal.Quotient.mk U.ideal x)

lemma rightReduction_eq : (SeparatedProductData.rightReduction f U V).toRingHom =
    (Spec.preimage (SeparatedProductData.closedSnd f U V)).hom.comp (Ideal.Quotient.mk V.ideal) := by
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun (SeparatedProductData.residueReduction_right f U V) (Ideal.Quotient.mk V.ideal x)

lemma quotientMap_fromLeft : (quotientMap f U V γ η).comp (SeparatedProductData.leftReduction f U V).toRingHom =
    (Ideal.Quotient.mk Z.ideal).comp γ.ringMap.toRingHom := by
  rw [leftReduction_eq, ← RingHom.comp_assoc, quotientMap_left]
  rfl

lemma quotientMap_fromRight : (quotientMap f U V γ η).comp (SeparatedProductData.rightReduction f U V).toRingHom =
    (Ideal.Quotient.mk Z.ideal).comp η.ringMap.toRingHom := by
  rw [rightReduction_eq, ← RingHom.comp_assoc, quotientMap_right]
  rfl

omit [IsSeparated f] in
lemma mapsBase : γ.ringMap.toRingHom.comp U.base = η.ringMap.toRingHom.comp V.base :=
  γ.overBase.trans η.overBase.symm

def liftDP : DividedPowers.DPMorphism (SeparatedProductRing.dividedPowers f U V) Z.dividedPowers := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact DividedPower.PrescribedLift.lift B U.ring V.ring U.ideal U.dividedPowers V.ideal V.dividedPowers
    (SeparatedProductData.ClosedRing f U V) (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V)
    γ.ringMap η.ringMap (mapsBase f U V γ η) (quotientMap f U V γ η)
    (quotientMap_fromLeft f U V γ η) (quotientMap_fromRight f U V γ η)

lemma liftDP_left : (liftDP f U V γ η).comp (SeparatedProductRing.fstDP f U V) = γ.ringMap := by
  let := U.base.toAlgebra
  let := V.base.toAlgebra
  exact DividedPower.PrescribedLift.lift_left B U.ring V.ring U.ideal U.dividedPowers V.ideal V.dividedPowers
    (SeparatedProductData.ClosedRing f U V) (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V)
    γ.ringMap η.ringMap (mapsBase f U V γ η) (quotientMap f U V γ η)
    (quotientMap_fromLeft f U V γ η) (quotientMap_fromRight f U V γ η)

lemma liftDP_right : (liftDP f U V γ η).comp (SeparatedProductRing.sndDP f U V) = η.ringMap := by
  let := U.base.toAlgebra
  let := V.base.toAlgebra
  exact DividedPower.PrescribedLift.lift_right B U.ring V.ring U.ideal U.dividedPowers V.ideal V.dividedPowers
    (SeparatedProductData.ClosedRing f U V) (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V)
    γ.ringMap η.ringMap (mapsBase f U V γ η) (quotientMap f U V γ η)
    (quotientMap_fromLeft f U V γ η) (quotientMap_fromRight f U V γ η)

lemma liftDP_unique (l : DividedPowers.DPMorphism (SeparatedProductRing.dividedPowers f U V) Z.dividedPowers)
    (hl : l.comp (SeparatedProductRing.fstDP f U V) = γ.ringMap) (hr : l.comp (SeparatedProductRing.sndDP f U V) = η.ringMap) : l = liftDP f U V γ η := by
  let := U.base.toAlgebra
  let := V.base.toAlgebra
  exact DividedPower.PrescribedLift.lift_unique B U.ring V.ring U.ideal U.dividedPowers V.ideal V.dividedPowers
    (SeparatedProductData.ClosedRing f U V) (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V)
    γ.ringMap η.ringMap (mapsBase f U V γ η) (quotientMap f U V γ η)
    (quotientMap_fromLeft f U V γ η) (quotientMap_fromRight f U V γ η) l hl hr

private lemma quotient_comp :
    (BigCrystallineSite.Object.quotientMap Z (SeparatedProductGeometry.object f U V hp) (liftDP f U V γ η)).comp
      (BigCrystallineSite.Object.quotientMap (SeparatedProductGeometry.object f U V hp) U (SeparatedProductRing.fstDP f U V)) = BigCrystallineSite.Object.quotientMap Z U γ.ringMap := by
  rw [← BigCrystallineSite.Object.quotientMap_comp, liftDP_left]

def lift : Z ⟶ SeparatedProductGeometry.object f U V hp where
  ringMap := liftDP f U V γ η
  overBase := by
    change ((liftDP f U V γ η).comp (SeparatedProductRing.fstDP f U V)).toRingHom.comp U.base = Z.base
    rw [liftDP_left]
    exact γ.overBase
  overX := by
    change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap Z (SeparatedProductGeometry.object f U V hp) (liftDP f U V γ η))) ≫
      (SeparatedProductGeometry.fstClosed f U V ≫ U.mapToX) = Z.mapToX
    rw [← Category.assoc]
    have hq : Spec.map (CommRingCat.ofHom
          (BigCrystallineSite.Object.quotientMap Z (SeparatedProductGeometry.object f U V hp) (liftDP f U V γ η))) ≫ SeparatedProductGeometry.fstClosed f U V =
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap Z U γ.ringMap)) := by
      change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap Z (SeparatedProductGeometry.object f U V hp) (liftDP f U V γ η))) ≫
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap (SeparatedProductGeometry.object f U V hp) U (SeparatedProductRing.fstDP f U V))) = _
      rw [← Spec.map_comp]
      exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) (quotient_comp f U V hp γ η)
    rw [hq]
    exact γ.overX

lemma lift_fst : SeparatedProductLift.lift f U V hp γ η ≫ SeparatedProductGeometry.fst f U V hp = γ := by
  apply BigCrystallineSite.Object.Hom.ext
  exact liftDP_left f U V γ η

lemma lift_snd : SeparatedProductLift.lift f U V hp γ η ≫ SeparatedProductGeometry.snd f U V hp = η := by
  apply BigCrystallineSite.Object.Hom.ext
  exact liftDP_right f U V γ η

lemma lift_unique (l : Z ⟶ SeparatedProductGeometry.object f U V hp) (hl : l ≫ SeparatedProductGeometry.fst f U V hp = γ) (hr : l ≫ SeparatedProductGeometry.snd f U V hp = η) :
    l = SeparatedProductLift.lift f U V hp γ η := by
  apply BigCrystallineSite.Object.Hom.ext
  exact liftDP_unique f U V γ η l.ringMap (congrArg (fun t : Z ⟶ U => t.ringMap) hl)
    (congrArg (fun t : Z ⟶ V => t.ringMap) hr)

omit γ η in
def fan : BinaryFan U V := BinaryFan.mk (SeparatedProductGeometry.fst f U V hp) (SeparatedProductGeometry.snd f U V hp)

omit γ η in
def isProduct : IsLimit (fan f U V hp) :=
  BinaryFan.isLimitMk (fun s => SeparatedProductLift.lift f U V hp s.fst s.snd)
    (fun s => SeparatedProductLift.lift_fst f U V hp s.fst s.snd) (fun s => SeparatedProductLift.lift_snd f U V hp s.fst s.snd)
    (fun s l hl hr => lift_unique f U V hp s.fst s.snd l hl hr)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductLift
