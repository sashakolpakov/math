import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductData

/-! # Separated Product Ring -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductRing

noncomputable section

/-!
# IntegralComparison: divided-power rings of products over a separated scheme

The proved surjective reduction lets the relative envelope impose the
actual closed fiber product over X as its closed quotient.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductData

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
variable (U V : BigCrystallineSite.Object p B J δ f)

def ringBundle : CommRingCat.{u} := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact CommRingCat.of (DividedPower.PrescribedPushout.Ring B U.ring V.ring
    U.ideal U.dividedPowers V.ideal V.dividedPowers (SeparatedProductData.ClosedRing f U V)
    (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V))

def Ring : Type u := ringBundle f U V

instance ringCommRing : CommRing (Ring f U V) := inferInstanceAs (CommRing (ringBundle f U V))

def ideal : Ideal (Ring f U V) := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact DividedPower.PrescribedPushout.ideal B U.ring V.ring
    U.ideal U.dividedPowers V.ideal V.dividedPowers (SeparatedProductData.ClosedRing f U V)
    (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V)

def dividedPowers : DividedPowers (SeparatedProductRing.ideal f U V) := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact DividedPower.PrescribedPushout.dividedPowers B U.ring V.ring
    U.ideal U.dividedPowers V.ideal V.dividedPowers (SeparatedProductData.ClosedRing f U V)
    (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V)

def fstDP : DividedPowers.DPMorphism U.dividedPowers (SeparatedProductRing.dividedPowers f U V) := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact DividedPower.PrescribedPushout.leftMap B U.ring V.ring
    U.ideal U.dividedPowers V.ideal V.dividedPowers (SeparatedProductData.ClosedRing f U V)
    (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V)

def sndDP : DividedPowers.DPMorphism V.dividedPowers (SeparatedProductRing.dividedPowers f U V) := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact DividedPower.PrescribedPushout.rightMap B U.ring V.ring
    U.ideal U.dividedPowers V.ideal V.dividedPowers (SeparatedProductData.ClosedRing f U V)
    (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V)

def residueEquiv : Ring f U V ⧸ SeparatedProductRing.ideal f U V ≃+* SeparatedProductData.ClosedRing f U V := by
  letI := U.base.toAlgebra
  letI := V.base.toAlgebra
  exact DividedPower.PrescribedPushout.residueEquiv B U.ring V.ring
    U.ideal U.dividedPowers V.ideal V.dividedPowers (SeparatedProductData.ClosedRing f U V)
    (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V)
    (SeparatedProductData.prescribedReduction_surjective f U V)

lemma residueEquiv_left (x : U.ring) : residueEquiv f U V
    (Ideal.Quotient.mk (SeparatedProductRing.ideal f U V) (fstDP f U V x)) =
      (Spec.preimage (SeparatedProductData.closedFst f U V)).hom (Ideal.Quotient.mk U.ideal x) := by
  let := U.base.toAlgebra
  let := V.base.toAlgebra
  have he := DividedPower.PrescribedPushout.residueEquiv_left B U.ring V.ring
    U.ideal U.dividedPowers V.ideal V.dividedPowers (SeparatedProductData.ClosedRing f U V)
    (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V)
    (SeparatedProductData.prescribedReduction_surjective f U V) x
  exact he.trans (DFunLike.congr_fun (SeparatedProductData.residueReduction_left f U V) (Ideal.Quotient.mk U.ideal x))

lemma residueEquiv_right (x : V.ring) : residueEquiv f U V
    (Ideal.Quotient.mk (SeparatedProductRing.ideal f U V) (sndDP f U V x)) =
      (Spec.preimage (SeparatedProductData.closedSnd f U V)).hom (Ideal.Quotient.mk V.ideal x) := by
  let := U.base.toAlgebra
  let := V.base.toAlgebra
  have he := DividedPower.PrescribedPushout.residueEquiv_right B U.ring V.ring
    U.ideal U.dividedPowers V.ideal V.dividedPowers (SeparatedProductData.ClosedRing f U V)
    (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V)
    (SeparatedProductData.prescribedReduction_surjective f U V) x
  exact he.trans (DFunLike.congr_fun (SeparatedProductData.residueReduction_right f U V) (Ideal.Quotient.mk V.ideal x))

lemma base_agree : (fstDP f U V).toRingHom.comp U.base = (sndDP f U V).toRingHom.comp V.base := by
  let := U.base.toAlgebra
  let := V.base.toAlgebra
  exact DividedPower.PrescribedPushout.maps_agree B U.ring V.ring
    U.ideal U.dividedPowers V.ideal V.dividedPowers (SeparatedProductData.ClosedRing f U V)
    (SeparatedProductData.leftReduction f U V) (SeparatedProductData.rightReduction f U V) (SeparatedProductData.reductions_agree f U V)

lemma prime_nilpotent : IsNilpotent (p : Ring f U V) := by
  simpa only [map_natCast] using U.primeNilpotent.map (fstDP f U V).toRingHom

lemma nilIdeal (hp : 0 < p) {x : Ring f U V} (hx : x ∈ SeparatedProductRing.ideal f U V) : IsNilpotent x :=
  DividedPower.Nilpotence.nilpotent_of_mem (SeparatedProductRing.dividedPowers f U V) p hp
    (prime_nilpotent f U V) hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SeparatedProductRing
