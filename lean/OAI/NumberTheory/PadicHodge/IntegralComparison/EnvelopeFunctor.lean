import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope

/-! # Envelope Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EnvelopeFunctor

noncomputable section

/-!
# IntegralComparison: functorial endomorphisms of divided-power envelopes

An explicitly constructed endomorphism of the input ring, compatible with
the divided-power base and preserving the defining ideal, induces an
actual divided-power endomorphism of its envelope by the proved universal
property. This is used for polynomial Frobenius lifts.
-/

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope

variable (A B : Type u) [CommRing A] [CommRing B]
variable (J : Ideal A) (δ : DividedPowers J) (f : A →+* B) (I : Ideal B)
variable (hf : J ≤ I.comap f)
variable (α : DividedPowers.DPMorphism δ δ) (β : B →+* B)
variable (hcomm : β.comp f = f.comp α.toRingHom) (hβ : I ≤ I.comap β)

def endomorphismTarget : DividedPower.PowerEnvelope.Target A B J δ f I where
  ring := DividedPower.PowerEnvelope.Envelope A B J δ f I
  ideal := DividedPower.PowerEnvelope.envelopeIdeal A B J δ f I
  dividedPowers := DividedPower.PowerEnvelope.envelopeDividedPowers A B J δ f I
  fromBase := (DividedPower.PowerEnvelope.toEnvelope A B J δ f I).comp β
  mapsIdeal := fun _x hx => DividedPower.PowerEnvelope.toEnvelope_mapsIdeal A B J δ f I (hβ hx)
  baseCompatible := by
    have hc : ((DividedPower.PowerEnvelope.toEnvelope A B J δ f I).comp β).comp f =
        ((DividedPower.PowerEnvelope.toEnvelope A B J δ f I).comp f).comp α.toRingHom := by
      rw [RingHom.comp_assoc, hcomm, ← RingHom.comp_assoc]
    rw [hc]
    exact (DividedPower.PowerEnvelope.envelopeTarget A B J δ f I hf).baseCompatible.comp _ α.isDPMorphism

/-- The induced divided-power endomorphism, with no assumed envelope maps. -/
def endomorphism :
    DividedPowers.DPMorphism (DividedPower.PowerEnvelope.envelopeDividedPowers A B J δ f I)
      (DividedPower.PowerEnvelope.envelopeDividedPowers A B J δ f I) :=
  DividedPower.PowerEnvelope.lift A B J δ f I (endomorphismTarget A B J δ f I hf α β hcomm hβ)

lemma endomorphism_fromBase :
    (endomorphism A B J δ f I hf α β hcomm hβ).toRingHom.comp (DividedPower.PowerEnvelope.toEnvelope A B J δ f I) =
      (DividedPower.PowerEnvelope.toEnvelope A B J δ f I).comp β :=
  DividedPower.PowerEnvelope.lift_fromBase A B J δ f I (endomorphismTarget A B J δ f I hf α β hcomm hβ)

/-- Change the map from the presentation ring by its specified endomorphism. -/
def transformedTarget (M : DividedPower.PowerEnvelope.Target A B J δ f I) : DividedPower.PowerEnvelope.Target A B J δ f I where
  ring := M.ring
  ideal := M.ideal
  dividedPowers := M.dividedPowers
  fromBase := M.fromBase.comp β
  mapsIdeal := fun _x hx => M.mapsIdeal (hβ hx)
  baseCompatible := by
    have hc : (M.fromBase.comp β).comp f = (M.fromBase.comp f).comp α.toRingHom := by
      rw [RingHom.comp_assoc, hcomm, ← RingHom.comp_assoc]
    rw [hc]
    exact M.baseCompatible.comp _ α.isDPMorphism

/-- The envelope endomorphism commutes with any explicitly given compatible
target endomorphism. -/
lemma endomorphism_natural (M : DividedPower.PowerEnvelope.Target A B J δ f I)
    (η : DividedPowers.DPMorphism M.dividedPowers M.dividedPowers)
    (hη : η.toRingHom.comp M.fromBase = M.fromBase.comp β) :
    (DividedPower.PowerEnvelope.lift A B J δ f I M).comp (endomorphism A B J δ f I hf α β hcomm hβ) =
      η.comp (DividedPower.PowerEnvelope.lift A B J δ f I M) := by
  let N := transformedTarget A B J δ f I α β hcomm hβ M
  have hleft : (DividedPower.PowerEnvelope.lift A B J δ f I M).comp (endomorphism A B J δ f I hf α β hcomm hβ) =
      DividedPower.PowerEnvelope.lift A B J δ f I N := by
    apply DividedPower.PowerEnvelope.lift_unique A B J δ f I N
    change ((DividedPower.PowerEnvelope.lift A B J δ f I M).toRingHom.comp
      (endomorphism A B J δ f I hf α β hcomm hβ).toRingHom).comp (DividedPower.PowerEnvelope.toEnvelope A B J δ f I) =
      M.fromBase.comp β
    rw [RingHom.comp_assoc, endomorphism_fromBase, ← RingHom.comp_assoc, DividedPower.PowerEnvelope.lift_fromBase]
  have hright : η.comp (DividedPower.PowerEnvelope.lift A B J δ f I M) = DividedPower.PowerEnvelope.lift A B J δ f I N := by
    apply DividedPower.PowerEnvelope.lift_unique A B J δ f I N
    change η.toRingHom.comp ((DividedPower.PowerEnvelope.lift A B J δ f I M).toRingHom.comp (DividedPower.PowerEnvelope.toEnvelope A B J δ f I)) =
      M.fromBase.comp β
    rw [DividedPower.PowerEnvelope.lift_fromBase]
    exact hη
  exact hleft.trans hright.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EnvelopeFunctor
