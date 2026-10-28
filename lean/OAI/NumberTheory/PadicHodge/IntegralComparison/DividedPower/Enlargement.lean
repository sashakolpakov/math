import OAI.NumberTheory.PadicHodge.IntegralComparison.EnvelopeResidue

/-! # Enlargement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Enlargement

noncomputable section

/-!
# IntegralComparison: enlarging the closed ideal of a divided-power thickening

The relative envelope extends the existing divided powers to a larger
ideal. Its closed quotient is the prescribed smaller closed subscheme,
and its universal property controls maps into other thickenings.
-/

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope

variable (A : Type u) [CommRing A] (I : Ideal A) (δ : DividedPowers I) (L : Ideal A) (hIL : I ≤ L)

abbrev Ring := PowerEnvelope.Envelope A A I δ (RingHom.id A) L

abbrev ideal := PowerEnvelope.envelopeIdeal A A I δ (RingHom.id A) L

abbrev dividedPowers := PowerEnvelope.envelopeDividedPowers A A I δ (RingHom.id A) L

def map : DividedPowers.DPMorphism δ (Enlargement.dividedPowers A I δ L) where
  toRingHom := PowerEnvelope.toEnvelope A A I δ (RingHom.id A) L
  ideal_comp := (PowerEnvelope.envelopeTarget A A I δ (RingHom.id A) L hIL).baseCompatible.ideal_comp
  dpow_comp := (PowerEnvelope.envelopeTarget A A I δ (RingHom.id A) L hIL).baseCompatible.dpow_comp

lemma map_largerIdeal {x : A} (hx : x ∈ L) : map A I δ L hIL x ∈ Enlargement.ideal A I δ L :=
  PowerEnvelope.toEnvelope_mapsIdeal A A I δ (RingHom.id A) L hx

def residueEquiv : A ⧸ L ≃+* Ring A I δ L ⧸ Enlargement.ideal A I δ L :=
  EnvelopeResidue.quotientEquiv A A I δ (RingHom.id A) L hIL

lemma residueEquiv_mk (x : A) :
    residueEquiv A I δ L hIL (Ideal.Quotient.mk L x) =
      Ideal.Quotient.mk (Enlargement.ideal A I δ L) (map A I δ L hIL x) := rfl

lemma prime_nilpotent (p : ℕ) (hp : IsNilpotent (p : A)) : IsNilpotent (p : Ring A I δ L) :=
  EnvelopeResidue.prime_nilpotent A A I δ (RingHom.id A) L p hp

lemma nilIdeal (p : ℕ) (hp : 0 < p) (hpn : IsNilpotent (p : A))
    {x : Ring A I δ L} (hx : x ∈ Enlargement.ideal A I δ L) : IsNilpotent x :=
  EnvelopeResidue.envelope_nilIdeal A A I δ (RingHom.id A) L p hp hpn hx

variable {D : Type u} [CommRing D] {K : Ideal D} {ε : DividedPowers K}
variable (φ : DividedPowers.DPMorphism δ ε) (hL : L ≤ K.comap φ.toRingHom)

def target : PowerEnvelope.Target A A I δ (RingHom.id A) L where
  ring := D
  ideal := K
  dividedPowers := ε
  fromBase := φ.toRingHom
  mapsIdeal := hL
  baseCompatible := φ.isDPMorphism

def lift : DividedPowers.DPMorphism (Enlargement.dividedPowers A I δ L) ε :=
  PowerEnvelope.lift A A I δ (RingHom.id A) L (target A I δ L φ hL)

lemma lift_comp : (lift A I δ L φ hL).comp (map A I δ L hIL) = φ := by
  apply DFunLike.ext
  intro x
  exact DFunLike.congr_fun (PowerEnvelope.lift_fromBase A A I δ (RingHom.id A) L (target A I δ L φ hL)) x

lemma lift_unique (ψ : DividedPowers.DPMorphism (Enlargement.dividedPowers A I δ L) ε)
    (hψ : ψ.comp (map A I δ L hIL) = φ) : ψ = lift A I δ L φ hL := by
  apply PowerEnvelope.lift_unique A A I δ (RingHom.id A) L (target A I δ L φ hL)
  exact congrArg (fun t : DividedPowers.DPMorphism δ ε => t.toRingHom) hψ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Enlargement
