import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Nilpotence

/-! # Envelope Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EnvelopeResidue

noncomputable section

/-!
# IntegralComparison: the closed subscheme of the divided-power envelope

The quotient of the constructed envelope by its divided-power ideal is
proved to be the original quotient B/I. If p is nilpotent in B, the
envelope is a genuine divided-power thickening of that same quotient.
-/

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope

variable (A B : Type u) [CommRing A] [CommRing B]
variable (J : Ideal A) (δ : DividedPowers J) (f : A →+* B) (I : Ideal B)

/-- The original quotient, carrying the zero divided-power ideal. -/
def residueTarget (hf : J ≤ I.comap f) : DividedPower.PowerEnvelope.Target A B J δ f I where
  ring := B ⧸ I
  ideal := ⊥
  dividedPowers := dividedPowersBot _
  fromBase := Ideal.Quotient.mk I
  mapsIdeal := fun _x hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx
  baseCompatible := by
    refine ⟨Ideal.map_le_iff_le_comap.mpr (fun x hx => ?_), ?_⟩
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf hx)
    · intro n x hx
      have hx0 : Ideal.Quotient.mk I (f x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hf hx)
      simp only [RingHom.comp_apply]
      rw [hx0]
      by_cases hn : n = 0
      · subst n
        rw [(dividedPowersBot (B ⧸ I)).dpow_zero (Ideal.zero_mem _),
          δ.dpow_zero hx, map_one, map_one]
      · rw [(dividedPowersBot (B ⧸ I)).dpow_eval_zero hn]
        have hmem : f (δ.dpow n x) ∈ I := hf (δ.dpow_mem hn hx)
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr hmem).symm

def reduction (hf : J ≤ I.comap f) : DividedPower.PowerEnvelope.Envelope A B J δ f I →+* B ⧸ I :=
  (DividedPower.PowerEnvelope.lift A B J δ f I (residueTarget A B J δ f I hf)).toRingHom

lemma reduction_fromBase (hf : J ≤ I.comap f) :
    (reduction A B J δ f I hf).comp (DividedPower.PowerEnvelope.toEnvelope A B J δ f I) = Ideal.Quotient.mk I :=
  DividedPower.PowerEnvelope.lift_fromBase A B J δ f I (residueTarget A B J δ f I hf)

lemma reduction_kills (hf : J ≤ I.comap f) :
    DividedPower.PowerEnvelope.envelopeIdeal A B J δ f I ≤ RingHom.ker (reduction A B J δ f I hf) :=
  Ideal.map_le_iff_le_comap.mp (DividedPower.PowerEnvelope.lift A B J δ f I (residueTarget A B J δ f I hf)).ideal_comp

def toQuotient (hf : J ≤ I.comap f) :
    (DividedPower.PowerEnvelope.Envelope A B J δ f I ⧸ DividedPower.PowerEnvelope.envelopeIdeal A B J δ f I) →+* B ⧸ I :=
  Ideal.Quotient.lift _ (reduction A B J δ f I hf) (reduction_kills A B J δ f I hf)

def baseQuotientMap : B →+* (DividedPower.PowerEnvelope.Envelope A B J δ f I ⧸ DividedPower.PowerEnvelope.envelopeIdeal A B J δ f I) :=
  (Ideal.Quotient.mk _).comp (DividedPower.PowerEnvelope.toEnvelope A B J δ f I)

def fromQuotient : B ⧸ I →+* (DividedPower.PowerEnvelope.Envelope A B J δ f I ⧸ DividedPower.PowerEnvelope.envelopeIdeal A B J δ f I) :=
  Ideal.Quotient.lift I (baseQuotientMap A B J δ f I)
    (fun _x hx => Ideal.Quotient.eq_zero_iff_mem.mpr (DividedPower.PowerEnvelope.toEnvelope_mapsIdeal A B J δ f I hx))

private def expressionResidue : DividedPower.PowerEnvelope.expressionRing A B J δ f I →+*
    (DividedPower.PowerEnvelope.Envelope A B J δ f I ⧸ DividedPower.PowerEnvelope.envelopeIdeal A B J δ f I) :=
  (Ideal.Quotient.mk _).comp (DividedPower.PowerEnvelope.envelopeEquiv A B J δ f I).symm.toRingHom

private lemma expression_mem_range : ∀ e : DividedPower.PowerEnvelope.Expression B I,
    expressionResidue A B J δ f I (DividedPower.PowerEnvelope.element A B J δ f I e) ∈
      (baseQuotientMap A B J δ f I).range
  | .constant b => ⟨b, rfl⟩
  | .add x y => by
    change expressionResidue A B J δ f I
      (DividedPower.PowerEnvelope.element A B J δ f I x + DividedPower.PowerEnvelope.element A B J δ f I y) ∈ _
    have he : expressionResidue A B J δ f I
        (DividedPower.PowerEnvelope.element A B J δ f I x + DividedPower.PowerEnvelope.element A B J δ f I y) =
      expressionResidue A B J δ f I (DividedPower.PowerEnvelope.element A B J δ f I x) +
        expressionResidue A B J δ f I (DividedPower.PowerEnvelope.element A B J δ f I y) :=
      (expressionResidue A B J δ f I).map_add' _ _
    rw [he]
    exact (baseQuotientMap A B J δ f I).range.add_mem
      (expression_mem_range x) (expression_mem_range y)
  | .neg x => by
    change expressionResidue A B J δ f I (-DividedPower.PowerEnvelope.element A B J δ f I x) ∈ _
    erw [map_neg (expressionResidue A B J δ f I).toAddMonoidHom (DividedPower.PowerEnvelope.element A B J δ f I x)]
    exact (baseQuotientMap A B J δ f I).range.neg_mem (expression_mem_range x)
  | .mul x y => by
    change expressionResidue A B J δ f I
      (DividedPower.PowerEnvelope.element A B J δ f I x * DividedPower.PowerEnvelope.element A B J δ f I y) ∈ _
    have he : expressionResidue A B J δ f I
        (DividedPower.PowerEnvelope.element A B J δ f I x * DividedPower.PowerEnvelope.element A B J δ f I y) =
      expressionResidue A B J δ f I (DividedPower.PowerEnvelope.element A B J δ f I x) *
        expressionResidue A B J δ f I (DividedPower.PowerEnvelope.element A B J δ f I y) :=
      (expressionResidue A B J δ f I).map_mul' _ _
    rw [he]
    exact (baseQuotientMap A B J δ f I).range.mul_mem
      (expression_mem_range x) (expression_mem_range y)
  | .ideal x => by
    have hz : expressionResidue A B J δ f I (DividedPower.PowerEnvelope.element A B J δ f I (.ideal x)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem
        (DividedPower.PowerEnvelope.envelopeEquiv A B J δ f I).symm.toRingHom ⟨x, rfl⟩)
    rw [hz]
    exact (baseQuotientMap A B J δ f I).range.zero_mem

lemma fromQuotient_surjective : Function.Surjective (fromQuotient A B J δ f I) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨x, rfl⟩ := (DividedPower.PowerEnvelope.envelopeEquiv A B J δ f I).symm.surjective x
  obtain ⟨e, rfl⟩ := DividedPower.PowerEnvelope.element_surjective A B J δ f I x
  obtain ⟨b, hb⟩ := EnvelopeResidue.expression_mem_range A B J δ f I e
  exact ⟨Ideal.Quotient.mk I b, hb⟩

lemma toQuotient_fromQuotient (hf : J ≤ I.comap f) :
    (toQuotient A B J δ f I hf).comp (fromQuotient A B J δ f I) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun (reduction_fromBase A B J δ f I hf) b

/-- Forming the divided-power envelope preserves the prescribed closed subscheme. -/
def quotientEquiv (hf : J ≤ I.comap f) :
    B ⧸ I ≃+* (DividedPower.PowerEnvelope.Envelope A B J δ f I ⧸ DividedPower.PowerEnvelope.envelopeIdeal A B J δ f I) :=
  RingEquiv.ofBijective (fromQuotient A B J δ f I)
    ⟨Function.LeftInverse.injective (fun x =>
      DFunLike.congr_fun (toQuotient_fromQuotient A B J δ f I hf) x),
      fromQuotient_surjective A B J δ f I⟩

lemma prime_nilpotent (p : ℕ) (hp : IsNilpotent (p : B)) :
    IsNilpotent (p : DividedPower.PowerEnvelope.Envelope A B J δ f I) := by
  simpa only [map_natCast] using hp.map (DividedPower.PowerEnvelope.toEnvelope A B J δ f I)

lemma envelope_nilIdeal (p : ℕ) (hp : 0 < p) (hpn : IsNilpotent (p : B))
    {x : DividedPower.PowerEnvelope.Envelope A B J δ f I} (hx : x ∈ DividedPower.PowerEnvelope.envelopeIdeal A B J δ f I) : IsNilpotent x :=
  DividedPower.Nilpotence.nilpotent_of_mem
    (DividedPower.PowerEnvelope.envelopeDividedPowers A B J δ f I) p hp (prime_nilpotent A B J δ f I p hpn) hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EnvelopeResidue
