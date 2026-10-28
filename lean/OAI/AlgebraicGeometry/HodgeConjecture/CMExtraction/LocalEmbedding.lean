import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Primes
import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic

/-! # Local Embedding -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalEmbedding.ParameterChoices

noncomputable section

/-! Each native integral character extends to an actual q-adic field
embedding; its finite place is the prime constructed from that character. -/

open _root_.NumberField IsDedekindDomain

theorem integerRingHom_injective {E F : Type} [Field E] [NumberField E]
    [Field F] [CharZero F] (f : 𝓞 E →+* F) : Function.Injective f := by
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply Ideal.eq_bot_of_under_eq_bot (R := ℤ)
  ext z
  change f (z : 𝓞 E) = 0 ↔ z = 0
  rw [map_intCast, Int.cast_eq_zero]

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

def nativeFieldEmbedding (i : Fin s × Bool) : E →+* ℚ_[q] :=
  IsFractionRing.lift (K := E)
    (integerRingHom_injective ((algebraMap ℤ_[q] ℚ_[q]).comp (D.localCharacter i)))

theorem nativeFieldEmbedding_onIntegers (i : Fin s × Bool) (a : 𝓞 E) :
    nativeFieldEmbedding D i (a : E) = (D.localCharacter i a : ℚ_[q]) :=
  IsLocalization.lift_eq _ a

theorem nativeFieldEmbedding_integral (i : Fin s × Bool) :
    PELModuli.CMPoints.LocalPadic.integersToPadicInt (nativeFieldEmbedding D i) = D.localCharacter i := by
  ext a
  apply PadicInt.ext
  exact (PELModuli.CMPoints.LocalPadic.integersToPadicInt_coe (nativeFieldEmbedding D i) a).trans
    (nativeFieldEmbedding_onIntegers D i a)

theorem nativeFieldEmbedding_place (i : Fin s × Bool) :
    PELModuli.CMPoints.LocalPadic.embeddingPlace (nativeFieldEmbedding D i) = Intrinsic.Primes.ParameterChoices.nativeLocalPrime D i := by
  apply HeightOneSpectrum.ext
  change RingHom.ker (PadicInt.toZMod.comp (PELModuli.CMPoints.LocalPadic.integersToPadicInt (nativeFieldEmbedding D i))) =
    RingHom.ker (PadicInt.toZMod.comp (D.localCharacter i))
  rw [nativeFieldEmbedding_integral]

theorem nativeFieldEmbedding_valuation_equiv (i : Fin s × Bool) :
    ((Intrinsic.Primes.ParameterChoices.nativeLocalPrime D i).valuation E).IsEquiv
      ((NormedField.valuation (K := ℚ_[q])).comap (nativeFieldEmbedding D i)) := by
  have h := PELModuli.CMPoints.LocalPadic.embedding_valuation_equiv (nativeFieldEmbedding D i)
  rw [nativeFieldEmbedding_place] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalEmbedding.ParameterChoices
