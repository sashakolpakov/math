import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Faithfulness
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Transport

/-! # Transport Faithfulness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.TransportFaithfulness

noncomputable section

/-! Exact faithfulness of the transport interface. Universal functions
are derived from the existing fine ReferenceFamily geometry and retained in the
existential witness. They are not a new premise. Proof irrelevance
identifies the pairing made with that witness with the native pairing.
Every other clause is the original full native IsogenyQuotient proposition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

section

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] [CharZero K] [Field L] [NumberField L]
    {d N q : ℕ} [NeZero N] [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
    (Z : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hZ : Z.IsFine) (κ₀ : K →+* ℂ)
    (hC : Z.HasProjectiveBallComponents κ₀)
    {κ : L →+* ℂ} (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (arithmeticEmbedding : E →+* L)
    (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
    (hd : 0 < d) (hdegree : Module.finrank ℚ E = 2 * d)
    (h : ℕ) (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex d ≃ Gal(E/ℚ))
    (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
    (a : Fin d → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v))
    (hcop : Nat.Coprime q N) (hpol : Nat.Coprime q (∏ i, P.polarizationType i))
    (h_FiniteDescent : AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.FiniteDescentInput.{0})

theorem integralHeckeFamily_iff_transportWitness :
    AbelianScheme.IsogenyQuotient.IntegralHecke.Construction.IntegralHeckeFamily Z hZ κ₀ hC j arithmeticEmbedding hsplit hd hdegree h labels hlabels
      a ha hdominant hcop hpol h_FiniteDescent ↔
    ∃ hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions Z.universal.polarized.abelian.scheme,
    ∃ (Q : Over Z.space.left) (_hQf : IsFinite Q.hom) (_hQe : Etale Q.hom)
      (f : AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction.NativeFinePELTarget (Z.universal.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space Q)) (q ^ h) Z),
      TransportWitness.TransportIntegralFiberWitness Z hZ hA j arithmeticEmbedding hsplit hd hdegree h labels hlabels
        a ha hdominant hcop hpol h_FiniteDescent Q f := by
  rw [Faithfulness.integralHeckeFamily_iff_fiberWitness]
  constructor
  · rintro ⟨Q, hQf, hQe, f, hw⟩
    exact ⟨AbelianScheme.IsogenyQuotient.FinePELUniversalFunctions.Construction.finePEL_universal_hasUniversalGlobalFunctions Z hZ κ₀ hC, Q, hQf, hQe, f, hw⟩
  · rintro ⟨hA, Q, hQf, hQe, f, hw⟩
    exact ⟨Q, hQf, hQe, f, hw⟩

end

theorem completeIsogenyQuotientTransportInput_iff_native : Transport.CompleteIsogenyQuotientTransportInput ↔ QuotientIntrinsic.FullIsogenyQuotientInput := by
  constructor
  · intro hComplete
    unfold QuotientIntrinsic.FullIsogenyQuotientInput
    intro E K _ _ _ _ _ _ _ s hs hdegree P hP iota κ₀ hemb N _ hN M hM hC
      L _ _ κ q _ j aE hsplit h labels hlabels a ha hdominant hcop hpol hFiniteDescent
    exact (integralHeckeFamily_iff_transportWitness M hM κ₀ hC j aE hsplit hs hdegree h labels hlabels
      a ha hdominant hcop hpol hFiniteDescent).mpr
        (hComplete s hs hdegree P hP iota κ₀ hemb N hN M hM hC q j aE hsplit h labels hlabels
          a ha hdominant hcop hpol hFiniteDescent)
  · intro hNative
    unfold Transport.CompleteIsogenyQuotientTransportInput
    intro E K _ _ _ _ _ _ _ s hs hdegree P hP iota κ₀ hemb N _ hN M hM hC
      L _ _ κ q _ j aE hsplit h labels hlabels a ha hdominant hcop hpol hFiniteDescent
    exact (integralHeckeFamily_iff_transportWitness M hM κ₀ hC j aE hsplit hs hdegree h labels hlabels
      a ha hdominant hcop hpol hFiniteDescent).mp
        (hNative s hs hdegree P hP iota κ₀ hemb N hN M hM hC q j aE hsplit h labels hlabels
          a ha hdominant hcop hpol hFiniteDescent)

theorem completeIsogenyQuotientTransportInput_of_native : Transport.CompleteIsogenyQuotientTransportInput :=
  completeIsogenyQuotientTransportInput_iff_native.mpr Faithfulness.fullIsogenyQuotientInput_of_native

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.TransportFaithfulness
