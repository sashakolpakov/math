import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.QuotientIntrinsic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.IntrinsicFiberWitness

/-! # Faithfulness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Faithfulness

noncomputable section

/-! The full input is directly instantiated by the native integral Hecke
family theorem. The exposed fiber witness is equivalent to that exact
native proposition; it does not substitute a TateComparison realization predicate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

section

theorem fullIsogenyQuotientInput_of_native : QuotientIntrinsic.FullIsogenyQuotientInput := by
  unfold QuotientIntrinsic.FullIsogenyQuotientInput
  intros
  apply AbelianScheme.IsogenyQuotient.IntegralHecke.Construction.integral_hecke_family_exists

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

theorem integralHeckeFamily_iff_fiberWitness :
    AbelianScheme.IsogenyQuotient.IntegralHecke.Construction.IntegralHeckeFamily Z hZ κ₀ hC j arithmeticEmbedding hsplit hd hdegree h labels hlabels
      a ha hdominant hcop hpol h_FiniteDescent ↔
    ∃ (Q : Over Z.space.left) (_hQf : IsFinite Q.hom) (_hQe : Etale Q.hom)
      (f : AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData.Construction.NativeFinePELTarget (Z.universal.pullback (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space Q)) (q ^ h) Z),
      IntrinsicFiberWitness.NativeIntegralFiberWitness Z hZ κ₀ hC j arithmeticEmbedding hsplit hd hdegree h labels hlabels
        a ha hdominant hcop hpol h_FiniteDescent Q f := by
  constructor
  · rintro ⟨Q, hQf, hQe, repr, e, he, hsf, hse, R, f, hk, hi, hr⟩
    exact ⟨Q, hQf, hQe, f, repr, e, he, hsf, hse, R, hk, hi, hr⟩
  · rintro ⟨Q, hQf, hQe, f, repr, e, he, hsf, hse, R, hk, hi, hr⟩
    exact ⟨Q, hQf, hQe, repr, e, he, hsf, hse, R, f, hk, hi, hr⟩

end

theorem completeIsogenyQuotientInput_iff_native : IntrinsicFiberWitness.CompleteIsogenyQuotientInput ↔ QuotientIntrinsic.FullIsogenyQuotientInput := by
  constructor
  · intro hComplete
    unfold QuotientIntrinsic.FullIsogenyQuotientInput
    intro E K _ _ _ _ _ _ _ s hs hdegree P hP iota κ₀ hemb N _ hN M hM hC
      L _ _ κ q _ j aE hsplit h labels hlabels a ha hdominant hcop hpol hFiniteDescent
    exact (integralHeckeFamily_iff_fiberWitness M hM κ₀ hC j aE hsplit hs hdegree h labels hlabels
      a ha hdominant hcop hpol hFiniteDescent).mpr
        (hComplete s hs hdegree P hP iota κ₀ hemb N hN M hM hC q j aE hsplit h labels hlabels
          a ha hdominant hcop hpol hFiniteDescent)
  · intro hNative
    unfold IntrinsicFiberWitness.CompleteIsogenyQuotientInput
    intro E K _ _ _ _ _ _ _ s hs hdegree P hP iota κ₀ hemb N _ hN M hM hC
      L _ _ κ q _ j aE hsplit h labels hlabels a ha hdominant hcop hpol hFiniteDescent
    exact (integralHeckeFamily_iff_fiberWitness M hM κ₀ hC j aE hsplit hs hdegree h labels hlabels
      a ha hdominant hcop hpol hFiniteDescent).mp
        (hNative s hs hdegree P hP iota κ₀ hemb N hN M hM hC q j aE hsplit h labels hlabels
          a ha hdominant hcop hpol hFiniteDescent)

theorem completeIsogenyQuotientInput_of_native : IntrinsicFiberWitness.CompleteIsogenyQuotientInput :=
  completeIsogenyQuotientInput_iff_native.mpr fullIsogenyQuotientInput_of_native

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.Faithfulness
