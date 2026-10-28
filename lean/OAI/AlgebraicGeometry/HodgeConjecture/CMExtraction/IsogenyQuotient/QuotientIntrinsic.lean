import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntegralHecke
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has

/-! # Quotient Intrinsic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.QuotientIntrinsic

noncomputable section

/-! The full native IsogenyQuotient input, before any retained-model specialization.

`IntegralHeckeFamily` retains the representing natural isomorphism, source
compatibility, finite étale source, actual full chosen/opposite kernel,
maximal isotropy, polarized quotient with integral action and full ordered
marking, and equality with the independent raw-Hecke target multiset.
The same witnesses occur in every clause. Its fine-model component data
are the full ReferenceFamily output already retained before choosing the prime.

The historical `Statements/IsogenyQuotient.lean` at a35640857a4b14455eb1da308ad591d863ae2117
is a proposed, nonelaboratable interface. It is not imported as evidence.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntegralHecke.Construction

def FullIsogenyQuotientInput : Prop :=
  ∀ {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] [CharZero K]
    (s : ℕ) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (_hP : P.IsAdmissible)
    (iota : E →+* K) (κ₀ : K →+* ℂ) (_hemb : κ₀.comp iota = P.μ)
    (N : ℕ) [NeZero N] (_hN : PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P N)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
    (hC : M.HasProjectiveBallComponents κ₀)
    {L : Type} [Field L] [NumberField L] {κ : L →+* ℂ}
    (q : ℕ) [Fact q.Prime] (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q)
    (arithmeticEmbedding : E →+* L) (hsplit : j.HasSplitCoordinates arithmeticEmbedding)
    (h : ℕ) (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
    (hlabels : ∀ i, labels (Sum.swap i) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels i)
    (a : Fin s → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h) (hdominant : ∀ v, Antitone (a v))
    (hcop : Nat.Coprime q N) (hpol : Nat.Coprime q (∏ i, P.polarizationType i))
    (hFiniteDescent : AbelianScheme.IsogenyQuotient.IsogenyComplement.Construction.FiniteDescentInput.{0}),
    AbelianScheme.IsogenyQuotient.IntegralHecke.Construction.IntegralHeckeFamily M hM κ₀ hC j arithmeticEmbedding hsplit hs hdegree h labels hlabels
      a ha hdominant hcop hpol hFiniteDescent

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.QuotientIntrinsic
