import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientPELData
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIntegralLieRanks

/-! # Canonical Quotient Lie Ranks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientLieRanks.Construction

noncomputable section

/-! The actual canonical quotient preserves the complete original
integral PEL Lie predicate on every geometric field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k R : Type} [Field k] [IsAlgClosed k] [CharP k q] [CommRing R] {s N : ℕ}
  (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hgood : q.Coprime (∏ i, P.polarizationType i))
  (n : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
  (hc : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
  (C : ∀ v : Fin s, CartierModel.Construction.CartierCoordinates (.of k)
    (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
  (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
    (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
  (hN : q.Coprime N)
  (iotaO : NumberField.RingOfIntegers E →+* R) (t : Spec (.of k) ⟶ Spec (.of R))
  (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ (3 * s))
  (hr : PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO (Over.mk t) A.abelian ρ)

include hordinary hr in
theorem canonicalFullQuotient_integralLieRanks :
    PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO (Over.mk t)
      (CanonicalQuotientPELData.Construction.canonicalFullQuotientPolarized j iota hsplit A ρ hρ hgood n s labels hc C H hN).abelian
      (CanonicalAction.Construction.canonicalFullQuotientAction j iota hsplit A ρ hρ hgood n s labels hc C H) :=
  OrdinaryIntegralLieRanks.Construction.ordinaryIsogeny_preserves_integralLieRanks j iota hsplit P iotaO t A
    (CanonicalQuotientPELData.Construction.canonicalFullQuotientPolarized j iota hsplit A ρ hρ hgood n s labels hc C H hN) ρ
    (CanonicalAction.Construction.canonicalFullQuotientAction j iota hsplit A ρ hρ hgood n s labels hc C H)
    (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc C H)
    (fun a => (CanonicalAction.Construction.canonicalFullQuotientAction_intertwines j iota hsplit A ρ hρ hgood n s labels hc C H a).symm)
    hordinary n (CanonicalPoincareBundle.Construction.canonicalFullQuotientKernelBound j iota hsplit A ρ hρ hgood n s labels hc C H) hr

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientLieRanks.Construction
