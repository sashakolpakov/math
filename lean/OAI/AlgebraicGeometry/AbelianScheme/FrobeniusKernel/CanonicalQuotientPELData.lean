import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientPolarization
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalAction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientRosatiCondition

/-! # Canonical Quotient PEL Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientPELData.Construction

noncomputable section

/-! Assemble the constructed polarization, full level and integral
action, and prove the original Rosati condition on the actual quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hgood : q.Coprime (∏ i, δ i))
  (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
  (hc : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
  (P : ∀ v : Fin s, CartierModel.Construction.CartierCoordinates (.of k)
    (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
  (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
    (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
  (hN : q.Coprime N)

def canonicalFullQuotientPolarized : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)) where
  abelian := (Canonical.Construction.canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).abelian
  dual := CanonicalQuotientDualData.Construction.canonicalFullQuotientDualData j iota hsplit A ρ hρ hgood n s labels hc P H
  polarization := CanonicalQuotientPolarization.Construction.canonicalFullQuotientPolarization j iota hsplit A ρ hρ hgood n s labels hc P H
  level := Canonical.Construction.canonicalFullQuotientLevel j iota hsplit A ρ hρ hgood n s labels hc P H hN

def canonicalFullQuotientActionData : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N (Spec (.of k)) where
  polarized := canonicalFullQuotientPolarized j iota hsplit A ρ hρ hgood n s labels hc P H hN
  action := CanonicalAction.Construction.canonicalFullQuotientAction j iota hsplit A ρ hρ hgood n s labels hc P H

theorem canonicalFullQuotientRosati :
    AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation
      (canonicalFullQuotientPolarized j iota hsplit A ρ hρ hgood n s labels hc P H hN)
      (CanonicalAction.Construction.canonicalFullQuotientAction j iota hsplit A ρ hρ hgood n s labels hc P H) :=
  QuotientRosatiCondition.Construction.quotient_rosati A
    (canonicalFullQuotientPolarized j iota hsplit A ρ hρ hgood n s labels hc P H hN)
    (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H) ρ
    (CanonicalAction.Construction.canonicalFullQuotientAction j iota hsplit A ρ hρ hgood n s labels hc P H)
    (fun a => (CanonicalAction.Construction.canonicalFullQuotientAction_intertwines j iota hsplit A ρ hρ hgood n s labels hc P H a).symm)
    (q ^ n) (CanonicalQuotientPolarization.Construction.canonicalFullQuotientPolarization_nativePullback j iota hsplit A ρ hρ hgood n s labels hc P H) hρ

theorem canonicalFullQuotientPolarized_pullback :
    PolarizationComparison.Construction.polarizationPullbackHom
      (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H).hom A.dual
      (canonicalFullQuotientPolarized j iota hsplit A ρ hρ hgood n s labels hc P H hN).dual
      (canonicalFullQuotientPolarized j iota hsplit A ρ hρ hgood n s labels hc P H hN).polarization =
        A.polarization.isogeny.hom ^ (q ^ n) :=
  CanonicalQuotientPolarization.Construction.canonicalFullQuotientPolarization_nativePullback j iota hsplit A ρ hρ hgood n s labels hc P H

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientPELData.Construction
