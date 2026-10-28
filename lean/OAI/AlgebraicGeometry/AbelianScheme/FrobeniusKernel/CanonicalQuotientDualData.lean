import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Canonical
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualExistence

/-! # Canonical Quotient Dual Data -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientDualData.Construction

noncomputable section

/-! Construct native dual data for the actual full chosen/annihilator
quotient, using its proved multiplier bound on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [NumberField.IsCMField E] [Field K] [NumberField K]
variable {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
variable (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) (hgood : q.Coprime (∏ i, δ i))
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (hc : ∀ v, labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
variable (P : ∀ v : Fin s, CartierModel.Construction.CartierCoordinates (.of k)
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))
variable (H : ∀ v : Fin s, FiniteCartierSubgroupTransport.Construction.FiniteCartierSubgroup k
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ (labels (v, false)) n))

def canonicalFullQuotientDualData :
    AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData (Canonical.Construction.canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).abelian :=
  QuotientDualExistence.Construction.isogenousQuotientDualData A.dual A.polarization.isogeny
    (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H)
    (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)
    ((Canonical.Construction.canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).kernel_killed (q ^ n)
      (Canonical.Construction.canonicalFullKernel_killed j iota hsplit A ρ hρ hgood n s labels hc P H))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientDualData.Construction
