import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientTypedIsogeny
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundleIntrinsicDualMap

/-! # Canonical Quotient Intrinsic Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientIntrinsicPullback.Construction

noncomputable section

/-! The constructed quotient isogeny satisfies the pullback equation in
the exact native Picard convention of the full quotient witness. -/

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

abbrev canonicalFullQuotientTypedIsogeny_nativePullback :=
  (BundleIntrinsicDualMap.Construction.IntrinsicPicardPullback.e45Pullback_eq
    (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H).hom
    A.dual (CanonicalQuotientDualData.Construction.canonicalFullQuotientDualData j iota hsplit A ρ hρ hgood n s labels hc P H)
    (CanonicalQuotientTypedIsogeny.Construction.canonicalFullQuotientTypedIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H).hom).symm.trans
    (CanonicalQuotientTypedIsogeny.Construction.canonicalFullQuotientTypedIsogeny_properties j iota hsplit A ρ hρ hgood n s labels hc P H).1

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientIntrinsicPullback.Construction
