import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PoincareBundlePolarizationDescent
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientIntrinsicPullback

/-! # Canonical Quotient Polarization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientPolarization.Construction

noncomputable section

/-! The actual full quotient has its constructed native dual and a
polarization of the original type, positive on all geometric fibers.
Its underlying isogeny is the one already determined by full descent. -/

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

def canonicalFullQuotientPolarization :=
  PoincareBundlePolarizationDescent.Construction.e45DescendedPolarization A.dual
    (CanonicalQuotientDualData.Construction.canonicalFullQuotientDualData j iota hsplit A ρ hρ hgood n s labels hc P H)
    A.polarization (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H)
    (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) ((hgood.pow_right 2).pow_left n)
    (CanonicalPoincareBundle.Construction.canonicalFullQuotientKernelBound j iota hsplit A ρ hρ hgood n s labels hc P H)
    (CanonicalPoincareBundle.Construction.canonicalFullKernel_e45SelfAnnihilating j iota hsplit A ρ hρ hgood n s labels hc P H)

abbrev canonicalFullQuotientPolarization_e45Pullback :=
  PoincareBundlePolarizationDescent.Construction.e45DescendedPolarization_pullback A.dual
    (CanonicalQuotientDualData.Construction.canonicalFullQuotientDualData j iota hsplit A ρ hρ hgood n s labels hc P H)
    A.polarization (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H)
    (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) ((hgood.pow_right 2).pow_left n)
    (CanonicalPoincareBundle.Construction.canonicalFullQuotientKernelBound j iota hsplit A ρ hρ hgood n s labels hc P H)
    (CanonicalPoincareBundle.Construction.canonicalFullKernel_e45SelfAnnihilating j iota hsplit A ρ hρ hgood n s labels hc P H)

abbrev canonicalFullQuotientPolarization_nativePullback :=
  (BundleIntrinsicDualMap.Construction.IntrinsicPicardPullback.e45Pullback_eq
    (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H).hom
    A.dual (CanonicalQuotientDualData.Construction.canonicalFullQuotientDualData j iota hsplit A ρ hρ hgood n s labels hc P H)
    (canonicalFullQuotientPolarization j iota hsplit A ρ hρ hgood n s labels hc P H).isogeny.hom).symm.trans
    (canonicalFullQuotientPolarization_e45Pullback j iota hsplit A ρ hρ hgood n s labels hc P H)

theorem canonicalFullQuotientPolarization_isogeny_eq :
    (canonicalFullQuotientPolarization j iota hsplit A ρ hρ hgood n s labels hc P H).isogeny =
      CanonicalQuotientTypedIsogeny.Construction.canonicalFullQuotientTypedIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H :=
  CanonicalQuotientTypedIsogeny.Construction.canonicalFullQuotientTypedIsogeny_unique j iota hsplit A ρ hρ hgood n s labels hc P H _
    ⟨canonicalFullQuotientPolarization_e45Pullback j iota hsplit A ρ hρ hgood n s labels hc P H,
      (canonicalFullQuotientPolarization j iota hsplit A ρ hρ hgood n s labels hc P H).kernelType⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientPolarization.Construction
