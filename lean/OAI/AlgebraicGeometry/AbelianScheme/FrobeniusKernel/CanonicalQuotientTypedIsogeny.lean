import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPoincareBundle
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientDualData
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPolarizedDescent

/-! # Canonical Quotient Typed Isogeny -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientTypedIsogeny.Construction

noncomputable section

/-! The actual full quotient and its constructed native dual carry a
unique descended isogeny of the original polarization type and the
original full pullback identity. Positivity remains a separate obligation. -/

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

abbrev canonicalFullQuotient_existsUnique_typedIsogeny :=
  Picard.PoincareBundle.Canonical.WeilPolarizedDescent.existsUnique_primePower_isogeny
    A.dual (CanonicalQuotientDualData.Construction.canonicalFullQuotientDualData j iota hsplit A ρ hρ hgood n s labels hc P H)
    A.polarization (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H)
    q n (Fact.out : q.Prime) hgood
    (CanonicalPoincareBundle.Construction.canonicalFullQuotientKernelBound j iota hsplit A ρ hρ hgood n s labels hc P H)
    (CanonicalPoincareBundle.Construction.canonicalFullKernel_e45SelfAnnihilating j iota hsplit A ρ hρ hgood n s labels hc P H)

def canonicalFullQuotientTypedIsogeny :=
  Classical.choose (canonicalFullQuotient_existsUnique_typedIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H)

abbrev canonicalFullQuotientTypedIsogeny_properties :=
  (Classical.choose_spec
    (canonicalFullQuotient_existsUnique_typedIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H)).1

abbrev canonicalFullQuotientTypedIsogeny_unique :=
  (Classical.choose_spec
    (canonicalFullQuotient_existsUnique_typedIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H)).2

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalQuotientTypedIsogeny.Construction
