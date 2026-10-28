import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedSelfAnnihilator
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BundleSelfAnnihilatorTransport

/-! # Canonical Poincare Bundle -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPoincareBundle.Construction

noncomputable section

/-! The constructed full quotient has exactly the independently
prescribed kernel and satisfies PoincareBundle's canonical scheme-theoretic
self-annihilation hypothesis. -/

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

abbrev canonicalFullQuotientKernelBound :=
  (Canonical.Construction.canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H).kernel_killed (q ^ n)
    (Canonical.Construction.canonicalFullKernel_killed j iota hsplit A ρ hρ hgood n s labels hc P H)

theorem canonicalFullQuotient_kernel_iff_prescribed (T : Over (Spec (.of k)))
    (a : T ⟶ A.abelian.scheme) :
    a ≫ (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H).hom = 1 ↔
      Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H T a := by
  let Q := Canonical.Construction.canonicalFullKernelQuotient j iota hsplit A ρ hρ hgood n s labels hc P H
  constructor
  · intro ha
    exact (CanonicalPoints.Construction.canonicalFullKernel_realizes j iota hsplit A ρ hρ hgood n s labels hc P H T a).mp
      ((Q.kernel T a).mp ha).exists
  · intro ha
    obtain ⟨z, hz⟩ := (CanonicalPoints.Construction.canonicalFullKernel_realizes j iota hsplit A ρ hρ hgood n s labels hc P H T a).mpr ha
    exact (Q.kernel T a).mpr ⟨z, hz, fun w hw =>
      (cancel_mono (Canonical.Construction.canonicalFullKernelInclusion j iota hsplit A ρ hρ hgood n s labels hc P H)).mp
        (hw.trans hz.symm)⟩

abbrev canonicalFullKernel_e45SelfAnnihilating :=
  BundleSelfAnnihilatorTransport.Construction.e45SelfAnnihilating_of_original A (q ^ n) (pow_pos (Fact.out : q.Prime).pos n)
    (Canonical.Construction.canonicalFullQuotientIsogeny j iota hsplit A ρ hρ hgood n s labels hc P H).hom
    (canonicalFullQuotientKernelBound j iota hsplit A ρ hρ hgood n s labels hc P H)
    (Prescription.Construction.prescribedFullKernel j iota hsplit A ρ n s labels H)
    (canonicalFullQuotient_kernel_iff_prescribed j iota hsplit A ρ hρ hgood n s labels hc P H)
    (PrescribedSelfAnnihilator.Construction.prescribedFullKernel_selfAnnihilating j iota hsplit A ρ hρ hgood n s labels hc H P)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalPoincareBundle.Construction
