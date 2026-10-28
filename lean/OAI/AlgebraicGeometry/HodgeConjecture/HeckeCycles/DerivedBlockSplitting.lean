import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.BlockSplitting
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.MultiplicativeFactor

/-! # Derived Block Splitting -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DerivedBlockSplitting.CM

noncomputable section

/-! Derive the finite-level splitting of every original ordinary
coefficient block, with no ambient splitting supplied as an input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [IsAlgClosed k] [CharP k q] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

theorem exists_splitting
    (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ) (τ : Gal(E/ℚ)) :
    ∃ d r : ℕ, Nonempty (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A.abelian ρ (n + 1) τ).toGrp q (n + 1) d r) :=
  Ordinary.BlockSplitting.CM.exists_splitting_of_multiplicative_torsion j iota hsplit A ρ
    hordinary n τ (Ordinary.MultiplicativeFactor.CM.multiplicative_factor A q hordinary (n + 1))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DerivedBlockSplitting.CM
