import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockHeightRank
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryBlockRank

/-! # Block Factor Heights -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockFactorHeights.CM

noncomputable section

/-! The dimensions of any constructed ordinary splitting of the original
coefficient block add up to its genuine q-divisible height. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (τ : Gal(E/ℚ))

theorem sum_eq_height (h : ℕ)
    (hheight : PELModuli.CMPoints.BlocksProjectors.BlockHasHeight A ρ (j.localCharacter iota τ) h)
    (n : ℕ) [IsFinite (A.torsionScheme (q ^ (n + 1))).hom] {d r : ℕ}
    (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp q (n + 1) d r) :
    d + r = h := by
  have hr := BlockHeightRank.CM.block_finrank j iota hsplit A ρ τ h hheight
    (n + 1) (IsLocalRing.closedPoint k)
  have hs := Isogenies.NeighborCounting.OrdinaryBlockRank.Ordinary.ordinaryBlock_rank k q (n + 1) e (IsLocalRing.closedPoint k)
  have he : (q ^ (n + 1)) ^ (d + r) = (q ^ (n + 1)) ^ h :=
    hs.symm.trans (hr.trans (pow_mul q (n + 1) h))
  exact Nat.pow_right_injective
    (one_lt_pow' (Fact.out : q.Prime).one_lt (Nat.succ_ne_zero n)) he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockFactorHeights.CM
