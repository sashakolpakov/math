import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSupport
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotient

/-! # Split Coset Relative Positions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitCosetRelativePositions

noncomputable section

/-! Raw split integral operators are precisely simultaneous ordinary
lattice relative positions with the prescribed single multiplier coset. -/

variable (s q : ℕ) [Fact q.Prime]

theorem splitCosetEquiv_smul (g : HeckeKernel.SplitGroup s q) (x : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q) :
    SplitCosetComponents.splitCosetEquiv s q (g • x) =
      ((fun i => g.1 i • (SplitCosetComponents.splitCosetEquiv s q x).1 i), g.2 • (SplitCosetComponents.splitCosetEquiv s q x).2) := by
  induction x using Quotient.inductionOn with
  | h x => rfl

theorem splitRaw_support_iff_positions (t : Local.IntegralType s)
    (x : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q) :
    x ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q t.val) ↔
      (∀ i, Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent i) (RelativePositionChoices.standardRankThreeLattice q)
        ((SplitCosetComponents.splitCosetLatticeEquiv s q x).1 i)) ∧
      (SplitCosetComponents.splitCosetEquiv s q x).2 = QuotientGroup.mk (HeckeKernel.qUnit q ^ (-t.val.multiplier)) := by
  rw [SplitSupport.split_raw_support_iff]
  apply and_congr
  · apply forall_congr'
    intro i
    change (SplitCosetComponents.splitCosetEquiv s q x).1 i ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q)
      (IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (t.val.exponent i)) ↔
      Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent i) (RelativePositionChoices.standardRankThreeLattice q)
        (IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q ((SplitCosetComponents.splitCosetEquiv s q x).1 i))
    have h := IsogenyQuotient.BlockHeckeChoices.Construction.raw_block_support_iff_smith q ((SplitCosetComponents.splitCosetEquiv s q x).1 i) (t.exponentNat i)
    simpa only [Local.IntegralType.exponentNat_cast, Duality.RelativePosition, IsogenyQuotient.LatticeBounds.Construction.diagonalLattice, RelativePositionChoices.standardRankThreeLattice] using h
  · exact (SplitSupport.scalar_raw_support_iff q (HeckeKernel.qUnit q ^ t.val.multiplier) ((SplitCosetComponents.splitCosetEquiv s q x).2)).trans
      (by rw [zpow_neg])

theorem splitRaw_translated_iff_positions (t : Local.IntegralType s) (g : HeckeKernel.SplitGroup s q)
    (x : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q) :
    g⁻¹ • x ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q t.val) ↔
      (∀ i, Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent i)
        ((SplitCosetComponents.splitCosetLatticeEquiv s q (QuotientGroup.mk g)).1 i) ((SplitCosetComponents.splitCosetLatticeEquiv s q x).1 i)) ∧
      g.2⁻¹ • (SplitCosetComponents.splitCosetEquiv s q x).2 = QuotientGroup.mk (HeckeKernel.qUnit q ^ (-t.val.multiplier)) := by
  rw [SplitSupport.split_raw_support_iff, splitCosetEquiv_smul]
  apply and_congr
  · apply forall_congr'
    intro i
    change (g.1 i)⁻¹ • (SplitCosetComponents.splitCosetEquiv s q x).1 i ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q)
      (IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (t.val.exponent i)) ↔
      Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent i)
        (IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q (QuotientGroup.mk (g.1 i)))
        (IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q ((SplitCosetComponents.splitCosetEquiv s q x).1 i))
    have h := BlockCosetLatticeAction.blockRelativePosition_iff_raw_translate q (g.1 i) ((SplitCosetComponents.splitCosetEquiv s q x).1 i) (t.exponentNat i)
    simpa only [Local.IntegralType.exponentNat_cast] using h.symm
  · exact (SplitSupport.scalar_raw_support_iff q (HeckeKernel.qUnit q ^ t.val.multiplier)
      (g.2⁻¹ • (SplitCosetComponents.splitCosetEquiv s q x).2)).trans (by rw [zpow_neg])

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitCosetRelativePositions
