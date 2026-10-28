import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeCosetConvolution
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitCosetRelativePositions

/-! # Lattice Neighbor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeNeighbor

noncomputable section

/-! Each ordinary lattice transition with its one prescribed scalar
transition occurs once in the raw local neighbor multiset. -/

open scoped Classical

variable (s q : ℕ) [Fact q.Prime]

def LatticeNeighborRelation (t : Local.IntegralType s) (x y : LatticeCosetConvolution.SplitLatticePoint s q) : Prop :=
  (∀ i, Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent i) (x.1 i) (y.1 i)) ∧
    x.2⁻¹ * y.2 = QuotientGroup.mk (HeckeKernel.qUnit q ^ (-t.val.multiplier))

theorem scalarCoset_smul_eq_mul (a : ℚ_[q]ˣ) (x : ℚ_[q]ˣ ⧸ SplitCosetComponents.scalarIntegralLevel q) :
    a • x = (QuotientGroup.mk a) * x := by
  induction x using Quotient.inductionOn with
  | h x => rfl

theorem splitRaw_translated_iff_neighborRelation (t : Local.IntegralType s) (g : HeckeKernel.SplitGroup s q)
    (x : HeckeKernel.SplitGroup s q ⧸ HeckeKernel.integralLevel s q) :
    g⁻¹ • x ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q t.val) ↔
      LatticeNeighborRelation s q t (SplitCosetComponents.splitCosetLatticeEquiv s q (QuotientGroup.mk g))
        (SplitCosetComponents.splitCosetLatticeEquiv s q x) := by
  rw [SplitCosetRelativePositions.splitRaw_translated_iff_positions]
  apply and_congr Iff.rfl
  change g.2⁻¹ • (SplitCosetComponents.splitCosetEquiv s q x).2 = _ ↔
    (QuotientGroup.mk g.2)⁻¹ * (SplitCosetComponents.splitCosetEquiv s q x).2 = _
  rw [scalarCoset_smul_eq_mul]
  rfl

theorem sphericalLatticeNeighbors_count (t : Local.IntegralType s) (x y : LatticeCosetConvolution.SplitLatticePoint s q) :
    (LatticeCosetConvolution.sphericalLatticeNeighbors s q t.val x).count y =
      if LatticeNeighborRelation s q t x y then 1 else 0 := by
  let e := SplitCosetComponents.splitCosetLatticeEquiv s q
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := e.surjective y
  change ((CosetNeighbors.sphericalCosetNeighbors s q t.val (e.symm (e x))).map e).count (e y) = _
  rw [e.symm_apply_apply, Multiset.count_map_eq_count' e _ e.injective]
  induction x using Quotient.inductionOn with
  | h g =>
    rw [CosetNeighbors.sphericalCosetNeighbors_count]
    have h := splitRaw_translated_iff_neighborRelation s q t g y
    change (if g⁻¹ • y ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q t.val) then 1 else 0) = _
    rw [h]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeNeighbor
