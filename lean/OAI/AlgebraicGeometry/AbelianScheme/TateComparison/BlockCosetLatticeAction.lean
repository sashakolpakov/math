import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionChoices

/-! # Block Coset Lattice Action -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockCosetLatticeAction

noncomputable section

/-! Left translation of a raw GL3 coset is the actual linear
transport of its lattice. Relative positions are therefore exactly
translated raw double-coset membership. -/

open scoped Pointwise

variable (q : ℕ) [Fact q.Prime]

theorem matrixBlockLattice_mul (g h : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) :
    RelativePositionTransport.rankThreeLatticeEquiv (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv (IsogenyQuotient.BlockLatticeCosets.Construction.matrixBlockLattice q h) =
      IsogenyQuotient.BlockLatticeCosets.Construction.matrixBlockLattice q (g * h) := by
  apply Subtype.ext
  rw [RelativePositionTransport.rankThreeLatticeEquiv_val]
  change (Submodule.span ℤ_[q] (Set.range (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis h))).map _ = _
  rw [RelativePositionTransport.map_basis_span]
  congr 1
  congr 1
  ext i j
  simp [Module.Basis.map_apply, Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem blockCosetToLattice_smul (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q])
    (x : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q] ⧸ IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q) :
    IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q (g • x) =
      RelativePositionTransport.rankThreeLatticeEquiv (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv (IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q x) := by
  induction x using Quotient.inductionOn with
  | h h => exact (matrixBlockLattice_mul q g h).symm

theorem blockCosetToLattice_one :
    IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q (QuotientGroup.mk (1 : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q])) =
      RelativePositionChoices.standardRankThreeLattice q := by
  apply Subtype.ext
  change Submodule.span ℤ_[q] (Set.range (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis 1)) = _
  have h : Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis (1 : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) =
      Pi.basisFun ℚ_[q] (Fin 3) := by
    ext i j
    simp [Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis_apply, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [h]
  rfl

theorem blockRelativePosition_iff_raw_translate
    (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q])
    (y : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q] ⧸ IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q) (a : Fin 3 → ℕ) :
    Duality.RelativePosition (q : ℤ_[q]) (fun i => (a i : ℤ))
      (IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q (QuotientGroup.mk g)) (IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q y) ↔
        g⁻¹ • y ∈ IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q) (IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun i => (a i : ℤ))) := by
  have hx : IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q (QuotientGroup.mk g) =
      RelativePositionTransport.rankThreeLatticeEquiv (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv (RelativePositionChoices.standardRankThreeLattice q) := by
    have h := blockCosetToLattice_smul q g (QuotientGroup.mk (1 : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]))
    change IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q (QuotientGroup.mk (g * 1)) =
      RelativePositionTransport.rankThreeLatticeEquiv (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
        (IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q (QuotientGroup.mk (1 : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]))) at h
    simpa only [mul_one, blockCosetToLattice_one] using h
  have hy : IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q y =
      RelativePositionTransport.rankThreeLatticeEquiv (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
        (IsogenyQuotient.BlockLatticeCosets.Construction.blockLatticeCosetEquiv q (g⁻¹ • y)) := by
    simpa only [smul_inv_smul] using blockCosetToLattice_smul q g (g⁻¹ • y)
  rw [hx, hy, RelativePositionTransport.relativePosition_map_iff]
  exact (IsogenyQuotient.BlockHeckeChoices.Construction.raw_block_support_iff_smith q (g⁻¹ • y) a).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockCosetLatticeAction
