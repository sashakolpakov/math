import OAI.RepresentationTheory.Theta.Geometric.Cleared.ReferenceTateLattice
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockCosetLatticeAction

/-! # Local Inverse Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The literal local preimage is the inverse-matrix full lattice used
by TateComparison's raw coset and relative-position classification. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockCosetLatticeAction

theorem Cleared.LocalInverseLattice.standardLocalLattice_eq_standardBlockLattice (q : ℕ) [Fact q.Prime] :
    Data.ActiveHeckeThetaData.standardLocalLattice (q := q) = AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.standardBlockLattice q := by
  have h : (Pi.basisFun ℚ_[q] (Fin 3) : Fin 3 → Fin 3 → ℚ_[q]) = fun i => Pi.single i 1 :=
    funext (Pi.basisFun_apply ℚ_[q] (Fin 3))
  exact congrArg (fun f : Fin 3 → Fin 3 → ℚ_[q] => Submodule.span ℤ_[q] (Set.range f)) h.symm

theorem Cleared.LocalInverseLattice.inverse_matrix_lattice_preimage (q : ℕ) [Fact q.Prime]
    (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) :
    (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockLatticeCosets.Construction.matrixBlockLattice q g⁻¹).val =
      (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.standardBlockLattice q).comap (g.val.mulVecLin.restrictScalars ℤ_[q]) := by
  have h := congrArg Subtype.val (AlgebraicGeometry.AbelianScheme.TateComparison.BlockCosetLatticeAction.matrixBlockLattice_mul q g⁻¹ 1)
  have h1 : AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockLatticeCosets.Construction.matrixBlockLattice q (1 : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) =
      AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionChoices.standardRankThreeLattice q := AlgebraicGeometry.AbelianScheme.TateComparison.BlockCosetLatticeAction.blockCosetToLattice_one q
  rw [h1, mul_one] at h
  change (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.standardBlockLattice q).map
    ((Matrix.GeneralLinearGroup.toLin g⁻¹).toLinearEquiv.toLinearMap.restrictScalars ℤ_[q]) = _ at h
  rw [← h]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g.val.mulVec ((g⁻¹).val.mulVec y) ∈ AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.standardBlockLattice q
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact hy
  · intro hx
    refine ⟨g.val.mulVec x, hx, ?_⟩
    change (g⁻¹).val.mulVec (g.val.mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}

def Data.ActiveHeckeThetaData.clearedLocalMatrix (g : D.RationalSU) (n : ℕ) (v : Fin s × Bool) :
    Matrix.GeneralLinearGroup (Fin 3) ℚ_[q] :=
  Matrix.GeneralLinearGroup.scalar (Fin 3) (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n) * Matrix.SpecialLinearGroup.toGL (D.localMatrix v g)

theorem Data.ActiveHeckeThetaData.clearedLocalMatrix_val (g : D.RationalSU) (n : ℕ) (v : Fin s × Bool) :
    (Data.ActiveHeckeThetaData.clearedLocalMatrix g n v).val = (q : ℚ_[q]) ^ n • (D.localMatrix v g).val := by
  change Matrix.scalar (Fin 3) ((AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.qUnit q ^ n).val) * (D.localMatrix v g).val = _
  ext i j
  simp only [Matrix.scalar_apply, Matrix.diagonal_mul]
  rfl

def Data.ActiveHeckeThetaData.clearedLocalInverseLattice (g : D.RationalSU) (n : ℕ) (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q] := AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockLatticeCosets.Construction.matrixBlockLattice q (Data.ActiveHeckeThetaData.clearedLocalMatrix g n v)⁻¹

theorem Data.ActiveHeckeThetaData.clearedLocalInverseLattice_val (g : D.RationalSU) (n : ℕ) (v : Fin s × Bool) :
    (Data.ActiveHeckeThetaData.clearedLocalInverseLattice g n v).val = Data.ActiveHeckeThetaData.clearedLocalPreimage g n v := by
  rw [Data.ActiveHeckeThetaData.clearedLocalInverseLattice, Cleared.LocalInverseLattice.inverse_matrix_lattice_preimage, Data.ActiveHeckeThetaData.clearedLocalMatrix_val,
    ← Cleared.LocalInverseLattice.standardLocalLattice_eq_standardBlockLattice]
  congr 1
  apply LinearMap.ext
  intro x
  exact Matrix.smul_mulVec ((q : ℚ_[q]) ^ n) (D.localMatrix v g).val x

end

end OAI.RepresentationTheory.Theta.Geometric
