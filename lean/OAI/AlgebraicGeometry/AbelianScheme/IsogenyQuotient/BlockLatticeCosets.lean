import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SuperlatticeType

/-! # Block Lattice Cosets -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockLatticeCosets.Construction

noncomputable section

/-!
Right cosets GL3(Q_q)/GL3(Z_q) classify actual full rank-three lattices.
Equality of lattice spans gives an integral change of basis, so no lattice
marking or choice of basis is retained by this classification.
-/

open _root_.Module

open OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction

variable (q : ℕ) [Fact q.Prime]

abbrev BlockBasis := Basis (Fin 3) ℚ_[q] (Fin 3 → ℚ_[q])
abbrev BlockLattice := {L : Submodule ℤ_[q] (Fin 3 → ℚ_[q]) // Submodule.IsLattice ℚ_[q] L}

def blockIntegralLevel : Subgroup (Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) :=
  (Matrix.GeneralLinearGroup.map (n := Fin 3) (PadicInt.Coe.ringHom (p := q))).range

def blockBasisChange (e f : BlockBasis q) : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q] where
  val := e.toMatrix f
  inv := f.toMatrix e
  val_inv := e.toMatrix_mul_toMatrix_flip f
  inv_val := f.toMatrix_mul_toMatrix_flip e

theorem blockBasisChange_mul (e f b : BlockBasis q) :
    blockBasisChange q e f * blockBasisChange q f b = blockBasisChange q e b := by
  apply Units.ext
  exact e.toMatrix_mul_toMatrix f b

theorem blockBasisChange_matrixBasis (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) :
    blockBasisChange q (Pi.basisFun ℚ_[q] (Fin 3)) (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis g) = g := by
  apply Units.ext
  exact Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.standard_toMatrix_matrixBasis g

theorem matrixBasis_blockBasisChange (e : BlockBasis q) :
    Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis (blockBasisChange q (Pi.basisFun ℚ_[q] (Fin 3)) e) = e := by
  ext i j
  simp [Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis_apply, blockBasisChange, Basis.toMatrix_apply]

theorem blockBasisChange_between_matrixBases
    (g k : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) :
    blockBasisChange q (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis g) (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis k) = g⁻¹ * k := by
  apply mul_left_cancel (a := g)
  rw [mul_inv_cancel_left]
  nth_rw 1 [← blockBasisChange_matrixBasis q g]
  rw [blockBasisChange_mul, blockBasisChange_matrixBasis]

def matrixBlockLattice (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) : BlockLattice q :=
  ⟨Submodule.span ℤ_[q] (Set.range (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis g)), Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.basis_span_isLattice (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis g)⟩

theorem matrixBlockLattice_eq_iff (g k : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) :
    matrixBlockLattice q g = matrixBlockLattice q k ↔ g⁻¹ * k ∈ blockIntegralLevel q := by
  constructor
  · intro he
    obtain ⟨U, hU⟩ := Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.integral_basis_change (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis g) (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis k)
      (congrArg Subtype.val he)
    refine ⟨U, ?_⟩
    rw [← blockBasisChange_between_matrixBases]
    apply Units.ext
    exact hU.symm
  · rintro ⟨U, hU⟩
    apply Subtype.ext
    apply Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.basis_span_eq_of_toMatrix_map (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis g) (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis k) U
    have hh := congrArg Units.val ((blockBasisChange_between_matrixBases q g k).trans hU.symm)
    exact hh

def blockCosetToLattice :
    Matrix.GeneralLinearGroup (Fin 3) ℚ_[q] ⧸ blockIntegralLevel q → BlockLattice q :=
  Quotient.lift (matrixBlockLattice q) (by
    intro g k hrel
    exact (matrixBlockLattice_eq_iff q g k).mpr (QuotientGroup.leftRel_apply.mp hrel))

@[simp] theorem blockCosetToLattice_mk (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) :
    blockCosetToLattice q (QuotientGroup.mk g) = matrixBlockLattice q g := rfl

theorem blockCosetToLattice_injective : Function.Injective (blockCosetToLattice q) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h g =>
    induction y using Quotient.inductionOn with
    | h k =>
      intro he
      exact Quotient.sound (QuotientGroup.leftRel_apply.mpr
        ((matrixBlockLattice_eq_iff q g k).mp he))

theorem blockCosetToLattice_surjective : Function.Surjective (blockCosetToLattice q) := by
  intro L
  let : Submodule.IsLattice ℚ_[q] L.val := L.property
  have hr : Module.finrank ℤ_[q] L.val = 3 := by
    simpa using Submodule.IsLattice.finrank_of_pi ℚ_[q] L.val
  let b := Module.finBasisOfFinrankEq ℤ_[q] L.val hr
  let e := b.extendOfIsLattice ℚ_[q]
  refine ⟨QuotientGroup.mk (blockBasisChange q (Pi.basisFun ℚ_[q] (Fin 3)) e), ?_⟩
  apply Subtype.ext
  change Submodule.span ℤ_[q] (Set.range (Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.matrixBasis (blockBasisChange q _ e))) = L.val
  rw [matrixBasis_blockBasisChange]
  exact Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.extended_basis_span b

/-- A full lattice is exactly an unmarked right coset of the integral level. -/
def blockLatticeCosetEquiv :
    Matrix.GeneralLinearGroup (Fin 3) ℚ_[q] ⧸ blockIntegralLevel q ≃ BlockLattice q :=
  Equiv.ofBijective (blockCosetToLattice q)
    ⟨blockCosetToLattice_injective q, blockCosetToLattice_surjective q⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockLatticeCosets.Construction
