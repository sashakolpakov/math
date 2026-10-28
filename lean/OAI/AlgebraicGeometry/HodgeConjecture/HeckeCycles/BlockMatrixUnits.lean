import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ElementaryMatrixUnits
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Block Matrix Units -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockMatrixUnits.CM

/-! Block triangular units and their membership in subgroups generated
by symmetric matrices. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ElementaryMatrixUnits.CM
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {R : Type*} [CommRing R]

def transposeUnit (A : (Matrix I I R)ˣ) : (Matrix I I R)ˣ where
  val := A.val.transpose
  inv := (A⁻¹).val.transpose
  val_inv := by
    change A.val.transpose * A.inv.transpose = 1
    rw [← transpose_mul, A.inv_val, transpose_one]
  inv_val := by
    change A.inv.transpose * A.val.transpose = 1
    rw [← transpose_mul, A.val_inv, transpose_one]

theorem transposeUnit_one : transposeUnit (1 : (Matrix I I R)ˣ) = 1 := by
  apply Units.ext
  exact transpose_one

theorem transposeUnit_mul (A B : (Matrix I I R)ˣ) :
    transposeUnit (A * B) = transposeUnit B * transposeUnit A := by
  apply Units.ext
  exact transpose_mul _ _

theorem transposeUnit_inv (A : (Matrix I I R)ˣ) :
    transposeUnit A⁻¹ = (transposeUnit A)⁻¹ := rfl

def transposeSubgroup (H : Subgroup (Matrix I I R)ˣ) : Subgroup (Matrix I I R)ˣ where
  carrier := {A | transposeUnit A ∈ H}
  one_mem' := by simp [transposeUnit_one]
  mul_mem' := by
    intro A B hA hB
    change transposeUnit (A * B) ∈ H
    rw [transposeUnit_mul]
    exact H.mul_mem hB hA
  inv_mem' := by
    intro A hA
    change transposeUnit A⁻¹ ∈ H
    rw [transposeUnit_inv]
    exact H.inv_mem hA

theorem transposeSubgroup_symmetric (H : Subgroup (Matrix I I R)ˣ)
    (hSym : ∀ A : (Matrix I I R)ˣ, A.val.IsSymm → A ∈ H)
    (A : (Matrix I I R)ˣ) (hA : A.val.IsSymm) : A ∈ transposeSubgroup H := by
  have he : transposeUnit A = A := Units.ext hA
  change transposeUnit A ∈ H
  rw [he]
  exact hSym A hA

def lowerUnit (C : Matrix J I R) : (Matrix (I ⊕ J) (I ⊕ J) R)ˣ where
  val := fromBlocks 1 0 C 1
  inv := fromBlocks 1 0 (-C) 1
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

def upperUnit (B : Matrix I J R) : (Matrix (I ⊕ J) (I ⊕ J) R)ˣ where
  val := fromBlocks 1 B 0 1
  inv := fromBlocks 1 (-B) 0 1
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

theorem lowerUnit_row (C : Matrix Unit I R) :
    lowerUnit C = ElementaryMatrixUnits.CM.rowUnit (Sum.inr ()) (Sum.elim (C ()) (fun _ => 0)) (by rfl) := by
  apply Units.ext
  ext a b
  cases a <;> cases b <;> simp [lowerUnit, ElementaryMatrixUnits.CM.rowUnit, ElementaryMatrixUnits.CM.rowMatrix, Matrix.one_apply]

theorem lowerUnit_mem (H : Subgroup (Matrix (I ⊕ Unit) (I ⊕ Unit) R)ˣ)
    (hSym : ∀ A : (Matrix (I ⊕ Unit) (I ⊕ Unit) R)ˣ, A.val.IsSymm → A ∈ H)
    (C : Matrix Unit I R) : lowerUnit C ∈ H := by
  rw [lowerUnit_row]
  exact ElementaryMatrixUnits.CM.rowUnit_mem H hSym _ _ _

theorem upperUnit_transpose (B : Matrix I J R) :
    upperUnit B = transposeUnit (lowerUnit B.transpose) := by
  apply Units.ext
  simp [upperUnit, transposeUnit, lowerUnit, fromBlocks_transpose]

theorem upperUnit_mem (H : Subgroup (Matrix (I ⊕ Unit) (I ⊕ Unit) R)ˣ)
    (hSym : ∀ A : (Matrix (I ⊕ Unit) (I ⊕ Unit) R)ˣ, A.val.IsSymm → A ∈ H)
    (B : Matrix I Unit R) : upperUnit B ∈ H := by
  rw [upperUnit_transpose]
  exact lowerUnit_mem (transposeSubgroup H) (transposeSubgroup_symmetric H hSym) B.transpose

def blockDiagonal (A : (Matrix I I R)ˣ) (D : (Matrix J J R)ˣ) :
    (Matrix (I ⊕ J) (I ⊕ J) R)ˣ where
  val := fromBlocks A.val 0 0 D.val
  inv := fromBlocks (A⁻¹).val 0 0 (D⁻¹).val
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

def embedLeft : (Matrix I I R)ˣ →* (Matrix (I ⊕ J) (I ⊕ J) R)ˣ where
  toFun A := blockDiagonal A 1
  map_one' := by apply Units.ext; simp [blockDiagonal, fromBlocks_one]
  map_mul' A B := by apply Units.ext; simp [blockDiagonal, fromBlocks_multiply]

theorem embedLeft_symmetric (A : (Matrix I I R)ˣ) (hA : A.val.IsSymm) :
    (embedLeft (J := J) A).val.IsSymm :=
  hA.fromBlocks (by simp) (by simp)

theorem blockDiagonal_eq (A : (Matrix I I R)ˣ) (D : (Matrix J J R)ˣ) :
    blockDiagonal A D = embedLeft A * blockDiagonal 1 D := by
  apply Units.ext
  simp [embedLeft, blockDiagonal, fromBlocks_multiply]

theorem unit_block_symmetric (D : (Matrix Unit Unit R)ˣ) :
    (blockDiagonal (1 : (Matrix I I R)ˣ) D).val.IsSymm := by
  apply Matrix.IsSymm.fromBlocks (by simp) (by simp)
  ext i j
  cases i
  cases j
  rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockMatrixUnits.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockMatrixUnits.CM.UnitPivotFactorization

/-! An invertible matrix with a unit pivot factors into two elementary
block shears and a smaller invertible block. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockMatrixUnits.CM
variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

theorem exists_block_factorization (M : (Matrix (I ⊕ Unit) (I ⊕ Unit) R)ˣ)
    (h : IsUnit (M.val (Sum.inr ()) (Sum.inr ()))) :
    ∃ (B : Matrix I Unit R) (C : Matrix Unit I R)
      (A : (Matrix I I R)ˣ) (D : (Matrix Unit Unit R)ˣ),
      M = upperUnit B * blockDiagonal A D * lowerUnit C := by
  have hD : IsUnit M.val.toBlocks₂₂ := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_unique]
    convert h using 2
    congr 2
  let := hD.invertible
  have hA : IsUnit (M.val.toBlocks₁₁ -
      M.val.toBlocks₁₂ * ⅟M.val.toBlocks₂₂ * M.val.toBlocks₂₁) := by
    apply Matrix.isUnit_fromBlocks_iff_of_invertible₂₂.mp
    simpa only [Matrix.fromBlocks_toBlocks] using M.isUnit
  obtain ⟨A, hA⟩ := hA
  obtain ⟨D, hD⟩ := hD
  refine ⟨M.val.toBlocks₁₂ * ⅟M.val.toBlocks₂₂,
    ⅟M.val.toBlocks₂₂ * M.val.toBlocks₂₁, A, D, ?_⟩
  apply Units.ext
  change M.val = fromBlocks 1 _ 0 1 * fromBlocks A.val 0 0 D.val * fromBlocks 1 0 _ 1
  rw [hA, hD]
  exact (Matrix.fromBlocks_toBlocks M.val).symm.trans
    (Matrix.fromBlocks_eq_of_invertible₂₂ _ _ _ _)

theorem mem_of_unit_pivot (H : Subgroup (Matrix (I ⊕ Unit) (I ⊕ Unit) R)ˣ)
    (hSym : ∀ A : (Matrix (I ⊕ Unit) (I ⊕ Unit) R)ˣ, A.val.IsSymm → A ∈ H)
    (hLeft : ∀ A : (Matrix I I R)ˣ, embedLeft A ∈ H)
    (M : (Matrix (I ⊕ Unit) (I ⊕ Unit) R)ˣ)
    (h : IsUnit (M.val (Sum.inr ()) (Sum.inr ()))) : M ∈ H := by
  obtain ⟨B, C, A, D, he⟩ := exists_block_factorization M h
  rw [he, blockDiagonal_eq]
  exact H.mul_mem (H.mul_mem (upperUnit_mem H hSym B)
    (H.mul_mem (hLeft A) (hSym _ (unit_block_symmetric D)))) (lowerUnit_mem H hSym C)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockMatrixUnits.CM.UnitPivotFactorization

end

end OAI
