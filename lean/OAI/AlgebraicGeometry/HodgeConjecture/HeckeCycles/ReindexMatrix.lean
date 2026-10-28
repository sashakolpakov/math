import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatrixUnitsMap
import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex

/-! # Reindex Matrix -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReindexMatrix.CM

noncomputable section

/-! Matrix identities for actual finite coordinate changes. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization
variable {I J K L : Type*} [Fintype I] [Fintype J] [CommRing K] [CommRing L]
  (e : I ≃ J)

def matrix (A : Matrix I I K) : Matrix J J K := Matrix.reindex e e A

omit [Fintype I] [Fintype J] [CommRing K] in
theorem apply (A : Matrix I I K) (i j : J) : matrix e A i j = A (e.symm i) (e.symm j) := rfl

omit [Fintype I] [Fintype J] [CommRing K] in
theorem transpose (A : Matrix I I K) : matrix e A.transpose = (matrix e A).transpose := rfl

omit [Fintype I] [Fintype J] in
theorem map (A : Matrix I I K) (f : K →+* L) : matrix e (A.map f) = (matrix e A).map f := rfl

omit [Fintype I] [Fintype J] in
theorem add (A B : Matrix I I K) : matrix e (A + B) = matrix e A + matrix e B := rfl

theorem mul (A B : Matrix I I K) : matrix e (A * B) = matrix e A * matrix e B :=
  (Matrix.reindexRingEquiv K e).map_mul A B

omit [Fintype I] [Fintype J] [CommRing K] in
theorem isSymm (A : Matrix I I K) (hA : A.IsSymm) : (matrix e A).IsSymm := by
  change (matrix e A).transpose = matrix e A
  rw [← CM.transpose, hA]

omit [Fintype I] [Fintype J] [CommRing K] in
theorem fromBlocks (A B C D : Matrix I I K) :
    Matrix.reindex (e.sumCongr e) (e.sumCongr e) (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (matrix e A) (matrix e B) (matrix e C) (matrix e D) := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;> rfl

theorem mulVec [TopologicalSpace K] (A : Matrix I I K) (x : I → K) :
    matrix e A *ᵥ RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x = RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e (A *ᵥ x) := by
  have h := Matrix.submatrix_mulVec_equiv A (fun j => x (e.symm j)) e.symm e.symm
  change A.submatrix e.symm e.symm *ᵥ (fun j => x (e.symm j)) = fun j => (A *ᵥ x) (e.symm j)
  simpa only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply] using h

variable [DecidableEq I] [DecidableEq J]

theorem one : matrix e (1 : Matrix I I K) = 1 := (Matrix.reindexRingEquiv K e).map_one

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem zero : matrix e (0 : Matrix I I K) = 0 := rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem neg (A : Matrix I I K) : matrix e (-A) = -matrix e A := rfl

theorem unit_val (A : (Matrix I I K)ˣ) :
    (MatrixUnitsMap.CM.map e (RingHom.id K) A).val = matrix e A.val := rfl

theorem unit_inv_val (A : (Matrix I I K)ˣ) :
    ((MatrixUnitsMap.CM.map e (RingHom.id K) A)⁻¹).val = matrix e (A⁻¹).val := by
  rw [← map_inv, unit_val]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReindexMatrix.CM
