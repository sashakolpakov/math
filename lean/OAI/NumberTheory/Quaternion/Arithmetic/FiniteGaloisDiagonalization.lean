import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! # Finite Galois Diagonalization -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteGaloisDiagonalization

noncomputable section

/-! A diagonalization using algebraic Galois coefficients is already
defined over a finite Galois intermediate field. -/

open scoped Classical
open _root_.Matrix

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [IsGalois F K] {n : ℕ}

theorem exists_finiteGalois_matrix_and_weights
    (B : Matrix.SpecialLinearGroup (Fin n) K) (w : Fin n → K) :
    ∃ L : FiniteGaloisIntermediateField F K,
      ∃ b : Matrix.SpecialLinearGroup (Fin n) L, ∃ z : Fin n → L,
        Matrix.SpecialLinearGroup.map (algebraMap L K) b = B ∧
          ∀ i, algebraMap L K (z i) = w i := by
  let s : Finset K := Finset.univ.image (fun ij : Fin n × Fin n => B ij.1 ij.2) ∪
    Finset.univ.image w
  let L := FiniteGaloisIntermediateField.adjoin F (s : Set K)
  have hB (i j : Fin n) : B i j ∈ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin F (s : Set K)
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hw (i : Fin n) : w i ∈ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin F (s : Set K)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  let b₀ : Matrix (Fin n) (Fin n) L := fun i j => ⟨B i j, hB i j⟩
  have hbmap : b₀.map (algebraMap L K) = (B : Matrix (Fin n) (Fin n) K) := rfl
  have hdet : b₀.det = 1 := by
    apply (algebraMap L K).injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hbmap, B.property, map_one]
  refine ⟨L, ⟨b₀, hdet⟩, fun i => ⟨w i, hw i⟩, ?_, fun _ => rfl⟩
  ext i j
  rfl

theorem exists_finiteGalois_diagonalization
    (S : Matrix (Fin n) (Fin n) F) (B : Matrix.SpecialLinearGroup (Fin n) K) (w : Fin n → K)
    (hS : S.map (algebraMap F K) = (B : Matrix (Fin n) (Fin n) K) * Matrix.diagonal w *
      ((B⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ L : FiniteGaloisIntermediateField F K,
      ∃ b : Matrix.SpecialLinearGroup (Fin n) L, ∃ z : Fin n → L,
        S.map (algebraMap F L) = (b : Matrix (Fin n) (Fin n) L) * Matrix.diagonal z *
          ((b⁻¹ : Matrix.SpecialLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  obtain ⟨L, b, z, hb, hz⟩ := exists_finiteGalois_matrix_and_weights (F := F) B w
  refine ⟨L, b, z, ?_⟩
  apply Matrix.map_injective (algebraMap L K).injective
  have hcoeff : (S.map (algebraMap F L)).map (algebraMap L K) = S.map (algebraMap F K) := by
    ext i j
    exact (IsScalarTower.algebraMap_apply F L K (S i j)).symm
  simp only [hcoeff, Matrix.map_mul, Matrix.diagonal_map (map_zero _)]
  have hbi : ((b⁻¹ : Matrix.SpecialLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L).map
      (algebraMap L K) = ((B⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    change ((Matrix.SpecialLinearGroup.map (algebraMap L K) b⁻¹ :
      Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
    rw [map_inv, hb]
  have hbm : (b : Matrix (Fin n) (Fin n) L).map (algebraMap L K) =
      (B : Matrix (Fin n) (Fin n) K) := congrArg Subtype.val hb
  simpa only [hbm, hbi, hz] using hS

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteGaloisDiagonalization
