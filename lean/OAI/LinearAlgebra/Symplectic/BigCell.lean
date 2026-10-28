/-
Copyright (c) 2022 Matej Penciak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matej Penciak, Moritz Doll, Fabien Clery, Seed Prover, Huanyu Zheng
This file has been modified.
-/
import Mathlib.LinearAlgebra.SymplecticGroup

/-! # Big Cell -/

namespace OAI.LinearAlgebra.Symplectic.BigCell.SymplecticBigCell

noncomputable section

/-! Ordinary big-cell proofs from the Mathlib, exposed here
for reuse without accessing private declarations through metaprogramming. -/
open _root_.Matrix SymplecticGroup
variable {l R : Type*} [Fintype l] [DecidableEq l] [CommRing R]
variable {A B C D : Matrix l l R}
private lemma exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot {R : Type*} [Field R]
    {A C : Matrix l l R} (hker : ∀ (x : l → R), (A • x = 0) → (C • x = 0) → x = 0)
    (hsymm : Aᵀ * C = Cᵀ * A) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C) := by
  -- `C` is transformed into `P = fromBlocks 1 0 0 0` by invertible matrices `V` and `U`.
  rcases exists_rank_normal_form C with ⟨V, U, s, hV, hU, heq⟩
  set P := V * C * U with P_def; set Q := Vᵀ⁻¹ * A * U with Q_def
  set f := fun (x : Matrix l l R) ↦ x.submatrix s.symm s.symm
  have hf (x) : f x = x.submatrix s.symm s.symm := rfl
  have f_unit {x} : IsUnit x → IsUnit (f x) := (isUnit_submatrix_equiv ..).2
  have f_mul (x y) : f (x * y) = f x * f y := submatrix_mul _ _ _ _ _ s.symm.bijective
  have _ : Invertible V := hV.invertible
  have _ : Invertible U := hU.invertible
  have _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
  -- The hypothesis that the only vector annihilated by both matrices is 0, holds for `P` and `Q`.
  have con1 (x : Fin C.rank ⊕ Fin (Fintype.card l - C.rank) → R)
      (heq1 : (f Q) • x = 0) (heq2 : (f P) • x = 0) : x = 0 := by
    refine (f_unit hU).smul_left_cancel.1 ?_
    rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
      smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at heq1 heq2
    · rw [Equiv.comp_symm_eq, Pi.zero_comp] at heq1 heq2
      exact s.surjective.injective_comp_right <| by simpa using hker _ heq1 heq2
    · exact f_unit hV
    · exact f_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
  -- The symmetry relation also holds for `P` and `Q`.
  have con2 : Qᵀ * P = Pᵀ * Q := by
    simp only [P_def, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, Q_def,
      inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
    rw [← mul_assoc Aᵀ, hsymm, mul_assoc]
  replace con2 : (f Q).toBlocks₁₁ᵀ = (f Q).toBlocks₁₁ ∧ (f Q).toBlocks₁₂ = 0 := by
    apply_fun reindex s s at con2
    rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Pᵀ, heq, hf,
      ← transpose_submatrix, ← hf Q, ← (f Q).fromBlocks_toBlocks, hf (_)ᵀ, hf
      ((fromBlocks 1 0 0 0).submatrix _ _)] at con2
    simp [fromBlocks_transpose, fromBlocks_multiply] at con2; tauto
  -- The lower-right block of `Q` is invertible.
  have con3 : IsUnit (f Q).toBlocks₂₂ := by
    refine mulVec_injective_iff_isUnit.1 ?_
    rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
    refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
      (con1 _ ?_ ?_).trans Sum.elim_zero_zero.symm
    · rw [← (f Q).fromBlocks_toBlocks]; simp [hx, con2.2, fromBlocks_mulVec]
    · simp [hf, heq, fromBlocks_mulVec]
  set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card l - C.rank)) (Fin C.rank ⊕
    Fin (Fintype.card l - C.rank)) R := fromBlocks (1 - (f Q).toBlocks₁₁) 0 0 0 with Y_def
  have hY_symm : Y.IsSymm := by
    rw [Y_def, isSymm_fromBlocks_iff]
    exact ⟨IsSymm.sub isSymm_one con2.1, by simp⟩
  -- We now take `X = Vᵀ * Y * V` and this gives the desired matrix `X.submatrix s s`.
  set X := (f Vᵀ) * Y * (f V) with X_def
  refine ⟨X.submatrix s s, IsSymm.submatrix ?_ s, (isUnit_submatrix_equiv s.symm s.symm).1 ?_⟩
  · simp_rw [X_def, Matrix.IsSymm, transpose_mul, hY_symm.eq, hf, transpose_submatrix,
      transpose_transpose, mul_assoc]
  · have heq' : f (A + X.submatrix s s * C) = (f Vᵀ) * (f Q + Y * (f P)) * f (U⁻¹) := by
      simp_rw [hf, submatrix_add, Pi.add_apply, Q_def, P_def, ← hf, f_mul, hf, mul_add, ← mul_assoc,
        ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
      simp [X_def]; rfl
    rw [← hf, heq', IsUnit.mul_iff, IsUnit.mul_iff]
    refine ⟨⟨isUnit_of_invertible _, ?_⟩, ?_⟩
    · nth_rw 1 [Y_def, heq, ← (f Q).fromBlocks_toBlocks, con2.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add]
    · exact f_unit <| isUnit_nonsing_inv_iff.2 hU

/-- For any symplectic matrix `fromBlocks A B C D` over a local ring `R`, we can construct
a symmetric `X` s.t. `A + X * C` is invertible.

Introducing local ring hypothesis enables us to transport the construction of `X`
(from the previous lemma, which works only over fields) back to `R` while keeping
`A + X * C` invertible. -/
theorem exists_symmetric_X_isUnit_det_add_mul_of_symplectic [IsLocalRing R]
    (hA : fromBlocks A B C D ∈ symplecticGroup l R) :
    ∃ (X : Matrix l l R), X.IsSymm ∧ IsUnit (A + X * C).det := by
  -- We utilize the previous result on field by mapping the symplectic matrix to residue field.
  set k := IsLocalRing.ResidueField R; set f := IsLocalRing.residue R
  set A' := f.mapMatrix A; set C' := f.mapMatrix C
  set F' := fromBlocks A' (f.mapMatrix B) C' (f.mapMatrix D) with F'_def
  have hF' : IsUnit F' := by
    refine F'.isUnit_iff_isUnit_det.2 ?_
    convert (symplectic_det hA).map f
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.fromBlocks_map]; rfl
  have hker (x : l → k) (hx1 : A' *ᵥ x = 0) (hx2 : C' *ᵥ x = 0) : x = 0 := by
    have hv0 : F' *ᵥ (Sum.elim x 0) = F' *ᵥ (Sum.elim 0 0) := by
      simp [fromBlocks_mulVec, hx1, hx2, F'_def]
    exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hF' hv0)).1
  -- Now we have a symmetric matrix `Y` over the residue field s.t. `A' + Y * C'` is invertible
  -- where `A'` and `C'` are images of `A` and `C` under quotient map from `R` to its residue field.
  obtain ⟨Y, hY_symm, hY_det⟩ :=
    exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot hker <| by
      change f.mapMatrix Aᵀ * f.mapMatrix C = f.mapMatrix Cᵀ * f.mapMatrix A
      rw [← map_mul, (fromBlocks_mem_iff.1 hA).1, map_mul]
  -- Lift `Y` back to the ring `R` and we have the `X` we need.
  obtain ⟨X, hX_symm, hXY⟩ : ∃ X : Matrix l l R, X.IsSymm ∧ X.map f = Y := by
    choose s hs using @IsLocalRing.residue_surjective R _ _
    exact ⟨Y.map s, hY_symm.map s, Matrix.ext fun i j ↦ hs (Y i j)⟩
  refine ⟨X, hX_symm, (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_⟩
  -- Ensure `A + X * C` is still invertible in `R`.
  rw [RingHom.map_det, map_add, map_mul, RingHom.mapMatrix_apply _ X, hXY]
  exact ((isUnit_iff_isUnit_det _).1 hY_det).ne_zero

end

end OAI.LinearAlgebra.Symplectic.BigCell.SymplecticBigCell
