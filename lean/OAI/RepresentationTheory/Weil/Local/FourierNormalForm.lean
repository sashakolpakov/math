import OAI.RepresentationTheory.Weil.Local.FourierBigCell

/-! # Fourier Normal Form -/

namespace OAI.RepresentationTheory.Weil.Local.FourierNormalForm.Construction

noncomputable section

section

/-! Quadratic–linear–Fourier normal forms on the invertible Fourier-block domain. -/

open _root_.Matrix

variable {k : Type} [Field k] {n : ℕ}

def fourierNormalForm (P : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B : FunctionsMetaplectic.Construction.GeneralLinear k n) (Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    FunctionsMetaplectic.Construction.Symplectic k n := Generators.Construction.quadraticSymplectic P * Generators.Construction.leviSymplectic B * Generators.Construction.weylSymplectic k n * Generators.Construction.quadraticSymplectic Q

theorem fourierNormalForm_matrix (P : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    (fourierNormalForm P B Q).val = Matrix.fromBlocks (B.val * Q.val) B.val
      (P.val * B.val * Q.val - B⁻¹.val.transpose) (P.val * B.val) := by
  change Matrix.fromBlocks 1 0 P.val 1 * Matrix.fromBlocks B.val 0 0 B⁻¹.val.transpose *
    Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 1 0 Q.val 1 = _
  simp only [Matrix.fromBlocks_multiply, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero,
    mul_neg, neg_zero]
  rw [sub_eq_add_neg, add_comm (-B⁻¹.val.transpose)]

theorem fourierNormalForm_mem (P : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) : fourierNormalForm P B Q ∈ FourierBigCell.Construction.fourierBigCell k n := by
  change (fourierNormalForm P B Q).val.toBlocks₁₂.det ≠ 0
  rw [fourierNormalForm_matrix, toBlocks_fromBlocks₁₂]
  exact ((Matrix.isUnit_iff_isUnit_det B.val).mp B.isUnit).ne_zero

theorem symplectic_fourierCell_parameters (B : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (A C D : Matrix (Fin n) (Fin n) k)
    (hg : Matrix.fromBlocks A B.val C D ∈ Matrix.symplecticGroup (Fin n) k) :
    (D * B⁻¹.val).IsSymm ∧ (B⁻¹.val * A).IsSymm ∧ C = D * B⁻¹.val * A - B⁻¹.val.transpose := by
  have hrot : Matrix.fromBlocks B.val (-A) D (-C) ∈ Matrix.symplecticGroup (Fin n) k := by
    let hp : FunctionsMetaplectic.Construction.Symplectic k n := ⟨Matrix.fromBlocks A B.val C D, hg⟩
    have hm := (hp * (Generators.Construction.weylSymplectic k n)⁻¹).property
    change Matrix.fromBlocks A B.val C D * ((Generators.Construction.weylSymplectic k n)⁻¹).val ∈
      Matrix.symplecticGroup (Fin n) k at hm
    rw [FourierBigCell.Construction.weylSymplectic_inv_matrix] at hm
    simpa [Matrix.fromBlocks_multiply] using hm
  have hs := GenerationSymplectic.Construction.symplectic_bigCell_parameters_symmetric B (-A) D (-C) hrot
  have hQ : (B⁻¹.val * A).IsSymm := by simpa only [Matrix.mul_neg, neg_neg] using hs.2.neg
  have hf := GenerationSymplectic.Construction.symplectic_bigCell_factorization B (-A) D (-C) hrot
  have hh := congrArg (fun g : FunctionsMetaplectic.Construction.Symplectic k n => g.val.toBlocks₂₂) hf
  change -C = ((Generators.Construction.quadraticSymplectic ⟨D * B⁻¹.val, hs.1⟩).val * (Generators.Construction.leviSymplectic B).val *
    (GenerationSymplectic.Construction.upperSymplectic ⟨B⁻¹.val * (-A), hs.2⟩).val).toBlocks₂₂ at hh
  simp only [Generators.Construction.quadraticSymplectic, Generators.Construction.leviSymplectic, GenerationSymplectic.Construction.upperSymplectic, Matrix.fromBlocks_multiply,
    one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, toBlocks_fromBlocks₂₂] at hh
  refine ⟨hs.1, hQ, ?_⟩
  have hneg := congrArg Neg.neg hh
  have hcancel : B.val * (B⁻¹.val * A) = A := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  simpa only [neg_neg, Matrix.mul_neg, neg_add, sub_eq_add_neg, Matrix.mul_assoc, hcancel] using hneg

theorem exists_fourierNormalForm (g : FunctionsMetaplectic.Construction.Symplectic k n) (hg : g ∈ FourierBigCell.Construction.fourierBigCell k n) :
    ∃ (P Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B : FunctionsMetaplectic.Construction.GeneralLinear k n), g = fourierNormalForm P B Q := by
  obtain ⟨B, hB⟩ := (Matrix.isUnit_iff_isUnit_det g.val.toBlocks₁₂).mpr (isUnit_iff_ne_zero.mpr hg)
  have hmatrix : Matrix.fromBlocks g.val.toBlocks₁₁ B.val g.val.toBlocks₂₁ g.val.toBlocks₂₂ = g.val := by
    rw [hB, Matrix.fromBlocks_toBlocks]
  have hs := symplectic_fourierCell_parameters B g.val.toBlocks₁₁ g.val.toBlocks₂₁ g.val.toBlocks₂₂
    (by rw [hmatrix]; exact g.property)
  refine ⟨⟨g.val.toBlocks₂₂ * B⁻¹.val, hs.1⟩, ⟨B⁻¹.val * g.val.toBlocks₁₁, hs.2.1⟩, B, ?_⟩
  apply Subtype.ext
  rw [fourierNormalForm_matrix]
  dsimp only
  have hba : B.val * (B⁻¹.val * g.val.toBlocks₁₁) = g.val.toBlocks₁₁ := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have hdb : (g.val.toBlocks₂₂ * B⁻¹.val) * B.val = g.val.toBlocks₂₂ := by
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  rw [hba, hdb, ← Matrix.mul_assoc g.val.toBlocks₂₂ B⁻¹.val g.val.toBlocks₁₁, ← hs.2.2]
  exact hmatrix.symm

end

/-! Uniqueness of Fourier normal forms and the quadratic form governing their products. -/

open _root_.Matrix

variable {k : Type} [Field k] {n : ℕ}

theorem fourierNormalForm_fourierBlock (P : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) : (fourierNormalForm P B Q).val.toBlocks₁₂ = B.val := by
  rw [fourierNormalForm_matrix, toBlocks_fromBlocks₁₂]

theorem fourierNormalForm_injective
    (P P' Q Q' : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B B' : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (h : fourierNormalForm P B Q = fourierNormalForm P' B' Q') :
    P = P' ∧ B = B' ∧ Q = Q' := by
  have hB : B = B' := by
    apply Units.ext
    simpa only [fourierNormalForm_fourierBlock] using congrArg (fun g : FunctionsMetaplectic.Construction.Symplectic k n => g.val.toBlocks₁₂) h
  subst B'
  have hQ := congrArg (fun g : FunctionsMetaplectic.Construction.Symplectic k n => g.val.toBlocks₁₁) h
  rw [fourierNormalForm_matrix, fourierNormalForm_matrix, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₁] at hQ
  have hP := congrArg (fun g : FunctionsMetaplectic.Construction.Symplectic k n => g.val.toBlocks₂₂) h
  rw [fourierNormalForm_matrix, fourierNormalForm_matrix, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₂₂] at hP
  refine ⟨?_, rfl, ?_⟩
  · apply Subtype.ext
    have hh := congrArg (fun M => M * B⁻¹.val) hP
    simpa only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] using hh
  · apply Subtype.ext
    have hh := congrArg (fun M => B⁻¹.val * M) hQ
    simpa only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] using hh

theorem fourierNormalForm_product_fourierBlock
    (P Q P' Q' : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B B' : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    (fourierNormalForm P B Q * fourierNormalForm P' B' Q').val.toBlocks₁₂ =
      B.val * (Q.val + P'.val) * B'.val := by
  change ((fourierNormalForm P B Q).val * (fourierNormalForm P' B' Q').val).toBlocks₁₂ = _
  rw [fourierNormalForm_matrix, fourierNormalForm_matrix, Matrix.fromBlocks_multiply,
    toBlocks_fromBlocks₁₂]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc B.val P'.val B'.val]

theorem fourierNormalForm_product_middle_nonsingular
    (P Q P' Q' : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B B' : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (h : fourierNormalForm P B Q * fourierNormalForm P' B' Q' ∈ FourierBigCell.Construction.fourierBigCell k n) :
    (Q.val + P'.val).det ≠ 0 := by
  change (fourierNormalForm P B Q * fourierNormalForm P' B' Q').val.toBlocks₁₂.det ≠ 0 at h
  rw [fourierNormalForm_product_fourierBlock, det_mul, det_mul] at h
  intro he
  rw [he, mul_zero, zero_mul] at h
  exact h rfl

end

end OAI.RepresentationTheory.Weil.Local.FourierNormalForm.Construction
