import OAI.LinearAlgebra.Symplectic.BigCell
import OAI.RepresentationTheory.Weil.Local.Generators

/-! # Symplectic Generation -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.SymplecticGeneration

noncomputable section

/-! Generation of the full symplectic group over any field by the actual
Schrödinger matrix generators. The block elimination argument follows the
checked PoissonAutomorphy generator calculation and the Mathlib big-cell lemma.
No PoissonAutomorphy theorem or representation data is imported. -/

open scoped _root_.Matrix
open _root_.Matrix

variable {k : Type} [Field k] {N : ℕ}

def upper (B : Matrix (Fin N) (Fin N) k) (hB : B.IsSymm) : Matrix.symplecticGroup (Fin N) k := by
  refine ⟨Matrix.fromBlocks 1 B 0 1, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [hB.eq]

def levi (A : (Matrix (Fin N) (Fin N) k)ˣ) : Matrix.symplecticGroup (Fin N) k := by
  refine ⟨Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [← Matrix.transpose_mul]

def weyl : Matrix.symplecticGroup (Fin N) k := by
  refine ⟨Matrix.fromBlocks 0 1 (-1) 0, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp

def lower (B : Matrix (Fin N) (Fin N) k) (hB : B.IsSymm) : Matrix.symplecticGroup (Fin N) k := by
  refine ⟨Matrix.fromBlocks 1 0 B 1, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [hB.eq]

theorem lower_conjugation (B : Matrix (Fin N) (Fin N) k) (hB : B.IsSymm) :
    lower B hB = weyl (k := k) (N := N) * upper (-B) hB.neg * (weyl (k := k) (N := N))⁻¹ := by
  apply Subtype.ext
  change Matrix.fromBlocks 1 0 B 1 =
    (weyl (k := k) (N := N)).val * (upper (-B) hB.neg).val * ((weyl (k := k) (N := N))⁻¹).val
  rw [SymplecticGroup.coe_inv]
  simp [weyl, upper, Matrix.J, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

/-- Reuses mathlib's proved big-cell lemma, which is private in the pinned
mathlib version. This name refers to its kernel-checked proof, not an axiom. -/
theorem exists_upper_bigCell (g : Matrix.symplecticGroup (Fin N) k) :
    ∃ (B : Matrix (Fin N) (Fin N) k) (hB : B.IsSymm),
      IsUnit ((upper B hB * g).val.toBlocks₁₁).det := by
  have hex : ∃ B : Matrix (Fin N) (Fin N) k, B.IsSymm ∧
      IsUnit (g.val.toBlocks₁₁ + B * g.val.toBlocks₂₁).det := by
    apply LinearAlgebra.Symplectic.BigCell.SymplecticBigCell.exists_symmetric_X_isUnit_det_add_mul_of_symplectic
    exact (show Matrix.fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂
      g.val.toBlocks₂₁ g.val.toBlocks₂₂ ∈ Matrix.symplecticGroup (Fin N) k from by
        simpa only [Matrix.fromBlocks_toBlocks] using g.property)
  obtain ⟨B, hB, hdet⟩ := hex
  refine ⟨B, hB, ?_⟩
  change IsUnit (((upper B hB).val * g.val).toBlocks₁₁).det
  rw [← Matrix.fromBlocks_toBlocks g.val]
  simpa [upper, Matrix.fromBlocks_multiply] using hdet

theorem bigCell_parameters_symmetric (A : (Matrix (Fin N) (Fin N) k)ˣ)
    (B C D : Matrix (Fin N) (Fin N) k)
    (hg : Matrix.fromBlocks A.val B C D ∈ Matrix.symplecticGroup (Fin N) k) :
    (C * (A⁻¹).val).IsSymm ∧ ((A⁻¹).val * B).IsSymm := by
  have hac := (SymplecticGroup.fromBlocks_mem_iff.mp hg).1
  have hab := (SymplecticGroup.fromBlocks_mem_iff.mp
    (show Matrix.fromBlocks A.val.transpose C.transpose B.transpose D.transpose ∈
      Matrix.symplecticGroup (Fin N) k from by
        simpa only [Matrix.fromBlocks_transpose] using SymplecticGroup.transpose_mem hg)).1
  simp only [Matrix.transpose_transpose] at hab
  constructor
  · change (C * (A⁻¹).val).transpose = C * (A⁻¹).val
    have h := congrArg (fun M => (A⁻¹).val.transpose * M * (A⁻¹).val) hac
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.transpose_one, one_mul] at h
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, mul_one] using h.symm
  · change ((A⁻¹).val * B).transpose = (A⁻¹).val * B
    have h := congrArg (fun M => (A⁻¹).val * M * (A⁻¹).val.transpose) hab
    simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mul] at h
    simpa only [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.transpose_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
      mul_one] using h

theorem bigCell_factorization (A : (Matrix (Fin N) (Fin N) k)ˣ)
    (B C D : Matrix (Fin N) (Fin N) k)
    (hg : Matrix.fromBlocks A.val B C D ∈ Matrix.symplecticGroup (Fin N) k) :
    (⟨Matrix.fromBlocks A.val B C D, hg⟩ : Matrix.symplecticGroup (Fin N) k) =
      lower (C * (A⁻¹).val) (bigCell_parameters_symmetric A B C D hg).1 *
        levi A * upper ((A⁻¹).val * B) (bigCell_parameters_symmetric A B C D hg).2 := by
  have hL := (bigCell_parameters_symmetric A B C D hg).1
  have had := (SymplecticGroup.fromBlocks_mem_iff.mp hg).2.2
  have hD : D = C * (A⁻¹).val * B + (A⁻¹).val.transpose := by
    have h := congrArg (fun M => (A⁻¹).val.transpose * M) had
    simp only [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
      one_mul, mul_one] at h
    rw [hL.eq] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  apply Subtype.ext
  change Matrix.fromBlocks A.val B C D =
    Matrix.fromBlocks 1 0 (C * (A⁻¹).val) 1 *
      Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose *
        Matrix.fromBlocks 1 ((A⁻¹).val * B) 0 1
  simp only [Matrix.fromBlocks_multiply, one_mul, mul_one, zero_mul, mul_zero,
    zero_add, add_zero]
  have hC : C * (A⁻¹).val * A.val = C := by
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hB : A.val * ((A⁻¹).val * B) = B := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  rw [hC, hB, hD, Matrix.mul_assoc C (A⁻¹).val B]

theorem subgroup_eq_top_of_generators (H : Subgroup (Matrix.symplecticGroup (Fin N) k))
    (hU : ∀ (B : Matrix (Fin N) (Fin N) k) (hB : B.IsSymm), upper B hB ∈ H)
    (hM : ∀ A : (Matrix (Fin N) (Fin N) k)ˣ, levi A ∈ H)
    (hW : weyl (k := k) (N := N) ∈ H) : H = ⊤ := by
  apply top_unique
  intro g _
  have hL : ∀ (B : Matrix (Fin N) (Fin N) k) (hB : B.IsSymm), lower B hB ∈ H := by
    intro B hB
    rw [lower_conjugation]
    exact H.mul_mem (H.mul_mem hW (hU (-B) hB.neg)) (H.inv_mem hW)
  obtain ⟨X, hX, hdet⟩ := exists_upper_bigCell g
  let f := upper X hX * g
  obtain ⟨A, hA⟩ := (Matrix.isUnit_iff_isUnit_det f.val.toBlocks₁₁).mpr hdet
  have hmatrix : Matrix.fromBlocks A.val f.val.toBlocks₁₂
      f.val.toBlocks₂₁ f.val.toBlocks₂₂ = f.val := by
    rw [hA, Matrix.fromBlocks_toBlocks]
  have hs : Matrix.fromBlocks A.val f.val.toBlocks₁₂ f.val.toBlocks₂₁
      f.val.toBlocks₂₂ ∈ Matrix.symplecticGroup (Fin N) k := by
    rw [hmatrix]
    exact f.property
  have hfactor := bigCell_factorization A f.val.toBlocks₁₂
    f.val.toBlocks₂₁ f.val.toBlocks₂₂ hs
  have hf : f ∈ H := by
    have heq : f = ⟨Matrix.fromBlocks A.val f.val.toBlocks₁₂
        f.val.toBlocks₂₁ f.val.toBlocks₂₂, hs⟩ :=
      Subtype.ext hmatrix.symm
    rw [heq, hfactor]
    exact H.mul_mem (H.mul_mem (hL _ _) (hM A)) (hU _ _)
  have h := H.mul_mem (H.inv_mem (hU X hX)) hf
  simpa only [f, inv_mul_cancel_left] using h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.SymplecticGeneration
