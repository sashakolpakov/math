import OAI.LinearAlgebra.Symplectic.BigCell
import OAI.RepresentationTheory.Weil.Local.Generators

/-! # Generation Symplectic -/

namespace OAI.RepresentationTheory.Weil.Local.GenerationSymplectic.Construction

noncomputable section

section

/-! Symplectic generator reduction over a field. The big-cell argument follows
the same matrix calculation as PoissonAutomorphy, with the field parameter left general. -/

open _root_.Matrix

variable {k : Type} [Field k] {n : ℕ}

def upperSymplectic (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) : FunctionsMetaplectic.Construction.Symplectic k n := by
  refine ⟨Matrix.fromBlocks 1 B.val 0 1, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [B.property.eq]

theorem quadratic_upper_conjugation (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    Generators.Construction.quadraticSymplectic B = Generators.Construction.weylSymplectic k n *
      upperSymplectic ⟨-B.val, B.property.neg⟩ * (Generators.Construction.weylSymplectic k n)⁻¹ := by
  apply Subtype.ext
  change Matrix.fromBlocks 1 0 B.val 1 =
    (Generators.Construction.weylSymplectic k n).val * (upperSymplectic ⟨-B.val, B.property.neg⟩).val *
      ((Generators.Construction.weylSymplectic k n)⁻¹).val
  rw [SymplecticGroup.coe_inv]
  simp [Generators.Construction.weylSymplectic, upperSymplectic, Matrix.J, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

/-- Uses the kernel-checked big-cell lemma in the Mathlib.
Its private visibility does not change its proof or axiom dependencies. -/
theorem symplectic_exists_upper_bigCell (g : FunctionsMetaplectic.Construction.Symplectic k n) :
    ∃ B : FunctionsMetaplectic.Construction.SymmetricMatrix k n,
      IsUnit ((upperSymplectic B * g).val.toBlocks₁₁).det := by
  have hex : ∃ B : Matrix (Fin n) (Fin n) k, B.IsSymm ∧
      IsUnit (g.val.toBlocks₁₁ + B * g.val.toBlocks₂₁).det := by
    apply LinearAlgebra.Symplectic.BigCell.SymplecticBigCell.exists_symmetric_X_isUnit_det_add_mul_of_symplectic
    exact (show Matrix.fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂
      g.val.toBlocks₂₁ g.val.toBlocks₂₂ ∈ Matrix.symplecticGroup (Fin n) k from by
        simpa only [Matrix.fromBlocks_toBlocks] using g.property)
  obtain ⟨B, hB, hdet⟩ := hex
  refine ⟨⟨B, hB⟩, ?_⟩
  change IsUnit (((upperSymplectic ⟨B, hB⟩).val * g.val).toBlocks₁₁).det
  rw [← Matrix.fromBlocks_toBlocks g.val]
  simpa [upperSymplectic, Matrix.fromBlocks_multiply] using hdet

theorem symplectic_bigCell_parameters_symmetric (A : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (B C D : Matrix (Fin n) (Fin n) k)
    (hg : Matrix.fromBlocks A.val B C D ∈ Matrix.symplecticGroup (Fin n) k) :
    (C * (A⁻¹).val).IsSymm ∧ ((A⁻¹).val * B).IsSymm := by
  have hac := (SymplecticGroup.fromBlocks_mem_iff.mp hg).1
  have hab := (SymplecticGroup.fromBlocks_mem_iff.mp
    (show Matrix.fromBlocks A.val.transpose C.transpose B.transpose D.transpose ∈
      Matrix.symplecticGroup (Fin n) k from by
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

theorem symplectic_bigCell_factorization (A : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (B C D : Matrix (Fin n) (Fin n) k)
    (hg : Matrix.fromBlocks A.val B C D ∈ Matrix.symplecticGroup (Fin n) k) :
    (⟨Matrix.fromBlocks A.val B C D, hg⟩ : FunctionsMetaplectic.Construction.Symplectic k n) =
      Generators.Construction.quadraticSymplectic ⟨C * (A⁻¹).val, (symplectic_bigCell_parameters_symmetric A B C D hg).1⟩ *
        Generators.Construction.leviSymplectic A *
        upperSymplectic ⟨(A⁻¹).val * B, (symplectic_bigCell_parameters_symmetric A B C D hg).2⟩ := by
  have hL := (symplectic_bigCell_parameters_symmetric A B C D hg).1
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

theorem subgroup_eq_top_of_symplectic_generators (H : Subgroup (FunctionsMetaplectic.Construction.Symplectic k n))
    (hU : ∀ B : FunctionsMetaplectic.Construction.SymmetricMatrix k n, upperSymplectic B ∈ H)
    (hM : ∀ A : FunctionsMetaplectic.Construction.GeneralLinear k n, Generators.Construction.leviSymplectic A ∈ H)
    (hW : Generators.Construction.weylSymplectic k n ∈ H) : H = ⊤ := by
  apply top_unique
  intro g _
  have hL : ∀ B : FunctionsMetaplectic.Construction.SymmetricMatrix k n, Generators.Construction.quadraticSymplectic B ∈ H := by
    intro B
    rw [quadratic_upper_conjugation]
    exact H.mul_mem (H.mul_mem hW (hU ⟨-B.val, B.property.neg⟩)) (H.inv_mem hW)
  obtain ⟨X, hdet⟩ := symplectic_exists_upper_bigCell g
  let f := upperSymplectic X * g
  obtain ⟨A, hA⟩ := (Matrix.isUnit_iff_isUnit_det f.val.toBlocks₁₁).mpr hdet
  have hmatrix : Matrix.fromBlocks A.val f.val.toBlocks₁₂
      f.val.toBlocks₂₁ f.val.toBlocks₂₂ = f.val := by
    rw [hA, Matrix.fromBlocks_toBlocks]
  have hs : Matrix.fromBlocks A.val f.val.toBlocks₁₂ f.val.toBlocks₂₁
      f.val.toBlocks₂₂ ∈ Matrix.symplecticGroup (Fin n) k := by
    rw [hmatrix]
    exact f.property
  have hfactor := symplectic_bigCell_factorization A f.val.toBlocks₁₂
    f.val.toBlocks₂₁ f.val.toBlocks₂₂ hs
  have hf : f ∈ H := by
    have heq : f = ⟨Matrix.fromBlocks A.val f.val.toBlocks₁₂
        f.val.toBlocks₂₁ f.val.toBlocks₂₂, hs⟩ := Subtype.ext hmatrix.symm
    rw [heq, hfactor]
    exact H.mul_mem (H.mul_mem (hL _) (hM A)) (hU _)
  have h := H.mul_mem (H.inv_mem (hU X)) hf
  simpa only [f, inv_mul_cancel_left] using h

end

section

/-! Invertible matrices are generated by invertible symmetric matrices. -/

open _root_.Matrix

variable {k : Type} [Field k] {n : ℕ}

def swapGeneralLinear (i j : Fin n) : FunctionsMetaplectic.Construction.GeneralLinear k n where
  val := (Equiv.swap i j).permMatrix k
  inv := (Equiv.swap i j).permMatrix k
  val_inv := by rw [← Matrix.permMatrix_mul]; simp
  inv_val := by rw [← Matrix.permMatrix_mul]; simp

theorem swapGeneralLinear_symmetric (i j : Fin n) :
    ((swapGeneralLinear (k := k) i j).val).IsSymm := by
  change ((Equiv.swap i j).permMatrix k).transpose = (Equiv.swap i j).permMatrix k
  rw [Matrix.transpose_permMatrix]
  simp

theorem swapGeneralLinear_square (i j : Fin n) :
    swapGeneralLinear (k := k) i j * swapGeneralLinear i j = 1 := by
  apply Units.ext
  change (Equiv.swap i j).permMatrix k * (Equiv.swap i j).permMatrix k = 1
  rw [← Matrix.permMatrix_mul]
  simp

theorem transvection_mul_swap (t : Matrix.TransvectionStruct (Fin n) k) :
    t.toMatrix * (swapGeneralLinear t.i t.j).val =
      (swapGeneralLinear t.i t.j).val + Matrix.single t.i t.i t.c := by
  rw [TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mul, Matrix.one_mul]
  congr 1
  ext a b
  by_cases ha : a = t.i
  · subst a
    rw [Matrix.single_mul_apply_same]
    simp [swapGeneralLinear, PEquiv.toMatrix, Equiv.toPEquiv_apply, Matrix.single]
  · rw [Matrix.single_mul_apply_of_ne t.c t.i t.j a b ha]
    simp [Matrix.single, Ne.symm ha]

theorem transvection_mul_swap_symmetric (t : Matrix.TransvectionStruct (Fin n) k) :
    (t.toMatrix * (swapGeneralLinear t.i t.j).val).IsSymm := by
  rw [transvection_mul_swap]
  apply (swapGeneralLinear_symmetric t.i t.j).add
  change (Matrix.single t.i t.i t.c).transpose = Matrix.single t.i t.i t.c
  simp

theorem subgroup_eq_top_of_symmetric_generalLinear (H : Subgroup (FunctionsMetaplectic.Construction.GeneralLinear k n))
    (hSym : ∀ A : FunctionsMetaplectic.Construction.GeneralLinear k n, A.val.IsSymm → A ∈ H) : H = ⊤ := by
  apply top_unique
  intro U _
  have hp : ∀ M : Matrix (Fin n) (Fin n) k, M.det ≠ 0 →
      ∀ A : FunctionsMetaplectic.Construction.GeneralLinear k n, A.val = M → A ∈ H := by
    intro M hM
    apply Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun M => ∀ A : FunctionsMetaplectic.Construction.GeneralLinear k n, A.val = M → A ∈ H) M hM
    · intro D _ A hA
      apply hSym A
      rw [hA]
      exact Matrix.isSymm_diagonal D
    · intro t A hA
      have hAP : A * swapGeneralLinear t.i t.j ∈ H := by
        apply hSym
        change (A.val * (swapGeneralLinear t.i t.j).val).IsSymm
        rw [hA]
        exact transvection_mul_swap_symmetric t
      have hP : swapGeneralLinear (k := k) t.i t.j ∈ H :=
        hSym _ (swapGeneralLinear_symmetric t.i t.j)
      have h := H.mul_mem hAP hP
      rwa [mul_assoc, swapGeneralLinear_square, mul_one] at h
    · intro M N hM hN ihM ihN A hA
      obtain ⟨B, hB⟩ := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hM)
      obtain ⟨C, hC⟩ := (Matrix.isUnit_iff_isUnit_det N).mpr (isUnit_iff_ne_zero.mpr hN)
      have heq : A = B * C := by
        apply Units.ext
        rw [hA, Units.val_mul, hB, hC]
      rw [heq]
      exact H.mul_mem (ihM B hB) (ihN C hC)
  exact hp U.val ((Matrix.isUnit_iff_isUnit_det U.val).mp U.isUnit).ne_zero U rfl

end

/-! Upper and lower symmetric unipotents generate the symplectic group. -/

open _root_.Matrix

variable {k : Type} [Field k] {n : ℕ}

def leviHom : FunctionsMetaplectic.Construction.GeneralLinear k n →* FunctionsMetaplectic.Construction.Symplectic k n where
  toFun := Generators.Construction.leviSymplectic
  map_one' := by
    apply Subtype.ext
    simp [Generators.Construction.leviSymplectic]
  map_mul' A B := by
    apply Subtype.ext
    change (Generators.Construction.leviSymplectic (A * B)).val = (Generators.Construction.leviSymplectic A).val * (Generators.Construction.leviSymplectic B).val
    simp [Generators.Construction.leviSymplectic, _root_.mul_inv_rev, Matrix.transpose_mul, Matrix.fromBlocks_multiply]

theorem weyl_unipotent_factorization :
    Generators.Construction.weylSymplectic k n = upperSymplectic ⟨1, Matrix.isSymm_one⟩ *
      Generators.Construction.quadraticSymplectic ⟨-1, Matrix.isSymm_one.neg⟩ * upperSymplectic ⟨1, Matrix.isSymm_one⟩ := by
  apply Subtype.ext
  change (Generators.Construction.weylSymplectic k n).val =
    (upperSymplectic ⟨1, Matrix.isSymm_one⟩).val *
      (Generators.Construction.quadraticSymplectic ⟨-1, Matrix.isSymm_one.neg⟩).val *
      (upperSymplectic ⟨1, Matrix.isSymm_one⟩).val
  simp [Generators.Construction.weylSymplectic, upperSymplectic, Generators.Construction.quadraticSymplectic, Matrix.fromBlocks_multiply]

theorem symmetric_levi_unipotent_factorization (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (hA : A.val.IsSymm) :
    Generators.Construction.leviSymplectic A * Generators.Construction.weylSymplectic k n =
      upperSymplectic ⟨A.val, hA⟩ *
        Generators.Construction.quadraticSymplectic ⟨-(A⁻¹).val, (by
          have h : ((A⁻¹).val).IsSymm := by simpa only [Matrix.coe_units_inv] using hA.inv
          exact h.neg)⟩ * upperSymplectic ⟨A.val, hA⟩ := by
  have hinv : ((A⁻¹).val).IsSymm := by simpa only [Matrix.coe_units_inv] using hA.inv
  apply Subtype.ext
  change (Generators.Construction.leviSymplectic A).val * (Generators.Construction.weylSymplectic k n).val =
    (upperSymplectic ⟨A.val, hA⟩).val *
      (Generators.Construction.quadraticSymplectic ⟨-(A⁻¹).val, hinv.neg⟩).val * (upperSymplectic ⟨A.val, hA⟩).val
  simp [Generators.Construction.leviSymplectic, Generators.Construction.weylSymplectic, upperSymplectic, Generators.Construction.quadraticSymplectic,
    Matrix.fromBlocks_multiply, hA.inv.eq]

theorem subgroup_eq_top_of_symplectic_unipotents (H : Subgroup (FunctionsMetaplectic.Construction.Symplectic k n))
    (hU : ∀ B : FunctionsMetaplectic.Construction.SymmetricMatrix k n, upperSymplectic B ∈ H)
    (hL : ∀ B : FunctionsMetaplectic.Construction.SymmetricMatrix k n, Generators.Construction.quadraticSymplectic B ∈ H) : H = ⊤ := by
  have hW : Generators.Construction.weylSymplectic k n ∈ H := by
    rw [weyl_unipotent_factorization]
    exact H.mul_mem (H.mul_mem (hU _) (hL _)) (hU _)
  have hSym (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (hA : A.val.IsSymm) : Generators.Construction.leviSymplectic A ∈ H := by
    have h : Generators.Construction.leviSymplectic A * Generators.Construction.weylSymplectic k n ∈ H := by
      rw [symmetric_levi_unipotent_factorization A hA]
      exact H.mul_mem (H.mul_mem (hU _) (hL _)) (hU _)
    have hh := H.mul_mem h (H.inv_mem hW)
    simpa only [mul_inv_cancel_right] using hh
  have htop : H.comap (leviHom (k := k) (n := n)) = ⊤ :=
    subgroup_eq_top_of_symmetric_generalLinear _ hSym
  apply subgroup_eq_top_of_symplectic_generators H hU _ hW
  intro A
  have h : A ∈ H.comap (leviHom (k := k) (n := n)) := by rw [htop]; trivial
  exact h

end

end OAI.RepresentationTheory.Weil.Local.GenerationSymplectic.Construction
