import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.CokernelLocalization
import Mathlib.Data.Matrix.Block

/-! # Augmented Matrix Cokernels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AugmentedMatrixCokernels

noncomputable section

/-! Adding an identity block preserves the actual cokernel and encodes any requested cokernel rank without subtraction or dimension assumptions. -/

universe u

variable {R : Type u} [CommRing R] {μ ν κ : Type u}
variable [Fintype μ] [Fintype ν] [Fintype κ]
variable [DecidableEq μ] [DecidableEq ν] [DecidableEq κ]
variable (A : Matrix ν μ R)

def identityAugmentedMatrix : Matrix (ν ⊕ κ) (μ ⊕ κ) R :=
  Matrix.fromBlocks A 0 0 1

omit [Fintype ν] [DecidableEq ν] in
theorem identityAugmentedMatrix_apply (x : μ ⊕ κ → R) :
    Matrix.toLin' (identityAugmentedMatrix (κ := κ) A) x =
      Sum.elim (Matrix.toLin' A (x ∘ Sum.inl)) (x ∘ Sum.inr) := by
  simp only [identityAugmentedMatrix, Matrix.toLin'_apply, Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec, Matrix.one_mulVec, add_zero, zero_add]

def identityAugmentedCokernelMap :
    (ν ⊕ κ → R) →ₗ[R] ((ν → R) ⧸ (Matrix.toLin' A).range) :=
  (Matrix.toLin' A).range.mkQ.comp (LinearMap.pi (fun i => LinearMap.proj (Sum.inl i)))

omit [Fintype ν] [Fintype κ] [DecidableEq ν] [DecidableEq κ] in
theorem identityAugmentedCokernelMap_surjective :
    Function.Surjective (identityAugmentedCokernelMap (κ := κ) A) := by
  intro z
  obtain ⟨x, rfl⟩ := (Matrix.toLin' A).range.mkQ_surjective z
  exact ⟨Sum.elim x 0, rfl⟩

omit [Fintype ν] [DecidableEq ν] in
theorem identityAugmentedCokernelMap_kernel :
    (identityAugmentedCokernelMap (κ := κ) A).ker =
      (Matrix.toLin' (identityAugmentedMatrix (κ := κ) A)).range := by
  ext x
  change (Matrix.toLin' A).range.mkQ (x ∘ Sum.inl) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Sum.elim y (x ∘ Sum.inr), ?_⟩
    rw [identityAugmentedMatrix_apply]
    funext i
    cases i with
    | inl i => exact congrFun hy i
    | inr i => rfl
  · rintro ⟨y, hy⟩
    refine ⟨y ∘ Sum.inl, ?_⟩
    rw [identityAugmentedMatrix_apply] at hy
    funext i
    exact congrFun hy (Sum.inl i)

def identityAugmentedCokernelEquiv :
    ((ν ⊕ κ → R) ⧸ (Matrix.toLin' (identityAugmentedMatrix (κ := κ) A)).range) ≃ₗ[R]
      ((ν → R) ⧸ (Matrix.toLin' A).range) :=
  (Submodule.quotEquivOfEq _ _ (identityAugmentedCokernelMap_kernel A).symm).trans
    ((identityAugmentedCokernelMap A).quotKerEquivOfSurjective
      (identityAugmentedCokernelMap_surjective A))

omit [DecidableEq ν] in
theorem identityAugmentedMatrix_flatRank_iff :
    (Module.Flat R ((ν ⊕ κ → R) ⧸ (Matrix.toLin' (identityAugmentedMatrix (κ := κ) A)).range) ∧
      ∀ p, Module.rankAtStalk (R := R)
        ((ν ⊕ κ → R) ⧸ (Matrix.toLin' (identityAugmentedMatrix (κ := κ) A)).range) p +
          Fintype.card ν = Fintype.card (ν ⊕ κ)) ↔
    (Module.Flat R ((ν → R) ⧸ (Matrix.toLin' A).range) ∧
      ∀ p, Module.rankAtStalk (R := R) ((ν → R) ⧸ (Matrix.toLin' A).range) p = Fintype.card κ) := by
  rw [Module.Flat.equiv_iff (identityAugmentedCokernelEquiv (κ := κ) A),
    Module.rankAtStalk_eq_of_equiv (identityAugmentedCokernelEquiv (κ := κ) A)]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro p
  rw [Fintype.card_sum]
  omega

omit [Fintype μ] [Fintype ν] [Fintype κ] [DecidableEq μ] [DecidableEq ν] in
theorem identityAugmentedMatrix_map {S : Type u} [CommRing S] (φ : R →+* S) :
    (identityAugmentedMatrix (κ := κ) A).map φ = identityAugmentedMatrix (κ := κ) (A.map φ) := by
  ext i j
  cases i <;> cases j <;> simp [identityAugmentedMatrix, Matrix.map_apply, Matrix.one_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AugmentedMatrixCokernels
