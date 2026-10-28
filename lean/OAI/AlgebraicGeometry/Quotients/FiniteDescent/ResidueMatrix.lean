import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ResidueEquivalenceLift

/-! # Residue Matrix -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ResidueMatrix.Construction.LocalSectionLifting

noncomputable section

/-! Detecting a cancellable matrix entry in a nonzero residue-field differential. -/

open scoped TensorProduct

variable {R : Type*} [CommRing R] [IsLocalRing R]
    {M N ι κ : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (bM : Module.Basis ι R M) (bN : Module.Basis κ R N) (f : M →ₗ[R] N)

theorem residue_matrix_coefficient (i : ι) (j : κ) :
    (bN.baseChange (IsLocalRing.ResidueField R)).repr
      (f.baseChange (IsLocalRing.ResidueField R)
        (bM.baseChange (IsLocalRing.ResidueField R) i)) j =
      IsLocalRing.residue R (bN.repr (f (bM i)) j) := by
  simp only [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one,
    IsLocalRing.ResidueField.algebraMap_eq]

theorem residue_map_eq_zero_iff_matrix :
    f.baseChange (IsLocalRing.ResidueField R) = 0 ↔
      ∀ i j, bN.repr (f (bM i)) j ∈ IsLocalRing.maximalIdeal R := by
  constructor
  · intro hf i j
    rw [← IsLocalRing.residue_eq_zero_iff,
      ← residue_matrix_coefficient bM bN f i j, hf]
    simp
  · intro hf
    apply (bM.baseChange (IsLocalRing.ResidueField R)).ext
    intro i
    apply (bN.baseChange (IsLocalRing.ResidueField R)).ext_elem
    intro j
    rw [residue_matrix_coefficient bM bN f i j]
    simpa using (IsLocalRing.residue_eq_zero_iff _).mpr (hf i j)

theorem exists_unit_matrix_coefficient_of_residue_ne_zero
    (hf : f.baseChange (IsLocalRing.ResidueField R) ≠ 0) :
    ∃ i j, IsUnit (bN.repr (f (bM i)) j) := by
  classical
  have h := (residue_map_eq_zero_iff_matrix bM bN f).not.mp hf
  push Not at h
  obtain ⟨i, j, hij⟩ := h
  exact ⟨i, j, (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    ((IsLocalRing.residue_eq_zero_iff _).not.mpr hij)⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ResidueMatrix.Construction.LocalSectionLifting
