import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.BasisLift
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Equivalence Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.EquivalenceLift.LocalSectionLifting

noncomputable section

/-! Lifting an arbitrary residue-field change of coordinates over a local ring. -/

open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R N] [Module.Flat R N]

theorem exists_linearEquiv_lifting_residue
    (e : (IsLocalRing.ResidueField R ⊗[R] M) ≃ₗ[IsLocalRing.ResidueField R]
      (IsLocalRing.ResidueField R ⊗[R] N)) :
    ∃ E : M ≃ₗ[R] N, E.baseChange R (IsLocalRing.ResidueField R) M N = e := by
  let b := Module.Free.chooseBasis R M
  obtain ⟨B, hB⟩ := BasisLift.LocalSectionLifting.exists_basis_lifting_residue ((b.baseChange (IsLocalRing.ResidueField R)).map e)
  let E : M ≃ₗ[R] N := b.equiv B (Equiv.refl _)
  refine ⟨E, ?_⟩
  apply (b.baseChange (IsLocalRing.ResidueField R)).ext'
  intro i
  simp only [Module.Basis.baseChange_apply, LinearEquiv.baseChange_tmul]
  change (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] (b.equiv B (Equiv.refl _) (b i)) =
    e ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] b i)
  rw [Module.Basis.equiv_apply]
  simpa only [Equiv.refl_apply, Module.Basis.map_apply, Module.Basis.baseChange_apply] using hB i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.EquivalenceLift.LocalSectionLifting
