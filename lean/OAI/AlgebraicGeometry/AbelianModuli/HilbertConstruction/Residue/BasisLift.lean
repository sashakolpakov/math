import Mathlib.RingTheory.LocalRing.Module

/-! # Basis Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.BasisLift.LocalSectionLifting

noncomputable section

/-! Lifting a chosen residue-field basis to a finite free local module. -/

open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M]

omit [Module.FinitePresentation R M] [Module.Flat R M] in
theorem exists_residueBasis_lifts {ι : Type w}
    (b : Module.Basis ι (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M)) :
    ∃ v : ι → M, ∀ i, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] v i = b i := by
  have hsurj : Function.Surjective (TensorProduct.mk R (IsLocalRing.ResidueField R) M 1) :=
    TensorProduct.mk_surjective R M (IsLocalRing.ResidueField R)
    Ideal.Quotient.mk_surjective
  choose v hv using fun i ↦ hsurj (b i)
  exact ⟨v, hv⟩

theorem exists_basis_of_residueBasis_lifts {ι : Type w} (v : ι → M)
    (b : Module.Basis ι (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M))
    (hv : ∀ i, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] v i = b i) :
    ∃ B : Module.Basis ι R M, ∀ i, B i = v i := by
  have hvec : TensorProduct.mk R (IsLocalRing.ResidueField R) M 1 ∘ v = b := funext hv
  apply Module.exists_basis_of_basis_baseChange v
  · rw [hvec]
    exact b.linearIndependent
  · rw [hvec]
    exact b.span_eq
  · exact Module.Flat.rTensor_preserves_injective_linearMap
      (M := M) (IsLocalRing.maximalIdeal R).subtype Subtype.val_injective

theorem exists_basis_lifting_residue {ι : Type w}
    (b : Module.Basis ι (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M)) :
    ∃ B : Module.Basis ι R M, ∀ i, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] B i = b i := by
  obtain ⟨v, hv⟩ := exists_residueBasis_lifts b
  obtain ⟨B, hB⟩ := exists_basis_of_residueBasis_lifts v b hv
  exact ⟨B, fun i ↦ (congrArg (TensorProduct.mk R (IsLocalRing.ResidueField R) M 1) (hB i)).trans (hv i)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.BasisLift.LocalSectionLifting
