import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NilpotentLinearMapLifting
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Nilpotent Free Lifting -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NilpotentFreeLifting

noncomputable section

/-! Freeness of a flat module lifts across a nilpotent ideal, with no
finiteness requirement on the rank. -/

open TensorProduct

universe u v
variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M]

theorem nilpotent_free_lifting (I : Ideal R) (hI : IsNilpotent I)
    [Module.Free (R ⧸ I) ((R ⧸ I) ⊗[R] M)] : Module.Free R M := by
  let b := Module.Free.chooseBasis (R ⧸ I) ((R ⧸ I) ⊗[R] M)
  let ι := Module.Free.ChooseBasisIndex (R ⧸ I) ((R ⧸ I) ⊗[R] M)
  have hx : ∀ i : ι, ∃ m : M, (1 : R ⧸ I) ⊗ₜ[R] m = b i :=
    fun i => Quotient.TensorRelations.quotientTensor_exists_one_tmul M I (b i)
  let x : ι → M := fun i => (hx i).choose
  let f : (ι →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
  let c : Module.Basis ι (R ⧸ I) ((R ⧸ I) ⊗[R] (ι →₀ R)) :=
    (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R)).baseChange (R ⧸ I)
  let e := c.equiv b (Equiv.refl ι)
  have he : AlgebraTensorModule.lTensor (R ⧸ I) (R ⧸ I) f = e.toLinearMap := by
    apply c.ext
    intro i
    change (AlgebraTensorModule.lTensor (R ⧸ I) (R ⧸ I) f) (c i) = e (c i)
    rw [Module.Basis.equiv_apply]
    simp only [c, Module.Basis.baseChange_apply]
    change (1 : R ⧸ I) ⊗ₜ[R] f (Finsupp.single i 1) = b i
    rw [Finsupp.linearCombination_single, one_smul]
    exact (hx i).choose_spec
  have hf : Function.Bijective (f.lTensor (R ⧸ I)) := by
    change Function.Bijective (AlgebraTensorModule.lTensor (R ⧸ I) (R ⧸ I) f)
    rw [he]
    exact e.bijective
  let e' := LinearEquiv.ofBijective f (NilpotentLinearMapLifting.nilpotent_bijective_of_reduction I hI f hf)
  exact Module.Free.of_equiv e'

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NilpotentFreeLifting
