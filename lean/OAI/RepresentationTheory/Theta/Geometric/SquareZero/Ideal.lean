import OAI.RepresentationTheory.Theta.Geometric.SquareZero.Factorization
import OAI.RepresentationTheory.Theta.Geometric.SquareZero.TensorDescent
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Ideal -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.Ideal

noncomputable section

/-! The square-zero factorization and normalized coefficient descent for
an actual ideal in a complex algebra. -/

open scoped TensorProduct

variable {R : Type*} [CommRing R] [Algebra ℂ R]

@[instance_reducible] def idealCoefficientOppositeModule (I : Ideal R) : Module ℂᵐᵒᵖ I :=
  Module.compHom I (RingEquiv.toOpposite ℂ).symm.toRingHom

attribute [local instance] idealCoefficientOppositeModule

local instance idealCoefficientCentralScalar (I : Ideal R) : IsCentralScalar ℂ I where
  op_smul_eq_smul _ _ := rfl

def squareZeroIdealMap (I : Ideal R) (hI : I * I = ⊥) : TrivSqZeroExt ℂ I →ₐ[ℂ] R :=
  Subalgebra.squareZeroSubalgebraMap ((I.restrictScalars ℂ).subtype) (fun x y => by
    apply (Submodule.mem_bot R).mp
    rw [← hI]
    exact Ideal.mul_mem_mul x.property y.property)

theorem squareZeroIdealMap_apply (I : Ideal R) (hI : I * I = ⊥)
    (x : TrivSqZeroExt ℂ I) :
    squareZeroIdealMap I hI x = algebraMap ℂ R x.fst + x.snd.val := rfl

theorem squareZeroIdealMap_injective [Nontrivial R] (I : Ideal R) (hI : I * I = ⊥) :
    Function.Injective (squareZeroIdealMap I hI) :=
  Subalgebra.squareZeroSubalgebraMap_injective _ Subtype.val_injective _

theorem squareZeroIdeal_exact (I : Ideal R) :
    Function.Exact (I.restrictScalars ℂ).subtype (Ideal.Quotient.mkₐ ℂ I).toLinearMap := by
  intro r
  change Ideal.Quotient.mk I r = 0 ↔ ∃ x : I, x.val = r
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun hr => ⟨⟨r, hr⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.property⟩

set_option backward.isDefEq.respectTransparency false in
theorem squareZeroIdeal_exists_factorization [Nontrivial R]
    {A : Type*} [CommRing A] [Algebra ℂ A] (I : Ideal R) (hI : I * I = ⊥)
    (f : A →ₐ[ℂ] R) (e : A →ₐ[ℂ] ℂ)
    (hf : ∀ a, Ideal.Quotient.mkₐ ℂ I (f a) = algebraMap ℂ (R ⧸ I) (e a)) :
    ∃ g : A →ₐ[ℂ] TrivSqZeroExt ℂ I, (squareZeroIdealMap I hI).comp g = f := by
  have hr : ∀ a, f a - algebraMap ℂ R (e a) ∈ LinearMap.range (I.restrictScalars ℂ).subtype := by
    intro a
    apply (squareZeroIdeal_exact I _).mp
    change Ideal.Quotient.mkₐ ℂ I (f a - algebraMap ℂ R (e a)) = 0
    rw [map_sub, hf, (Ideal.Quotient.mkₐ ℂ I).commutes, sub_self]
  exact ⟨Factorization.squareZeroFactorization (M := I) _ Subtype.val_injective _ f e hr,
    Factorization.squareZeroFactorization_comp (M := I) _ Subtype.val_injective _ f e hr⟩

set_option backward.isDefEq.respectTransparency false in
theorem squareZeroIdealTensor_unit_lift [Nontrivial R]
    {B : Type*} [CommRing B] [Algebra ℂ B] (I : Ideal R) (hI : I * I = ⊥)
    (x : (R ⊗[ℂ] B)ˣ)
    (hx : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ ℂ I) (AlgHom.id ℂ B)
      (x : R ⊗[ℂ] B) = 1) :
    ∃! y : (TrivSqZeroExt ℂ I ⊗[ℂ] B)ˣ,
      Algebra.TensorProduct.map (squareZeroIdealMap I hI) (AlgHom.id ℂ B)
        (y : TrivSqZeroExt ℂ I ⊗[ℂ] B) = x :=
  TensorDescent.squareZeroTensor_exists_unit_lift_of_reduction_one (M := I) _ Subtype.val_injective _
    (Ideal.Quotient.mkₐ ℂ I) (squareZeroIdeal_exact I) x hx

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.Ideal
