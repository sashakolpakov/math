import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.TypeCharacters
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Product Domain -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Tensor.ProductDomain.Constructions

/-! A tensor product over an algebraically closed field is an integral
domain when the left factor is a finite-type integral algebra and the
right factor is integral. The proof uses actual character specialization. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.TypeCharacters.Constructions

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

def specializeLeft (χ : A →ₐ[k] k) : A ⊗[k] B →ₐ[k] B :=
  Algebra.TensorProduct.lift ((Algebra.ofId k B).comp χ) (AlgHom.id k B)
    (fun _ _ => Commute.all _ _)

theorem specializeLeft_tmul (χ : A →ₐ[k] k) (a : A) (b : B) :
    specializeLeft (B := B) χ (a ⊗ₜ[k] b) = χ a • b := by
  simp [specializeLeft, Algebra.smul_def]

theorem specializeLeft_coefficient {ι : Type*} [DecidableEq ι]
    (b : Module.Basis ι k B) (χ : A →ₐ[k] k) (x : A ⊗[k] B) (i : ι) :
    b.repr (specializeLeft χ x) i = χ (TensorProduct.equivFinsuppOfBasisRight b x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a c =>
      simp only [specializeLeft_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem exists_tensor_coefficient_ne_zero {ι : Type*} [DecidableEq ι]
    (b : Module.Basis ι k B) (x : A ⊗[k] B) (hx : x ≠ 0) :
    ∃ i, TensorProduct.equivFinsuppOfBasisRight b x i ≠ 0 := by
  classical
  by_contra! h
  apply hx
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  exact h i

variable [IsAlgClosed k] [Algebra.FiniteType k A] [IsDomain A]

theorem exists_specialization_two_ne_zero (x y : A ⊗[k] B) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ χ : A →ₐ[k] k, specializeLeft χ x ≠ 0 ∧ specializeLeft χ y ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis k B
  obtain ⟨i, hi⟩ := exists_tensor_coefficient_ne_zero b x hx
  obtain ⟨j, hj⟩ := exists_tensor_coefficient_ne_zero b y hy
  obtain ⟨χ, hχx, hχy⟩ := Finite.TypeCharacters.Constructions.exists_character_two_ne_zero k A
    (TensorProduct.equivFinsuppOfBasisRight b x i) (TensorProduct.equivFinsuppOfBasisRight b y j) hi hj
  refine ⟨χ, ?_, ?_⟩
  · intro h
    apply hχx
    rw [← specializeLeft_coefficient b χ x i, h, map_zero, Finsupp.zero_apply]
  · intro h
    apply hχy
    rw [← specializeLeft_coefficient b χ y j, h, map_zero, Finsupp.zero_apply]

variable [IsDomain B]

theorem tensorProduct_isDomain : IsDomain (A ⊗[k] B) := by
  classical
  obtain ⟨χ, _⟩ := Finite.TypeCharacters.Constructions.exists_character_ne_zero k A 1 one_ne_zero
  let : Nontrivial (A ⊗[k] B) := (specializeLeft (B := B) χ).toRingHom.domain_nontrivial
  let : NoZeroDivisors (A ⊗[k] B) := ⟨by
    intro x y hxy
    by_cases hx : x = 0
    · exact Or.inl hx
    right
    by_contra hy
    obtain ⟨φ, hφx, hφy⟩ := exists_specialization_two_ne_zero x y hx hy
    apply mul_ne_zero hφx hφy
    rw [← map_mul, hxy, map_zero]⟩
  exact NoZeroDivisors.to_isDomain _

end AlgebraicGeometry.CycleClass.Thom.Tensor.ProductDomain.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Tensor.ProductDomain.Constructions.Reduced

/-! Character specialization is jointly injective and proves reducedness
of the actual tensor product, including zero algebras and empty affine opens. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.TypeCharacters.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductDomain.Constructions

variable {k A B : Type*} [Field k] [IsAlgClosed k]
  [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  [Algebra.FiniteType k A] [IsReduced A]

theorem specialization_ext (x y : A ⊗[k] B)
    (h : ∀ χ : A →ₐ[k] k, specializeLeft χ x = specializeLeft χ y) : x = y := by
  classical
  let b := Module.Free.chooseBasis k B
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  apply Finite.TypeCharacters.Constructions.character_ext k A
  intro χ
  rw [← specializeLeft_coefficient b χ x i, ← specializeLeft_coefficient b χ y i, h χ]

theorem tensorProduct_isReduced [IsReduced B] : IsReduced (A ⊗[k] B) := by
  let e : A ⊗[k] B →+* ((A →ₐ[k] k) → B) :=
    RingHom.pi (fun χ => (specializeLeft χ).toRingHom)
  apply isReduced_of_injective e
  intro x y h
  exact specialization_ext x y (fun χ => congrFun h χ)

end AlgebraicGeometry.CycleClass.Thom.Tensor.ProductDomain.Constructions.Reduced

end

end OAI
