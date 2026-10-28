import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Invariant Basis Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantBasisOf.Construction.InvariantBasis

/-!
# Invariant coefficients for an affine quotient

This is the coefficient argument in the affine finite-flat quotient construction
(Stacks, Tag 03BL). The hypotheses are identities between the source, target,
composition, and pullback ring maps, together with a basis and its base-changed
linear independence. No quotient existence or freeness over invariants is assumed.
-/

open scoped BigOperators TensorProduct
open _root_.Module

universe u v w z

variable {A : Type u} {B : Type v} {D : Type w} {ι : Type z}
variable [CommRing A] [CommRing B] [CommRing D]
variable [Algebra A B] [Algebra B D] [Fintype ι]

/-- Coefficients of a target-valued element in a target-valued source basis
are invariant under the two structural ring maps. -/
theorem coefficients_invariant
    (t : A →+* B) (p c : B →+* D)
    (hp : ∀ a, p (algebraMap A B a) = algebraMap B D (t a))
    (hc : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a))
    (hct : ∀ a, c (t a) = p (t a))
    (x : ι → A) (b : Basis ι A B) (hb : ∀ i, b i = t (x i))
    (hind : LinearIndependent B (fun i => p (b i)))
    (a : A) (j : ι) :
    algebraMap A B (b.repr (t a) j) = t (b.repr (t a) j) := by
  classical
  have hp_sum :
      (∑ i, t (b.repr (t a) i) • p (b i)) = p (t a) := by
    calc
      _ = p (∑ i, b.repr (t a) i • b i) := by
        simp only [map_sum, Algebra.smul_def, map_mul, hp]
      _ = p (t a) := congrArg p (b.sum_repr (t a))
  have hc_sum :
      (∑ i, algebraMap A B (b.repr (t a) i) • p (b i)) = c (t a) := by
    calc
      _ = c (∑ i, b.repr (t a) i • b i) := by
        simp only [map_sum, Algebra.smul_def, map_mul, hc, hb, hct]
      _ = c (t a) := congrArg c (b.sum_repr (t a))
  exact hind.eq_coords_of_eq (hc_sum.trans ((hct a).trans hp_sum.symm)) j

/-- A basis supplied by target-valued elements descends to a basis over the
actual invariant subring. This proves the freeness conclusion, rather than
assuming it as part of a quotient interface. -/
theorem exists_basis_over_invariants
    (t : A →+* B) (ht : Function.Injective t) (p c : B →+* D)
    (hp : ∀ a, p (algebraMap A B a) = algebraMap B D (t a))
    (hc : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a))
    (hct : ∀ a, c (t a) = p (t a))
    (x : ι → A) (b : Basis ι A B) (hb : ∀ i, b i = t (x i))
    (hind : LinearIndependent B (fun i => p (b i))) :
    let C := (algebraMap A B).eqLocus t
    letI : Algebra C A := C.subtype.toAlgebra
    ∃ bC : Basis ι C A, ∀ i, bC i = x i := by
  classical
  let C := (algebraMap A B).eqLocus t
  let : Algebra C A := C.subtype.toAlgebra
  change ∃ bC : Basis ι C A, ∀ i, bC i = x i
  have hmap (d : ι → C) :
      t (∑ i, d i • x i) = ∑ i, (d i : A) • b i := by
    change t (∑ i, (d i : A) * x i) = ∑ i, (d i : A) • b i
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, ← (d i).property, ← hb i, Algebra.smul_def]
  let d (a : A) (i : ι) : C :=
    ⟨b.repr (t a) i, coefficients_invariant t p c hp hc hct x b hb hind a i⟩
  have hsum (a : A) : ∑ i, d a i • x i = a := by
    apply ht
    rw [hmap]
    exact b.sum_repr (t a)
  have hli : LinearIndependent C x := by
    apply Fintype.linearIndependent_iff.mpr
    intro e he i
    have he' : ∑ j, (e j : A) • b j = 0 := by
      rw [← hmap, he, map_zero]
    apply Subtype.ext
    exact Fintype.linearIndependent_iff.mp b.linearIndependent _ he' i
  have hspan : ⊤ ≤ Submodule.span C (Set.range x) := by
    intro a _
    rw [← hsum a]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Basis.mk hli hspan, Basis.mk_apply hli hspan⟩

omit [Fintype ι] in
/-- If the images of a basis form a basis after base change, the canonical
tensor-product map is bijective. -/
theorem tensor_lift_bijective_of_bases
    {R : Type*} [CommRing R] [Algebra R A] [Algebra R B] [IsScalarTower R A B]
    (t : A →ₐ[R] B) (bA : Basis ι R A) (bB : Basis ι A B)
    (hb : ∀ i, bB i = t (bA i)) :
    Function.Bijective (t.liftEquiv R A A B) := by
  let e := (bA.baseChange A).equiv bB (Equiv.refl ι)
  have he : (t.liftEquiv R A A B).toLinearMap = e.toLinearMap := by
    apply (bA.baseChange A).ext
    intro i
    change (t.liftEquiv R A A B) (bA.baseChange A i) =
      (bA.baseChange A).equiv bB (Equiv.refl ι) (bA.baseChange A i)
    rw [Basis.equiv_apply]
    simp [hb]
  have he' : (t.liftEquiv R A A B : A ⊗[R] A → B) = e :=
    congrArg (fun f : A ⊗[R] A →ₗ[A] B => (f : A ⊗[R] A → B)) he
  rw [he']
  exact e.bijective

/-- The affine basis criterion yields finite freeness over invariants and
the tensor-product description of the relation algebra. -/
theorem finiteFree_and_tensor_of_target_basis
    (t : A →+* B) (ht : Function.Injective t) (p c : B →+* D)
    (hp : ∀ a, p (algebraMap A B a) = algebraMap B D (t a))
    (hc : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a))
    (hct : ∀ a, c (t a) = p (t a))
    (x : ι → A) (b : Basis ι A B) (hb : ∀ i, b i = t (x i))
    (hind : LinearIndependent B (fun i => p (b i))) :
    let C := (algebraMap A B).eqLocus t
    letI : Algebra C A := C.subtype.toAlgebra
    Module.Free C A ∧ Module.Finite C A ∧
      ∃ e : A ⊗[C] A ≃ₐ[A] B, ∀ a a', e (a ⊗ₜ[C] a') = algebraMap A B a * t a' := by
  let C := (algebraMap A B).eqLocus t
  let : Algebra C A := C.subtype.toAlgebra
  let : Algebra C B := ((algebraMap A B).comp C.subtype).toAlgebra
  have : IsScalarTower C A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let tC : A →ₐ[C] B := { t with commutes' := fun r => r.property.symm }
  obtain ⟨bC, hbC⟩ := exists_basis_over_invariants t ht p c hp hc hct x b hb hind
  refine ⟨Module.Free.of_basis bC, Module.Finite.of_basis bC, ?_⟩
  have hbij : Function.Bijective (tC.liftEquiv C A A B) := by
    apply tensor_lift_bijective_of_bases tC bC b
    intro i
    change b i = t (bC i)
    rw [hbC, hb]
  refine ⟨AlgEquiv.ofBijective (tC.liftEquiv C A A B) hbij, ?_⟩
  intro a a'
  exact Algebra.smul_def a (t a')

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantBasisOf.Construction.InvariantBasis
