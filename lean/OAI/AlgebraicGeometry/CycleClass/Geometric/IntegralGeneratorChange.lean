import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Ring.Int.Units

/-! # Integral Generator Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralGeneratorChange.Cycles

/-!
# Changes between integral rank-one normalizations

Two actual integral linear isomorphisms to the integers specify primitive
generators. Their comparison coefficient is a unit of the integers, hence
one or negative one. This is independent of any choice of a positive
geometric orientation.
-/

section

universe u

variable {H : Type u} [AddCommGroup H] [Module ℤ H]

/-- The coefficient of the second specified primitive generator in the first
specified integral coordinate system. -/
def integralGeneratorChange (e e' : H ≃ₗ[ℤ] ℤ) : ℤ := e (e'.symm 1)

/-- An actual isomorphism with the integers expands every vector in its
specified primitive generator. -/
theorem integralGenerator_expansion (e : H ≃ₗ[ℤ] ℤ) (x : H) :
    x = e x • e.symm 1 := by
  apply e.injective
  rw [map_zsmul, e.apply_symm_apply]
  simp

/-- The generator change has the stated coefficient, without choosing a
separate basis or an arbitrary nonzero vector. -/
theorem integralGeneratorChange_generator (e e' : H ≃ₗ[ℤ] ℤ) :
    e'.symm 1 = integralGeneratorChange e e' • e.symm 1 :=
  integralGenerator_expansion e (e'.symm 1)

/-- The corresponding coordinate functionals have the reciprocal relation. -/
theorem integralGeneratorChange_apply (e e' : H ≃ₗ[ℤ] ℤ) (x : H) :
    e x = integralGeneratorChange e e' * e' x := by
  calc
    e x = e (e' x • e'.symm 1) := congrArg e (integralGenerator_expansion e' x)
    _ = integralGeneratorChange e e' * e' x := by
      rw [map_zsmul]
      change e' x * e (e'.symm 1) = e (e'.symm 1) * e' x
      exact mul_comm _ _

theorem integralGeneratorChange_coordinates (e e' : H ≃ₗ[ℤ] ℤ) :
    e.toLinearMap = integralGeneratorChange e e' • e'.toLinearMap := by
  ext x
  exact integralGeneratorChange_apply e e' x

@[simp]
theorem integralGeneratorChange_self (e : H ≃ₗ[ℤ] ℤ) :
    integralGeneratorChange e e = 1 := e.apply_symm_apply 1

/-- Reversing the two normalizations supplies an actual multiplicative inverse. -/
theorem integralGeneratorChange_mul_swap (e e' : H ≃ₗ[ℤ] ℤ) :
    integralGeneratorChange e e' * integralGeneratorChange e' e = 1 := by
  have h := integralGeneratorChange_apply e e' (e.symm 1)
  rw [e.apply_symm_apply] at h
  exact h.symm

/-- Integral primitive-generator changes are units, proved using the inverse
coordinate change rather than a nonzero assumption. -/
theorem integralGeneratorChange_isUnit (e e' : H ≃ₗ[ℤ] ℤ) :
    IsUnit (integralGeneratorChange e e') :=
  isUnit_iff_exists_inv.mpr
    ⟨integralGeneratorChange e' e, integralGeneratorChange_mul_swap e e'⟩

theorem integralGeneratorChange_eq_one_or_neg_one (e e' : H ≃ₗ[ℤ] ℤ) :
    integralGeneratorChange e e' = 1 ∨ integralGeneratorChange e e' = -1 :=
  Int.isUnit_eq_one_or (integralGeneratorChange_isUnit e e')

theorem integralGeneratorChange_ne_zero (e e' : H ≃ₗ[ℤ] ℤ) :
    integralGeneratorChange e e' ≠ 0 :=
  (integralGeneratorChange_isUnit e e').ne_zero

/-- Successive changes of actual integral normalizations compose multiplicatively. -/
theorem integralGeneratorChange_comp (e e' e'' : H ≃ₗ[ℤ] ℤ) :
    integralGeneratorChange e e'' =
      integralGeneratorChange e e' * integralGeneratorChange e' e'' :=
  integralGeneratorChange_apply e e' (e''.symm 1)

/-- The two primitive generators are equal or negatives of one another. -/
theorem integralGenerators_eq_or_eq_neg (e e' : H ≃ₗ[ℤ] ℤ) :
    e'.symm 1 = e.symm 1 ∨ e'.symm 1 = -(e.symm 1) := by
  rcases integralGeneratorChange_eq_one_or_neg_one e e' with h | h
  · exact Or.inl (by simpa only [h, one_smul] using integralGeneratorChange_generator e e')
  · exact Or.inr (by simpa only [h, neg_one_zsmul] using integralGeneratorChange_generator e e')

/-- The integral coordinate functionals likewise differ only by sign. -/
theorem integralCoordinates_eq_or_eq_neg (e e' : H ≃ₗ[ℤ] ℤ) :
    e.toLinearMap = e'.toLinearMap ∨ e.toLinearMap = -e'.toLinearMap := by
  rcases integralGeneratorChange_eq_one_or_neg_one e e' with h | h
  · exact Or.inl (by simpa only [h, one_smul] using integralGeneratorChange_coordinates e e')
  · exact Or.inr (by simpa only [h, neg_one_zsmul] using integralGeneratorChange_coordinates e e')

end

universe u

variable {A : Type u} [AddCommGroup A]

/-- The same statement for actual additive-group isomorphisms, using their
canonical integral linear structure. -/
theorem addEquiv_generators_eq_or_eq_neg (e e' : A ≃+ ℤ) :
    e'.symm 1 = e.symm 1 ∨ e'.symm 1 = -(e.symm 1) :=
  integralGenerators_eq_or_eq_neg e.toIntLinearEquiv e'.toIntLinearEquiv

end OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralGeneratorChange.Cycles
