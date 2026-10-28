import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Supported Bilinear Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SupportedBilinearDimension

noncomputable section

/-! Symmetric bilinear forms supported between two specified sets
of basis vectors inject into their rectangular coefficient matrix.
Their dimension is at most the product of the two set sizes. -/

variable {k V I : Type*} [Field k] [AddCommGroup V] [Module k V] [DecidableEq I]
    (b : Module.Basis I k V) (L R : Finset I)

def basisCrossSymmetricForms : Submodule k (V →ₗ[k] V →ₗ[k] k) where
  carrier := {B | (∀ i j, B (b i) (b j) = B (b j) (b i)) ∧
    ∀ i j, ¬ ((i ∈ L ∧ j ∈ R) ∨ (i ∈ R ∧ j ∈ L)) → B (b i) (b j) = 0}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  add_mem' := by
    intro x y hx hy
    constructor
    · intro i j
      change x (b i) (b j) + y (b i) (b j) = x (b j) (b i) + y (b j) (b i)
      rw [hx.1 i j, hy.1 i j]
    · intro i j h
      change x (b i) (b j) + y (b i) (b j) = 0
      rw [hx.2 i j h, hy.2 i j h, add_zero]
  smul_mem' c x hx := by
    constructor
    · intro i j
      change c * _ = c * _
      rw [hx.1 i j]
    · intro i j h
      change c * _ = 0
      rw [hx.2 i j h, mul_zero]

def basisCrossCoefficientLinear : basisCrossSymmetricForms b L R →ₗ[k] (L → R → k) where
  toFun F i j := F.val (b i.val) (b j.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem basisCrossCoefficientLinear_injective : Function.Injective (basisCrossCoefficientLinear b L R) := by
  intro F G h
  apply Subtype.ext
  apply b.ext
  intro i
  apply b.ext
  intro j
  by_cases hs : (i ∈ L ∧ j ∈ R) ∨ (i ∈ R ∧ j ∈ L)
  · rcases hs with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · exact congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
    · rw [F.property.1 i j, G.property.1 i j]
      exact congrFun (congrFun h ⟨j, hj⟩) ⟨i, hi⟩
  · rw [F.property.2 i j hs, G.property.2 i j hs]

theorem basisCrossSymmetricForms_finrank_le :
    Module.finrank k (basisCrossSymmetricForms b L R) ≤ L.card * R.card := by
  have h := LinearMap.finrank_le_finrank_of_injective (basisCrossCoefficientLinear_injective b L R)
  simpa only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_one] using h

theorem basisCrossSymmetricForms_finrank_le_two (hL : L.card = 2) (hR : R.card = 1) :
    Module.finrank k (basisCrossSymmetricForms b L R) ≤ 2 := by
  have h := basisCrossSymmetricForms_finrank_le b L R
  simpa only [hL, hR, mul_one] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SupportedBilinearDimension
