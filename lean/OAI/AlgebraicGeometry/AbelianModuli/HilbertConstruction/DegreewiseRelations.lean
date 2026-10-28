import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ComponentMultiplication

/-! # Degreewise Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreewiseRelations

noncomputable section

/-!
Polynomials whose homogeneous pieces lie in a prescribed family of submodules.
Stability under variable multiplication implies stability under every polynomial.
-/

universe u v

variable {R : Type u} [CommRing R] {σ : Type v}
variable (N : ∀ d, Submodule R (MvPolynomial.homogeneousSubmodule σ R d))

def degreewiseRelationsSubmodule : Submodule R (MvPolynomial σ R) where
  carrier := {p | ∀ d, Homogeneous.ComponentMultiplication.homogeneousComponentSection d p ∈ N d}
  zero_mem' d := by rw [map_zero]; exact (N d).zero_mem
  add_mem' hp hq d := by rw [map_add]; exact (N d).add_mem (hp d) (hq d)
  smul_mem' r _p hp d := by rw [map_smul]; exact (N d).smul_mem r (hp d)

theorem degreewiseRelations_mem_homogeneous {d : ℕ}
    (p : MvPolynomial.homogeneousSubmodule σ R d) :
    p.val ∈ degreewiseRelationsSubmodule N ↔ p ∈ N d := by
  have hd : Homogeneous.ComponentMultiplication.homogeneousComponentSection d p.val = p :=
    Subtype.ext (MvPolynomial.homogeneousComponent_eq_self p.property)
  constructor
  · intro hp
    exact hd ▸ hp d
  · intro hp e
    by_cases he : e = d
    · subst e
      rwa [hd]
    · have hz : Homogeneous.ComponentMultiplication.homogeneousComponentSection e p.val = 0 := by
        apply Subtype.ext
        exact (MvPolynomial.homogeneousComponent_of_mem p.property).trans (ite_eq_right he)
      rw [hz]
      exact (N e).zero_mem

theorem degreewiseRelations_component {p : MvPolynomial σ R}
    (hp : p ∈ degreewiseRelationsSubmodule N) (d : ℕ) :
    MvPolynomial.homogeneousComponent d p ∈ degreewiseRelationsSubmodule N :=
  (degreewiseRelations_mem_homogeneous N
    ⟨MvPolynomial.homogeneousComponent d p, MvPolynomial.homogeneousComponent_mem d p⟩).mpr (hp d)

variable (hN : ∀ d i, N d ≤ (N (d + 1)).comap (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i))
include hN

theorem degreewiseRelations_variable_mul {p : MvPolynomial σ R}
    (hp : p ∈ degreewiseRelationsSubmodule N) (i : σ) :
    MvPolynomial.X i * p ∈ degreewiseRelationsSubmodule N := by
  intro d
  cases d with
  | zero =>
      have hz : Homogeneous.ComponentMultiplication.homogeneousComponentSection 0 (MvPolynomial.X i * p) = 0 :=
        Subtype.ext (Homogeneous.ComponentMultiplication.homogeneousComponent_variable_mul_zero i p)
      rw [hz]
      exact (N 0).zero_mem
  | succ d =>
      have he : Homogeneous.ComponentMultiplication.homogeneousComponentSection (d + 1) (MvPolynomial.X i * p) =
          Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i (Homogeneous.ComponentMultiplication.homogeneousComponentSection d p) :=
        Subtype.ext (Homogeneous.ComponentMultiplication.homogeneousComponent_variable_mul_succ i p d)
      rw [he]
      exact hN d i (hp d)

theorem degreewiseRelations_mul {p : MvPolynomial σ R}
    (hp : p ∈ degreewiseRelationsSubmodule N) (q : MvPolynomial σ R) :
    q * p ∈ degreewiseRelationsSubmodule N := by
  induction q using MvPolynomial.induction_on with
  | C r =>
      rw [MvPolynomial.C_mul']
      exact (degreewiseRelationsSubmodule N).smul_mem r hp
  | add a b ha hb =>
      rw [add_mul]
      exact (degreewiseRelationsSubmodule N).add_mem ha hb
  | mul_X a i ha =>
      have he : (a * MvPolynomial.X i) * p = MvPolynomial.X i * (a * p) := by ac_rfl
      rw [he]
      exact degreewiseRelations_variable_mul N hN ha i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreewiseRelations
