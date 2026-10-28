import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ExponentFiniteGeneration
import Mathlib.RingTheory.FiniteType

/-! # Monomial Algebra -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialAlgebra

noncomputable section

/-! Equal-degree monomials in a finite family of determinant generators
generate a finite-type algebra. The proof uses the constructed finite
generation of their exponent monoid. -/
open scoped BigOperators Classical
universe u v w
variable {κ : Type u} [Fintype κ] {ι : Type v}
variable {R A : Type w} [CommRing R] [CommRing A] [Algebra R A]

def exponentMonomial (D : κ → A) (a : κ → ℕ) : A := ∏ k, D k ^ a k

theorem exponentMonomial_zero (D : κ → A) : exponentMonomial D 0 = 1 := by
  simp only [exponentMonomial, Pi.zero_apply, pow_zero, Finset.prod_const_one]

theorem exponentMonomial_add (D : κ → A) (a b : κ → ℕ) :
    exponentMonomial D (a + b) = exponentMonomial D a * exponentMonomial D b := by
  simp only [exponentMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

def balancedMonomialAlgebra (R : Type w) [CommRing R] [Algebra R A]
    (D : κ → A) (w : κ → ι → ℕ) : Subalgebra R A :=
  Algebra.adjoin R (exponentMonomial D '' (ExponentFiniteGeneration.balancedExponentMonoid w : Set (κ → ℕ)))

theorem balancedMonomialAlgebra_fg (D : κ → A) (w : κ → ι → ℕ) :
    (balancedMonomialAlgebra R D w).FG := by
  obtain ⟨B, hB⟩ := ExponentFiniteGeneration.balancedExponentMonoid_fg w
  let C := B.image (exponentMonomial D)
  refine ⟨C, le_antisymm ?_ ?_⟩
  · apply Algebra.adjoin_le
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    apply Algebra.subset_adjoin
    refine ⟨b, ?_, rfl⟩
    rw [← hB]
    exact AddSubmonoid.subset_closure hb
  · apply Algebra.adjoin_le
    rintro _ ⟨a, ha, rfl⟩
    have hac : a ∈ AddSubmonoid.closure (B : Set (κ → ℕ)) := hB.symm ▸ ha
    refine AddSubmonoid.closure_induction (fun b hb => ?_) ?_ ?_ hac
    · exact Algebra.subset_adjoin (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    · rw [exponentMonomial_zero]
      exact (Algebra.adjoin R (C : Set A)).one_mem
    · intro a b _ _ ha hb
      rw [exponentMonomial_add]
      exact (Algebra.adjoin R (C : Set A)).mul_mem ha hb

theorem balancedMonomialAlgebra_finiteType (D : κ → A) (w : κ → ι → ℕ) :
    Algebra.FiniteType R (balancedMonomialAlgebra R D w) :=
  (Subalgebra.fg_iff_finiteType _).mp (balancedMonomialAlgebra_fg D w)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialAlgebra
