import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialAlgebra
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # Monomial Span -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialSpan

noncomputable section

/-! The balanced algebra is the linear span of its balanced monomials.
This identifies its degree pieces without adding any invariant-ring hypothesis. -/
open scoped BigOperators Classical Pointwise
universe u v w
variable {κ : Type u} [Fintype κ] {ι : Type v}
variable {R A : Type w} [CommRing R] [CommRing A] [Algebra R A]

def exponentMonomialSubmonoid (D : κ → A) (M : AddSubmonoid (κ → ℕ)) : Submonoid A where
  carrier := MonomialAlgebra.exponentMonomial D '' (M : Set (κ → ℕ))
  one_mem' := ⟨0, M.zero_mem, MonomialAlgebra.exponentMonomial_zero D⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, M.add_mem ha hb, MonomialAlgebra.exponentMonomial_add D a b⟩

theorem balancedMonomialAlgebra_eq_span (D : κ → A) (w : κ → ι → ℕ) :
    (MonomialAlgebra.balancedMonomialAlgebra R D w).toSubmodule =
      Submodule.span R (MonomialAlgebra.exponentMonomial D '' (ExponentFiniteGeneration.balancedExponentMonoid w : Set (κ → ℕ))) := by
  change (Algebra.adjoin R (exponentMonomialSubmonoid D (ExponentFiniteGeneration.balancedExponentMonoid w) : Set A)).toSubmodule = _
  rw [Algebra.adjoin_eq_span, Submonoid.closure_eq]
  rfl

def balancedMonomialDegreeSpan (D : κ → A) (w : κ → ι → ℕ) (i : ι) (n : ℕ) : Submodule R A :=
  Submodule.span R (MonomialAlgebra.exponentMonomial D ''
    {a | a ∈ ExponentFiniteGeneration.balancedExponentMonoid w ∧ ExponentFiniteGeneration.monomialMultiDegree w a i = n})

theorem balancedMonomialDegreeSpan_le (D : κ → A) (w : κ → ι → ℕ) (i : ι) (n : ℕ) :
    balancedMonomialDegreeSpan D w i n ≤ (MonomialAlgebra.balancedMonomialAlgebra R D w).toSubmodule := by
  rw [balancedMonomialAlgebra_eq_span]
  exact Submodule.span_mono (Set.image_mono fun _ ha => ha.1)

theorem balancedMonomialDegreeSpan_mul (D : κ → A) (w : κ → ι → ℕ) (i : ι) (n t : ℕ) :
    balancedMonomialDegreeSpan (R := R) D w i n * balancedMonomialDegreeSpan D w i t ≤
      balancedMonomialDegreeSpan D w i (n + t) := by
  unfold balancedMonomialDegreeSpan
  rw [Submodule.span_mul_span]
  apply Submodule.span_mono
  rintro _ ⟨x, ⟨a, ha, rfl⟩, y, ⟨b, hb, rfl⟩, rfl⟩
  refine ⟨a + b, ⟨(ExponentFiniteGeneration.balancedExponentMonoid w).add_mem ha.1 hb.1, ?_⟩, MonomialAlgebra.exponentMonomial_add D a b⟩
  rw [ExponentFiniteGeneration.monomialMultiDegree_add, ha.2, hb.2]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialSpan
