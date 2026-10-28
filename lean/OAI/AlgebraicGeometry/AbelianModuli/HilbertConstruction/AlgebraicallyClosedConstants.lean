import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Integral

/-! # Algebraically Closed Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraicallyClosedConstants

noncomputable section

/-! In a domain algebra over an algebraically closed field, algebraic elements are precisely scalar constants. -/

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {R : Type v} [CommRing R] [IsDomain R] [Algebra K R]

theorem algebraic_is_scalar (x : R) (hx : IsAlgebraic K x) : ∃ c : K, algebraMap K R c = x := by
  have hi : _root_.IsIntegral K x := hx.isIntegral
  have hq : (minpoly K x).leadingCoeff = 1 := minpoly.monic hi
  have hd : (minpoly K x).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hi)
  have h : Polynomial.aeval x (minpoly K x) = 0 := minpoly.aeval K x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd, hq, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at h
  exact ⟨-(minpoly K x).coeff 0, (map_neg (algebraMap K R) _).trans h.symm⟩

theorem transcendental_iff_not_scalar (x : R) :
    Transcendental K x ↔ ¬ ∃ c : K, algebraMap K R c = x := by
  constructor
  · rintro hx ⟨c, rfl⟩
    exact hx (isAlgebraic_algebraMap c)
  · intro hx ha
    exact hx (algebraic_is_scalar x ha)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraicallyClosedConstants
