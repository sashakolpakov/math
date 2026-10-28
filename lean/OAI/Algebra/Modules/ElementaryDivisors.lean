import OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear
import Lean.Util.CollectAxioms

/-! # Elementary Divisors -/

namespace OAI.Algebra.Modules.ElementaryDivisors

/-!
# ElementaryDivisors: elementary divisors for DVR lattices

These four proved declarations reproduce the types in Statements/ElementaryDivisors.lean.
The proof uses Mathlib's PID diagonalization, denominator clearing, and a
unit permutation term in the determinant to prove uniqueness. The matrix
statements then follow by changing integral bases. No statement stub is imported.
-/

open scoped BigOperators

variable {R K : Type*}
  [CommRing R] [hDomain : IsDomain R] [hDVR : IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [hFraction : IsFractionRing R K]

/-- Simultaneous elementary-divisor form for two full lattices. -/
theorem lattices_elementary_divisors
    {n : ℕ} (π : R) (hπ : Irreducible π)
    (L M : Submodule R (Fin n → K))
    [Submodule.IsLattice K L] [Submodule.IsLattice K M] :
    ∃! a : Fin n → ℤ,
      Monotone a ∧
      ∃ e : Module.Basis (Fin n) K (Fin n → K),
        L = Submodule.span R (Set.range fun i => e i) ∧
        M = Submodule.span R
          (Set.range fun i =>
            (algebraMap R K π) ^ (a i) • e i) := by
  exact ElementaryDivisorsExistenceLinear.Construction.lattices_elementary_divisors π hπ L M

/-- Unique ordered representatives for integral GL₃ double cosets. -/
theorem gl3_smith_normal_form
    (π : R) (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin 3) K) :
    ∃! a : Fin 3 → ℤ,
      Monotone a ∧
      ∃ U V : Matrix.GeneralLinearGroup (Fin 3) R,
        g.val =
          U.val.map (algebraMap R K) *
          Matrix.diagonal (fun i => (algebraMap R K π) ^ (a i)) *
          V.val.map (algebraMap R K) := by
  exact ElementaryDivisorsExistenceLinear.Construction.gl3_smith_normal_form π hπ g

/-- A unit determinant can be adjusted to one by an integral
basis change, preserving the lattice spanned by the columns. -/
theorem gl3_determinant_unit_adjustment
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (g : Matrix.GeneralLinearGroup (Fin 3) K)
    (hdet : ∃ u : Rˣ,
      g.val.det = algebraMap R K (u : R)) :
    ∃ U : Matrix.GeneralLinearGroup (Fin 3) R,
      (g.val * U.val.map (algebraMap R K)).det = 1 := by
  exact ElementaryDivisorsExistenceLinear.Construction.gl3_determinant_unit_adjustment g hdet

/-- Integral SL₃ double cosets have unique ordered exponent triples
whose sum is zero. -/
theorem sl3_smith_normal_form
    (π : R) (hπ : Irreducible π)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    ∃! a : Fin 3 → ℤ,
      Monotone a ∧
      (∑ i, a i) = 0 ∧
      ∃ U V : Matrix.SpecialLinearGroup (Fin 3) R,
        (g : Matrix (Fin 3) (Fin 3) K) =
          (U : Matrix (Fin 3) (Fin 3) R).map (algebraMap R K) *
          Matrix.diagonal (fun i => (algebraMap R K π) ^ (a i)) *
          (V : Matrix (Fin 3) (Fin 3) R).map (algebraMap R K) := by
  exact ElementaryDivisorsExistenceLinear.Construction.sl3_smith_normal_form π hπ g

end OAI.Algebra.Modules.ElementaryDivisors
