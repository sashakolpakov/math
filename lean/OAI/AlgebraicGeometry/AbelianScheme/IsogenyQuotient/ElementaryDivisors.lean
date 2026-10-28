import OAI.Algebra.Modules.ElementaryDivisors

/-! # Elementary Divisors -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryDivisors.Construction

/-!
The full ElementaryDivisors prerequisite, retaining all four DVR lattice/matrix clauses.
The adapters may use its lattice clause without silently replacing the
named prerequisite by the desired Hecke-correspondence conclusion.
-/

open scoped BigOperators

universe u

def ElementaryDivisorsInput : Prop :=
  ∀ {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K],
    (∀ {d : ℕ} (π : R) (_hπ : Irreducible π)
      (L M : Submodule R (Fin d → K))
      [Submodule.IsLattice K L] [Submodule.IsLattice K M],
      ∃! a : Fin d → ℤ, Monotone a ∧
        ∃ e : Module.Basis (Fin d) K (Fin d → K),
          L = Submodule.span R (Set.range e) ∧
          M = Submodule.span R (Set.range fun i => (algebraMap R K π) ^ a i • e i)) ∧
    (∀ (π : R) (_hπ : Irreducible π) (g : Matrix.GeneralLinearGroup (Fin 3) K),
      ∃! a : Fin 3 → ℤ, Monotone a ∧
        ∃ U V : Matrix.GeneralLinearGroup (Fin 3) R,
          g.val = U.val.map (algebraMap R K) *
            Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) * V.val.map (algebraMap R K)) ∧
    (∀ (g : Matrix.GeneralLinearGroup (Fin 3) K)
      (_hdet : ∃ u : Rˣ, g.val.det = algebraMap R K (u : R)),
      ∃ U : Matrix.GeneralLinearGroup (Fin 3) R,
        (g.val * U.val.map (algebraMap R K)).det = 1) ∧
    (∀ (π : R) (_hπ : Irreducible π) (g : Matrix.SpecialLinearGroup (Fin 3) K),
      ∃! a : Fin 3 → ℤ, Monotone a ∧ (∑ i, a i) = 0 ∧
        ∃ U V : Matrix.SpecialLinearGroup (Fin 3) R,
          (g : Matrix (Fin 3) (Fin 3) K) =
            (U : Matrix (Fin 3) (Fin 3) R).map (algebraMap R K) *
              Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) *
                (V : Matrix (Fin 3) (Fin 3) R).map (algebraMap R K))

/-- The independently checked ElementaryDivisors proofs discharge this complete input. -/
theorem verified_ElementaryDivisorsInput : ElementaryDivisorsInput := by
  intro R K _ _ _ _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d π hπ L M _ _
    exact OAI.Algebra.Modules.ElementaryDivisors.lattices_elementary_divisors π hπ L M
  · intro π hπ g
    exact OAI.Algebra.Modules.ElementaryDivisors.gl3_smith_normal_form π hπ g
  · intro g hg
    exact OAI.Algebra.Modules.ElementaryDivisors.gl3_determinant_unit_adjustment g hg
  · intro π hπ g
    exact OAI.Algebra.Modules.ElementaryDivisors.sl3_smith_normal_form π hπ g

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryDivisors.Construction
