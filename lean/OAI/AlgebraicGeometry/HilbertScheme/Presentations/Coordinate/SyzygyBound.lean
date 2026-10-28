import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.SyzygyGenerators

/-! # Syzygy Bound -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.SyzygyBound.GradedHilbert

noncomputable section

/-! A syzygy degree bound depending only on the number of coordinates, number of equations, and their common degree. -/

universe u v

def homogeneousSyzygyDegreeBound (n m N : ℕ) : ℕ :=
  Uniform.GroebnerCompletion.GradedHilbert.homogeneousGroebnerDegreeBound (n + m + 1) (N + 1)

theorem exists_uniform_coordinate_syzygy_generators
    {K : Type u} [Field K] {n : ℕ} {ι : Type v} [Fintype ι]
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) :
    ∃ B : Finset (ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n),
      LinearMap.ker (SyzygiesFromPolynomialKernel.GradedHilbert.polynomialRelationMap g) =
        Submodule.span (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (B : Set (ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) ∧
      ∀ b ∈ B, ∃ d ≤ homogeneousSyzygyDegreeBound n (Fintype.card ι) N,
        ∀ i, (b i).IsHomogeneous d := by
  let E : (ι ⊕ Option (Fin (n + 1))) ≃ Fin ((n + Fintype.card ι + 1) + 1) :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_fin]; omega)
  exact Uniform.SyzygyGenerators.GradedHilbert.exists_uniform_homogeneous_syzygy_generators E g N hg

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.SyzygyBound.GradedHilbert
