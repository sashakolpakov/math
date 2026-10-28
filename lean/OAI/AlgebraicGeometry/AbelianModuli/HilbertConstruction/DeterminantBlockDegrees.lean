import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LabeledDeterminantPolynomials
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialAlgebra
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Determinant Block Degrees -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantBlockDegrees

noncomputable section

/-! Each determinant has one unit of degree for every occurrence of a
label among its columns. Products have the corresponding additive degrees. -/
open scoped BigOperators Classical
universe u
variable {R : Type u} [CommRing R] {r m : ℕ}

def pointBlockWeight (i : Fin m) (jk : Fin m × Fin r) : ℕ :=
  if jk.1 = i then 1 else 0

def labeledDeterminantWeight (σ : Fin r → Fin m) (i : Fin m) : ℕ :=
  ∑ j, if σ j = i then 1 else 0

theorem labeledDeterminantPolynomial_blockHomogeneous
    (σ : Fin r → Fin m) (i : Fin m) :
    (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R σ).IsWeightedHomogeneous
      (pointBlockWeight i) (labeledDeterminantWeight σ i) := by
  unfold LabeledDeterminantPolynomials.labeledDeterminantPolynomial LabeledDeterminantPolynomials.labeledDeterminant
  erw [Matrix.det_apply']
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro τ _
  have hp : (∏ j : Fin r, (MvPolynomial.X (σ j, τ j) : MvPolynomial (Fin m × Fin r) R)).IsWeightedHomogeneous (pointBlockWeight i) (labeledDeterminantWeight σ i) := by
    apply MvPolynomial.IsWeightedHomogeneous.prod
    intro j _
    exact MvPolynomial.isWeightedHomogeneous_X _ _ _
  simpa only [map_intCast] using hp.C_mul ((Equiv.Perm.sign τ : ℤ) : R)

theorem exponentMonomial_blockHomogeneous
    {κ : Type} [Fintype κ] (D : κ → MvPolynomial (Fin m × Fin r) R)
    (w : κ → Fin m → ℕ)
    (hD : ∀ k i, (D k).IsWeightedHomogeneous (pointBlockWeight i) (w k i))
    (a : κ → ℕ) (i : Fin m) :
    (Balanced.MonomialAlgebra.exponentMonomial D a).IsWeightedHomogeneous
      (pointBlockWeight i) (Balanced.ExponentFiniteGeneration.monomialMultiDegree w a i) := by
  apply MvPolynomial.IsWeightedHomogeneous.prod
  intro k _
  simpa only [nsmul_eq_mul, Nat.cast_id] using (hD k i).pow (a k)

theorem balancedDeterminantMonomial_blockHomogeneous
    (a : (Fin r → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid (labeledDeterminantWeight (r := r) (m := m)))
    (i j : Fin m) :
    (Balanced.MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) a).IsWeightedHomogeneous
      (pointBlockWeight i) (Balanced.ExponentFiniteGeneration.monomialMultiDegree labeledDeterminantWeight a j) := by
  rw [← (Balanced.ExponentFiniteGeneration.mem_balancedExponentMonoid_iff _ _).mp ha i j]
  exact exponentMonomial_blockHomogeneous _ _
    labeledDeterminantPolynomial_blockHomogeneous a i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantBlockDegrees
