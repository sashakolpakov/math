import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-! # Normalized Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.NormalizedCoordinates

noncomputable section

/-! Polynomial coordinates and rank-one equations on a normalized Segre chart. -/

open _root_.MvPolynomial

universe u v w

variable (R : Type u) [CommRing R] {σ : Type v} {τ : Type w}

def segreMinor (a c : σ) (b d : τ) : MvPolynomial (σ × τ) R :=
  X (a, b) * X (c, d) - X (a, d) * X (c, b)

def segreNormalizedIdeal (i : σ) (j : τ) : Ideal (MvPolynomial (σ × τ) R) :=
  Ideal.span (insert (X (i, j) - 1)
    (Set.range (fun q : (σ × τ) × (σ × τ) => segreMinor R q.1.1 q.2.1 q.1.2 q.2.2)))

abbrev SegreChartRing (i : σ) (j : τ) :=
  MvPolynomial ({a : σ // a ≠ i} ⊕ {b : τ // b ≠ j}) R

def segreRowCoordinate (i : σ) (j : τ) (a : σ) : SegreChartRing R i j := by
  classical
  exact if h : a = i then 1 else X (Sum.inl ⟨a, h⟩)

def segreColumnCoordinate (i : σ) (j : τ) (b : τ) : SegreChartRing R i j := by
  classical
  exact if h : b = j then 1 else X (Sum.inr ⟨b, h⟩)

def segreChartEvaluation (i : σ) (j : τ) :
    MvPolynomial (σ × τ) R →ₐ[R] SegreChartRing R i j :=
  aeval (fun q => segreRowCoordinate R i j q.1 * segreColumnCoordinate R i j q.2)

theorem segreChartEvaluation_minor (i a c : σ) (j b d : τ) :
    segreChartEvaluation R i j (segreMinor R a c b d) = 0 := by
  simp only [segreMinor, map_sub, map_mul, segreChartEvaluation, aeval_X]
  ring

theorem segreChartEvaluation_pivot (i : σ) (j : τ) :
    segreChartEvaluation R i j (X (i, j)) = 1 := by
  simp [segreChartEvaluation, segreRowCoordinate, segreColumnCoordinate]

theorem segreNormalizedIdeal_le_ker (i : σ) (j : τ) :
    segreNormalizedIdeal R i j ≤ RingHom.ker (segreChartEvaluation R i j).toRingHom := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases hp with rfl | ⟨q, rfl⟩
  · change segreChartEvaluation R i j (X (i, j) - 1) = 0
    rw [map_sub, segreChartEvaluation_pivot, map_one, sub_self]
  · exact segreChartEvaluation_minor R i q.1.1 q.2.1 j q.1.2 q.2.2

def segreNormalizedQuotientMap (i : σ) (j : τ) :
    (MvPolynomial (σ × τ) R ⧸ segreNormalizedIdeal R i j) →ₐ[R] SegreChartRing R i j :=
  Ideal.Quotient.liftₐ (segreNormalizedIdeal R i j) (segreChartEvaluation R i j)
    (fun _ h => segreNormalizedIdeal_le_ker R i j h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.NormalizedCoordinates
