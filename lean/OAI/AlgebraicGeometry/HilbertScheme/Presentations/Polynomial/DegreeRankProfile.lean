import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.DegreeLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Truncation

/-! # Degree Rank Profile -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert

noncomputable section

/-! The relation-rank profile determined by the Hilbert polynomial. Its
realizability is verified against actual homogeneous quotients. -/

universe u

def polynomialDegreeRankProfile (n N : ℕ) (P : Polynomial ℚ) (d : ℕ) : ℕ :=
  Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N)) - (P.eval ((d + N : ℕ) : ℚ)).num.toNat

variable {K : Type u} [Field K] {n : ℕ}

theorem hilbertFunction_le_degreeIndex (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction I d ≤ Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n d) := by
  have h := Submodule.finrank_quotient_le (Hilbert.Polynomial.GradedHilbert.degreeRelations I d)
  rw [Module.finrank_eq_card_basis (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis K n d)] at h
  exact h

theorem polynomialDegreeRankProfile_add (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
    (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)
    (N : ℕ) (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N) (d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal (d + N) + polynomialDegreeRankProfile.{u} n N P d =
      Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (d + N)) := by
  have h := (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P K I hI hP).2 (d + N)
    (hN.trans (Nat.le_add_left N d))
  unfold polynomialDegreeRankProfile
  rw [← h]
  simp only [Rat.num_natCast, Int.toNat_natCast]
  exact Nat.add_sub_of_le (hilbertFunction_le_degreeIndex I.toIdeal (d + N))

theorem polynomialDegreeRankProfile_realizes (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
    (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)
    (N : ℕ) (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N) :
    BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (polynomialDegreeRankProfile.{u} n N P) P := by
  refine ⟨Finite.PolynomialTest.GradedHilbert.hilbertPolynomial_natDegree_le I P hP, fun i => ?_⟩
  have h := polynomialDegreeRankProfile_add I hI P hP N hN (BoundedHilbert.DegreeLocus.GradedHilbert.hilbertTestDegree n N i)
  rw [BoundedHilbert.DegreeLocus.GradedHilbert.hilbertTestDegree_add] at h
  have he : Fintype.card (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n (Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val)) -
      polynomialDegreeRankProfile.{u} n N P (BoundedHilbert.DegreeLocus.GradedHilbert.hilbertTestDegree n N i) =
      Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal (Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val) := by omega
  rw [he]
  exact (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P K I hI hP).2 _
    (hN.trans ((Local.RankTest.GradedHilbert.generatorHilbertFunctionBound_ge n N).trans (Nat.le_add_right _ _)))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert
