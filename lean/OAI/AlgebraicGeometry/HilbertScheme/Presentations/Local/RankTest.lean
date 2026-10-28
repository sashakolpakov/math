import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.DegreeRankSpecialization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedPolynomialTest

/-! # Rank Test -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.RankTest.GradedHilbert

noncomputable section

/-! Over a local base, a flat homogeneous family has a prescribed field-fiber
Hilbert polynomial exactly when finitely many actual quotient ranks have the
prescribed values. -/

open _root_.MvPolynomial

universe u v z

theorem generatorHilbertFunctionBound_ge (n N : ℕ) : N ≤ Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N := by
  unfold Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound Uniform.GroebnerCompletion.GradedHilbert.homogeneousGroebnerDegreeBound
  have hp : 1 ≤ 2 ^ ControlledCompletionCertificates.GradedHilbert.polynomialCompletionHorizon n N := Nat.one_le_two_pow
  have hN : N ≤ N * 2 ^ ControlledCompletionCertificates.GradedHilbert.polynomialCompletionHorizon n N := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hp
  exact hN.trans (by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right (N * 2 ^ ControlledCompletionCertificates.GradedHilbert.polynomialCompletionHorizon n N) (Nat.succ_le_succ (Nat.zero_le n)))

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {K : Type v} [Field K] [Algebra R K]
variable {n : ℕ} {ι : Type z} [Fintype ι]

theorem homogeneous_local_hilbertPolynomial_rank_test
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (hflat : ∀ d, Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N)))
    (P : Polynomial ℚ) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R K) g) N
      (fun i => (hg i).map (algebraMap R K))).toIdeal P ↔
      P.natDegree ≤ n ∧ ∀ i : Fin (n + 1),
        (Module.finrank R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal
          (Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val)) : ℚ) =
            P.eval ((Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val : ℕ) : ℚ) := by
  refine (GeneratedPolynomialTest.GradedHilbert.homogeneousGenerators_hilbertPolynomial_finite_test
    (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R K) g) N (fun i => (hg i).map (algebraMap R K)) P).trans ?_
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  have hd : N ≤ Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val :=
    (generatorHilbertFunctionBound_ge n N).trans (Nat.le_add_right _ _)
  have hr : Module.finrank K (Hilbert.Polynomial.GradedHilbert.DegreeQuotient
      (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R K) g) N
        (fun i => (hg i).map (algebraMap R K))).toIdeal (Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val)) =
      Module.finrank R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal
        (Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val)) := by
    rw [← Nat.sub_add_cancel hd]
    let := hflat (Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val - N)
    exact DegreeRankSpecialization.GradedHilbert.homogeneousDegree_finrank_baseChange_of_local_flat g N hg _
  change ((Module.finrank K _ : ℚ) = _) ↔ _
  rw [hr]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.RankTest.GradedHilbert
