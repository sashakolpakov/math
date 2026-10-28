import OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContractionVanishing
import OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContractionAnticommutation
import OAI.AlgebraicGeometry.Comparison.Betti.Open.AntiholomorphicContraction
import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormBasis

/-! # Contraction Vanishing -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.ContractionVanishing.Dolbeault

noncomputable section

/-! Finitely many coordinate contractions detect every positive
antiholomorphic pure form. -/

open _root_.TopologicalSpace
open scoped BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

theorem antiContraction_zero_direction (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    AntiholomorphicContraction.Dolbeault.antiContraction n (0 : E) a = 0 := by
  rw [AntiholomorphicContraction.Dolbeault.antiContraction_eq_projected]
  exact (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E [⋀^Fin n]→L[ℝ] ℂ) a.curryLeft).map_zero

theorem antiContraction_sum_direction {ι : Type} (n : ℕ) (s : Finset ι) (v : ι → E)
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    AntiholomorphicContraction.Dolbeault.antiContraction n (∑ i ∈ s, v i) a = ∑ i ∈ s, AntiholomorphicContraction.Dolbeault.antiContraction n (v i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, antiContraction_zero_direction]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, AntiholomorphicContractionAnticommutation.Dolbeault.antiContraction_add_direction, ih]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem antiContraction_zero_of_coordinates (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue (ι → ℂ) (n + 1))
    (ha : ∀ i, AntiholomorphicContraction.Dolbeault.antiContraction n (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector i) a = 0) (v : ι → ℂ) :
    AntiholomorphicContraction.Dolbeault.antiContraction n v a = 0 := by
  rw [← DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector_decomposition v, antiContraction_sum_direction]
  apply Finset.sum_eq_zero
  intro i _
  rw [AntiholomorphicContraction.Dolbeault.antiContraction_smul_direction, ha i]
  ext w
  change star (v i) * (0 : ℂ) = 0
  exact mul_zero _

theorem pureOpenForm_eq_zero_of_coordinate_contractions {U : Opens (ι → ℂ)}
    (n p q : ℕ) (hn : n = p + q) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1))
    (ha : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a)
    (hz : ∀ i, Open.AntiholomorphicContraction.Dolbeault.openAntiContraction U n (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector i) a = 0) : a = 0 := by
  subst n
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  apply AntiholomorphicContractionVanishing.Dolbeault.pureCovector_eq_zero_of_antiContractions p q (a x) (ha x)
  apply antiContraction_zero_of_coordinates
  intro i
  have h := congrArg (fun b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (p + q) => b x) (hz i)
  simpa only [Open.AntiholomorphicContraction.Dolbeault.openAntiContraction_apply, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.zero_apply] using h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.ContractionVanishing.Dolbeault
