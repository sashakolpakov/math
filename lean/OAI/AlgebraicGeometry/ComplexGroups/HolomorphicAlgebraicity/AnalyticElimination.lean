import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialFibers
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ResultantElimination

/-! # Analytic Elimination -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticElimination.Constructions.Elimination

noncomputable section

/-!
# Analytic equations after eliminating a finite fiber coordinate

Fixed-size Sylvester determinants are holomorphic functions of polynomial
coefficients. Finite resultant tests therefore turn the common-root locus
into an actual local holomorphic zero set.
-/

open Set Filter _root_.Metric _root_.Complex _root_.Polynomial
open scoped _root_.Topology BigOperators

theorem differentiableOn_finset_product
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset ι) {f : ι → E → ℂ} {U : Set E}
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) :
    DifferentiableOn ℂ (fun y => ∏ i ∈ s, f i y) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (differentiableOn_const (c := (1 : ℂ)) (s := U))
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).fun_mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem differentiableOn_resultant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P Q : E → Polynomial ℂ} {U : Set E}
    (hP : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U)
    (hQ : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (Q y).coeff k) U) (m n : ℕ) :
    DifferentiableOn ℂ (fun y => (P y).resultant (Q y) m n) U := by
  classical
  have hm (i j : Fin (m + n)) :
      DifferentiableOn ℂ (fun y => (P y).sylvester (Q y) m n i j) U := by
    induction j using Fin.addCases with
    | left j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hQ _
      · exact differentiableOn_const _
    | right j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hP _
      · exact differentiableOn_const _
  simp only [resultant, Matrix.det_apply']
  apply DifferentiableOn.fun_sum
  intro σ _
  exact (differentiableOn_finset_product Finset.univ (fun i _ => hm (σ i) i)).const_mul _

theorem differentiableOn_combination_coeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m : ℕ} {Q : Fin m → E → Polynomial ℂ} {U : Set E}
    (hQ : ∀ i k, DifferentiableOn ℂ (fun y => (Q i y).coeff k) U) (t : ℂ) (k : ℕ) :
    DifferentiableOn ℂ (fun y => (ResultantElimination.Constructions.Elimination.combination (fun i => Q i y) t).coeff k) U := by
  simp only [ResultantElimination.Constructions.Elimination.combination, finsetSum_coeff, coeff_smul, smul_eq_mul]
  exact DifferentiableOn.fun_sum (fun i _ => (hQ i k).const_mul _)

theorem holomorphicZeroSetAt_common_roots
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m d : ℕ} {Q : Fin (m + 1) → E → Polynomial ℂ} {U : Set E}
    (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (hcoeff : ∀ i k, DifferentiableOn ℂ (fun y => (Q i y).coeff k) U)
    (hdegree : ∀ i y, y ∈ U → (Q i y).natDegree ≤ d)
    (hmonic : ∀ y ∈ U, (Q 0 y).Monic ∧ (Q 0 y).natDegree = d) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt {y | ∃ z, ∀ i, (Q i y).eval z = 0} x := by
  let f : Fin (d * (m + 1) + 1) → E → ℂ := fun k y =>
    (Q 0 y).resultant (ResultantElimination.Constructions.Elimination.combination (fun i => Q i y) (k.val : ℂ)) d d
  refine ⟨U, hU, hx, d * (m + 1) + 1, f, ?_, ?_⟩
  · intro k
    exact differentiableOn_resultant (hcoeff 0)
      (differentiableOn_combination_coeff hcoeff (k.val : ℂ)) d d
  · intro y hy
    have h := ResultantElimination.Constructions.Elimination.common_root_iff_resultant_tests (Q 0 y) (hmonic y hy).1 (hmonic y hy).2
      (fun i => Q i y) (fun i => hdegree i y hy)
    change (∃ z, ∀ i, (Q i y).eval z = 0) ↔ _
    exact (show (∃ z, ∀ i, (Q i y).eval z = 0) ↔
      (∃ z, (Q 0 y).eval z = 0 ∧ ∀ i, (Q i y).eval z = 0) from
      ⟨fun ⟨z, hz⟩ => ⟨z, hz 0, hz⟩, fun ⟨z, _, hz⟩ => ⟨z, hz⟩⟩).trans h

/-- Near a point of a finite analytic fiber, projection of a sufficiently
small closed disk is cut out by finitely many holomorphic equations. -/
theorem holomorphic_local_projection {n : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)} {x : Fin n → ℂ} {c : ℂ}
    (hlocal : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S (x, c))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite) :
    ∃ R : ℝ, 0 < R ∧
      ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt {y | ∃ z ∈ closedBall c R, (y, z) ∈ S} x := by
  obtain ⟨R, d, m, U, Q, hR, hU, hx, hcoeff, hdeg, hQ, heq⟩ :=
    PolynomialFibers.Constructions.Preparation.local_projection_as_common_roots hlocal hfinite
  refine ⟨R, hR, (holomorphicZeroSetAt_common_roots hU hx hcoeff hdeg hQ).congr ?_⟩
  filter_upwards [hU.mem_nhds hx] with y hy
  exact heq y hy

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticElimination.Constructions.Elimination
