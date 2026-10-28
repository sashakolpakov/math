import OAI.Geometry.ComplexBall.Generation
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-! # Active Generation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveGeneration.Approximation

noncomputable section

/-! Two binary subgroups through the third coordinate generate SL₃.
Consequently approximation of their four root groups while the away
coordinate tends to one suffices for density in the actual product. -/

open scoped Classical _root_.Matrix
open _root_.Matrix.SpecialLinearGroup OAI.Geometry.ComplexBall.Generation.ArithmeticQuotient

variable {K : Type*} [Field K]

theorem transvection_through_last {i j : Fin 3} (hij : i ≠ j)
    (hi : i ≠ 2) (hj : j ≠ 2) (a : K) :
    transvection hij a = transvection hi a * transvection hj.symm 1 *
      transvection hi (-a) * transvection hj.symm (-1) := by
  fin_cases i <;> fin_cases j <;> first | contradiction | skip
  all_goals
    apply Subtype.ext
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [transvection_coe, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

theorem subgroup_eq_top_of_active_roots (H : Subgroup (Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL K))
    (hforward : ∀ (i : Fin 3) (hi : i ≠ 2) (a : K), transvection hi a ∈ H)
    (hbackward : ∀ (i : Fin 3) (hi : i ≠ 2) (a : K), transvection hi.symm a ∈ H) : H = ⊤ := by
  apply top_unique
  intro g _
  apply Geometry.ComplexBall.Generation.ArithmeticQuotient.sl3_transvection_induction (fun g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.SL K => g ∈ H) _ _ g
  · intro i j hij a
    by_cases hi : i = 2
    · subst i
      exact hbackward j hij.symm a
    by_cases hj : j = 2
    · subst j
      exact hforward i hij a
    rw [transvection_through_last hij hi hj a]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hforward i hi a) (hbackward j hj 1))
      (hforward i hi (-a))) (hbackward j hj (-1))
  · exact fun _ _ => H.mul_mem

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ActiveGeneration.Approximation
