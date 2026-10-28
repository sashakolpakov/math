import OAI.Analysis.PDE.Dirichlet.Periodic.Linearized
import OAI.Analysis.PDE.Dirichlet.Periodic.Data
import OAI.Analysis.PDE.Dirichlet.Moore.Divergence
import OAI.Analysis.PDE.Dirichlet.Continuity

open Set Filter Module
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem abs_matrix_pairing_le {I : Type*} [Fintype I]
    (A R : Matrix I I ℝ) :
    |∑ i, ∑ j, A i j * R i j| ≤ (Fintype.card I : ℝ)^2 * ‖A‖ * ‖R‖ := by
  classical
  calc
    _ ≤ ∑ i, ∑ j, |A i j * R i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : I, ∑ _j : I, ‖A‖ * ‖R‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul
        ((norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i))
        ((norm_le_pi_norm (R i) j).trans (norm_le_pi_norm R i))
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem abs_mooreLinearization_sub_le {n : ℕ}
    (A B : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    {r : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 2 r) (x : CoordinateSpace n 4) :
    |mooreLinearization A r x - mooreLinearization B r x| ≤
      (Fintype.card (Fin n × Fin 4) : ℝ)^2 *
        ‖mooreRealMatrix (A x) - mooreRealMatrix (B x)‖ * ‖realHessian r x‖ := by
  rw [← mooreRealMatrix_linearization_at A hr.contDiffAt,
    ← mooreRealMatrix_linearization_at B hr.contDiffAt]
  change |(∑ p, ∑ q, mooreRealMatrix (A x) p q * realHessian r x p q) -
    (∑ p, ∑ q, mooreRealMatrix (B x) p q * realHessian r x p q)| ≤ _
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← sub_mul]
  exact abs_matrix_pairing_le _ _

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Positivity of both genuine quaternionic Hessians supplies a uniform
positive defining-function barrier on the full periodic closed domain. -/
theorem periodic_moore_defining_positive_lower
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r ψ : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hψ : ContDiff ℝ 2 ψ) (hψp : LatticePeriodic e lat ψ)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, r x ≤ 0 →
      c ≤ mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) r x := by
  by_cases hne : ({x | r x ≤ 0} : Set (CoordinateSpace n 4)).Nonempty
  · have hp : Continuous (fun x : CoordinateSpace n 4 ↦
        (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x, quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)) :=
      (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hψ).prodMk
        (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hr)
    have hc : Continuous (mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) r) :=
      (OAI.LinearAlgebra.Moore.continuous_mooreDifferential n).comp
        (f := fun x : CoordinateSpace n 4 ↦
          (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x, quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)) hp
    apply exists_lattice_positive_lower e lat hK hr.continuous hrp hbounded hne hc.continuousOn
    · intro x l
      unfold mooreLinearization
      rw [(hψp.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots) x l, (hrp.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots) x l]
    · intro x hx
      apply OAI.LinearAlgebra.Moore.mooreDifferential_pos_of_posDef _ _ (hψpos x hx) (hrpos x hx).posSemidef
      intro hz
      let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      have hh := (hrpos x hx).det_pos
      simp only [hz, OAI.LinearAlgebra.Moore.complexify_zero, Matrix.det_zero, lt_self_iff_false] at hh
  · exact ⟨1, zero_lt_one, fun x hx ↦ (hne ⟨x, hx⟩).elim⟩

/-- Uniform convergence of the actual cofactor matrices preserves half the
strict defining-function barrier after removing finitely many terms. -/
theorem eventually_periodic_moore_defining_lower
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r ψ : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hψ : ContDiff ℝ 2 ψ) (hψp : LatticePeriodic e lat ψ)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hψpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (u : ℕ → CoordinateSpace n 4 → ℝ)
    (hc : TendstoUniformlyOn (fun j x ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))
      (fun x ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)) atTop {x | r x ≤ 0}) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ j, N ≤ j → ∀ x, r x ≤ 0 →
      c ≤ mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j)) r x := by
  obtain ⟨c, hcpos, hcmin⟩ := periodic_moore_defining_positive_lower hn e lat hK
    hr hrp hbounded hψ hψp hrpos hψpos
  have hRp : LatticePeriodic e lat (realHessian r) := by
    intro x l
    unfold realHessian
    rw [hrp.fderiv.fderiv x l]
  obtain ⟨M, hM, hRM⟩ := exists_lattice_norm_bound e lat hK hr.continuous hrp hbounded
    (continuous_realHessian hr).continuousOn hRp
  let D : ℝ := (Fintype.card (Fin n × Fin 4) : ℝ)^2 * M + 1
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (Metric.tendstoUniformlyOn_iff.mp hc (c / (2 * D)) (by positivity))
  refine ⟨c/2, by positivity, N, ?_⟩
  intro j hj x hx
  have he : ‖mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x) -
      mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)‖ < c / (2 * D) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hN j hj x hx
  have hb := abs_mooreLinearization_sub_le (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j))
    (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) hr x
  have hbound : |mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j)) r x -
      mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) r x| ≤ c/2 := by
    calc
      _ ≤ (Fintype.card (Fin n × Fin 4) : ℝ)^2 *
          ‖mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x) -
            mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)‖ * M :=
        hb.trans (mul_le_mul_of_nonneg_left (hRM x hx) (by positivity))
      _ ≤ D * ‖mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x) -
            mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)‖ := by
        dsimp [D]
        nlinarith [norm_nonneg (mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x) -
          mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x))]
      _ ≤ D * (c / (2 * D)) := mul_le_mul_of_nonneg_left he.le hD.le
      _ = c/2 := by field_simp
  have hbase := hcmin x hx
  have habs := (abs_le.mp hbound).1
  linarith

end OAI.Analysis.PDE.Dirichlet
