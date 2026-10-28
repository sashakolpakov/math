import OAI.Analysis.HodgeTheory.Decomposition.CovectorConnection
import OAI.Analysis.DifferentialForms.Manifold.DolbeaultCoefficientType

/-! # Covector Connection Types -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CovectorConnectionTypes.Constructions

noncomputable section

/-! The induced covector connection preserves actual pure bidegrees when
its tangent coefficient preserves the complex structure. -/

open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem realLinearMap_complex_smul_of_I (A : E →L[ℝ] E)
    (hA : ∀ v, A (Complex.I • v) = Complex.I • A v) (z : ℂ) (v : E) : A (z • v) = z • A v := by
  have hreal (r : ℝ) (w : E) : (r : ℂ) • w = r • w := algebraMap_smul ℂ r w
  rw [← Complex.re_add_im z]
  simp only [add_smul, mul_smul, hreal, map_add, ContinuousLinearMap.map_smul, hA]

theorem covectorInfinitesimalAction_pure (p q : ℕ) (A : E →L[ℝ] E)
    (hA : ∀ v, A (Complex.I • v) = Complex.I • A v)
    (a : DifferentialForms.Manifold.Basic.FormValue E (p + q)) (ha : DifferentialForms.Manifold.Bidegree.HasBidegree E p q a) :
    DifferentialForms.Manifold.Bidegree.HasBidegree E p q (CovectorConnection.Constructions.covectorInfinitesimalAction (p + q) A a) := by
  intro z v
  rw [CovectorConnection.Constructions.covectorInfinitesimalAction_apply, CovectorConnection.Constructions.covectorInfinitesimalAction_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have htuple : Function.update (fun j => (z : ℂ) • v j) i (A ((z : ℂ) • v i)) =
      (fun j => (z : ℂ) • Function.update v i (A (v i)) j) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, realLinearMap_complex_smul_of_I A hA]
    · simp only [Function.update_of_ne hj]
  rw [htuple]
  exact ha z _

theorem covectorConnectionDerivative_pure (p q : ℕ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (p + q)) (x : E) (ha : DifferentiableAt ℝ a x)
    (hpure : ∀ᶠ y in 𝓝 x, DifferentialForms.Manifold.Bidegree.HasBidegree E p q (a y))
    (hΓ : ∀ u v, Γ x u (Complex.I • v) = Complex.I • Γ x u v) (u : E) :
    DifferentialForms.Manifold.Bidegree.HasBidegree E p q (CovectorConnection.Constructions.covectorConnectionDerivative (p + q) Γ a x u) := by
  rw [CovectorConnection.Constructions.covectorConnectionDerivative_apply]
  exact (DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E p q).sub_mem (DifferentialForms.Manifold.DolbeaultCoefficientType.fderiv_hasBidegree ha hpure u)
    (covectorInfinitesimalAction_pure p q (Γ x u) (hΓ u) (a x) hpure.self_of_nhds)

end

end OAI.Analysis.HodgeTheory.Decomposition.CovectorConnectionTypes.Constructions
