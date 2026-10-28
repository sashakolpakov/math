import OAI.Analysis.PDE.Dirichlet.Moore.Divergence
import OAI.Analysis.Normed.Function.Holder.Banach.Composition

open Set Filter InnerProductSpace
open scoped Topology Matrix Matrix.Norms.Elementwise MatrixOrder ComplexOrder ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green OAI.Analysis.Normed.Function.Holder

theorem contDiff_mooreRealMatrix (n : ℕ) (k : ℕ∞ω) :
    ContDiff ℝ k (mooreRealMatrix (n := n)) := by
  apply contDiff_pi.mpr
  intro p
  apply contDiff_pi.mpr
  intro q
  exact (OAI.Analysis.PDE.Green.realCoefficientCLM OAI.Analysis.Calculus.Quaternion.fourSlots p q).contDiff.comp (OAI.LinearAlgebra.Moore.contDiff_mooreCofactor n k)

theorem mooreRealMatrix_dotProduct {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (v : CoordinateSpace n 4) :
    star (v : Fin n × Fin 4 → ℝ) ⬝ᵥ (mooreRealMatrix A *ᵥ (v : Fin n × Fin 4 → ℝ)) =
      inner ℝ v (detRealOperator A v) := by
  rw [← mooreRealMatrix_quadratic]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem mooreRealMatrix_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) : (mooreRealMatrix A).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.ext
    intro p q
    change mooreRealMatrix A q p = mooreRealMatrix A p q
    exact congrFun (congrFun (mooreRealMatrix_isSymm A) p) q
  · intro x hx
    let v : CoordinateSpace n 4 := WithLp.toLp 2 x
    have hv : v ≠ 0 := by
      intro hv0
      apply hx
      funext p
      exact congrArg (fun w : CoordinateSpace n 4 ↦ w p) hv0
    change 0 < star (v : Fin n × Fin 4 → ℝ) ⬝ᵥ
      (mooreRealMatrix A *ᵥ (v : Fin n × Fin 4 → ℝ))
    rw [mooreRealMatrix_dotProduct, detRealOperator_symbol_eq_log A hA]
    exact mul_pos (OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef A hA)
      (logPrincipalSymbol_pos A hA v hv)

/-- The conservation law is local, so no global extension regularity is
required of a Dirichlet solution. -/
theorem mooreRealMatrix_divergence_at {n : ℕ} {ψ : CoordinateSpace n 4 → ℝ}
    {x : CoordinateSpace n 4} (hψ : ContDiffAt ℝ 3 ψ x) (q : Fin n × Fin 4) :
    (∑ p, fderiv ℝ (fun y ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) p q)
      x (coordinateVector p)) = 0 := by
  obtain ⟨g, hg, heq⟩ := exists_contDiff_extension_near_point hψ
  have hh : quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g =ᶠ[𝓝 x] quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ := by
    filter_upwards [heq.eventuallyEq_nhds] with y hy
    exact quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hy
  have hder (p : Fin n × Fin 4) :
      fderiv ℝ (fun y ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y) p q) x =
      fderiv ℝ (fun y ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) p q) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hh] with y hy
    rw [hy]
  simp_rw [← hder]
  exact mooreRealMatrix_divergence hg x q

/-- The concrete symmetric matrix used by the variational problem is a
bounded Hölder coefficient field on every bounded C²,α set of potentials. -/
theorem exists_mooreRealMatrix_holder_bound {n : ℕ}
    {Ω K : Set (CoordinateSpace n 4)} {hΩK : Ω ⊆ K} {α : ℝ}
    (hα : 0 ≤ α) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α, ‖f‖ ≤ R →
      ∃ a : OAI.Analysis.Normed.Function.Holder.HolderMap K (Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α,
        (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value a x =
          mooreRealMatrix (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots f) x)) ∧
        ‖a‖ ≤ C := by
  let J := quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots
  obtain ⟨C, hC, hcompose⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_compose_contDiff_bound
    (X := K) (contDiff_mooreRealMatrix n 1) hα (mul_nonneg (norm_nonneg J) hR)
  refine ⟨C * (1 + ‖J‖ * R), mul_nonneg hC (by positivity), ?_⟩
  intro f hf
  have hJ : ‖J f‖ ≤ ‖J‖ * R := (J.le_opNorm f).trans
    (mul_le_mul_of_nonneg_left hf (norm_nonneg J))
  obtain ⟨a, ha, hnorm⟩ := hcompose (J f) hJ
  refine ⟨a, ha, hnorm.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (by linarith) hC

end OAI.Analysis.PDE.Dirichlet
