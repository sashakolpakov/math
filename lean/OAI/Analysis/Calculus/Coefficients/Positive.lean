import OAI.Analysis.Calculus.Coefficients.Cofactor
import OAI.Analysis.Calculus.Coefficients.Lattice

open Set Filter Module Metric InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

theorem compact_positive_cofactor_lower {n : ℕ} (hn : 1 ≤ n)
    {K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} (hK : IsCompact K)
    (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (hf : ContDiff ℝ 3 f)
    (hpos : ∀ x ∈ K, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ K, ∀ v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4,
      lam*‖v‖^2 ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x) v) := by
  by_cases hne : K.Nonempty
  · have hA : Continuous (fun x ↦ OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)) :=
      (OAI.Analysis.PDE.Dirichlet.contDiff_detRealOperator n 1).continuous.comp (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots hf).continuous
    apply OAI.Analysis.PDE.Dirichlet.uniform_positive_quadratic_lower hK hne (OAI.Analysis.PDE.Dirichlet.fourSlot_unitSphere_nonempty hn)
      (fun x v ↦ inner ℝ v (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x) v))
    · exact (continuous_snd.inner ((hA.comp continuous_fst).clm_apply continuous_snd)).continuousOn
    · intro x hx v hv
      rw [OAI.Analysis.PDE.Dirichlet.detRealOperator_symbol_eq_log _ (hpos x hx)]
      exact mul_pos (OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef _ (hpos x hx))
        (OAI.Analysis.PDE.Dirichlet.logPrincipalSymbol_pos _ (hpos x hx) v hv)
    · intro x hx t v
      simp only [map_smul,inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial]
      ring
  · exact ⟨1,zero_lt_one,fun x hx ↦ (hne ⟨x,hx⟩).elim⟩

end OAI.Analysis.Calculus.Coefficients
