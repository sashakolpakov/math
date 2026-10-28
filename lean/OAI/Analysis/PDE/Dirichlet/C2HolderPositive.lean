import OAI.Analysis.PDE.Dirichlet.C2HolderNonlinear
import OAI.LinearAlgebra.Moore.Positive

open Set
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

/-- At positive quaternionic Hessians the genuine Banach derivative is the
determinant times the inverse-trace linearized elliptic operator. -/
theorem fderiv_mooreDirichletOperator_positive {m s : ℕ}
    {Ω K : Set (CoordinateSpace m s)} {hΩK : Ω ⊆ K} {α : ℝ}
    (hΩ : IsOpen Ω) (hα : 0 ≤ α) (e : Fin s → Q)
    (f w : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    {x : CoordinateSpace m s} (hx : x ∈ Ω)
    (hpos : (OAI.LinearAlgebra.Moore.complexify
      (quaternionHessian e (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value f)) x)).PosDef) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (fderiv ℝ (mooreDirichletOperator hα e) f w) ⟨x, hΩK hx⟩ =
      OAI.LinearAlgebra.Moore.mooreDet m (quaternionHessian e (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value f)) x) *
        (((OAI.LinearAlgebra.Moore.complexify (quaternionHessian e (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value f)) x))⁻¹ *
          OAI.LinearAlgebra.Moore.complexify (quaternionHessian e (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value w)) x)).trace.re / 2) := by
  rw [fderiv_mooreDirichletOperator_value hΩ hα e f w hx]
  apply OAI.LinearAlgebra.Moore.mooreDifferential_eq_complex_inverse _ _ hpos
  exact quaternionHessian_isHermitian e
    ((OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ w).contDiffAt (hΩ.mem_nhds hx))

end OAI.Analysis.PDE.Dirichlet
