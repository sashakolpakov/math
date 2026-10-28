import OAI.Analysis.Fourier.WavePackets.PeriodicDirichlet
import OAI.Analysis.PDE.Dirichlet.Closed.Admissible

noncomputable section

namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped ContDiff ComplexOrder

variable {m s : ℕ} {slots : Fin s → Quaternion ℝ}
  {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : PeriodicQuaternionicData slots e b}

/-- The literal equation of a periodic quaternionic solution extends to
the closed fiber. This includes both the three- and four-slot equations. -/
theorem PeriodicQuaternionicSolution.equation_closed
    (S : PeriodicQuaternionicSolution D) :
    ∀ x, D.defining x ≤ 0 →
      OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (fun y => D.background y + S.u y) x) =
        D.density x := by
  apply OAI.Analysis.PDE.Dirichlet.equality_on_regular_sublevel_of_interior
    (D.defining_smooth.of_le (by simp)) D.regular
    (OAI.Analysis.PDE.Dirichlet.continuous_mooreHessian slots ((D.background_smooth.add S.smooth).of_le (by simp)))
    D.density_smooth.continuous
  intro x hx
  exact S.equation x (OAI.Analysis.PDE.Dirichlet.neg_of_mem_interior_regular_sublevel D.regular hx)

/-- Interior positive definiteness has a semidefinite boundary limit;
the positive prescribed determinant rules out degeneracy there. -/
theorem PeriodicQuaternionicSolution.admissible_closed
    (S : PeriodicQuaternionicSolution D) :
    ∀ x, D.defining x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (fun y => D.background y + S.u y) x)).PosDef := by
  have hψ : ContDiff ℝ 2 (fun y => D.background y + S.u y) :=
    (D.background_smooth.add S.smooth).of_le (by simp)
  have hsem (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s) (hx : D.defining x ≤ 0) :
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (fun y => D.background y + S.u y) x)).PosSemidef := by
    apply (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian slots hψ.contDiffAt)).mpr
    intro z
    have hc : Continuous (fun y =>
        (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (fun y => D.background y + S.u y) y) z).re) :=
      OAI.Analysis.PDE.Dirichlet.continuous_quaternionForm_re (OAI.Analysis.PDE.Dirichlet.continuous_quaternionHessian slots hψ) continuous_const
    have hs : interior {y | D.defining y ≤ 0} ⊆
        {y | 0 ≤ (OAI.Analysis.PDE.Dirichlet.quaternionForm
          (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots (fun y => D.background y + S.u y) y) z).re} := by
      intro y hy
      exact (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian slots hψ.contDiffAt)).mp
        (S.admissible y (OAI.Analysis.PDE.Dirichlet.neg_of_mem_interior_regular_sublevel D.regular hy)).posSemidef z
    exact closure_minimal hs (isClosed_le continuous_const hc)
      (OAI.Analysis.PDE.Dirichlet.sublevel_subset_closure_interior (D.defining_smooth.of_le (by simp)) D.regular hx)
  intro x hx
  apply OAI.Analysis.PDE.Dirichlet.complexify_posDef_of_posSemidef_mooreDet_pos _ (hsem x hx)
  rw [S.equation_closed x hx]
  exact D.density_positive x hx

end OAI.Analysis.Fourier.WavePackets
