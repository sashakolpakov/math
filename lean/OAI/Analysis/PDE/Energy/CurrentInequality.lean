import OAI.LinearAlgebra.Moore.Schur
import OAI.Analysis.PDE.Energy.Comparison

/-! The source's pointwise current/determinant inequality for actual Hessians. -/

noncomputable section
namespace OAI.Analysis.PDE.Energy

open Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

theorem current_hessian_energy_inequality {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosSemidef) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)
    (hD : (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x).submatrix
      Fin.succ Fin.succ)).PosDef)
    {lam : ℝ} (hlam : 0 < lam)
    (hdet : OAI.LinearAlgebra.Moore.mooreDet n ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x).submatrix
      Fin.succ Fin.succ) = lam * (A 0 0).re)
    (hann : OAI.LinearAlgebra.Moore.realTrace (A * OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) = 0) :
    lam⁻¹ * OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) ≤
      OAI.LinearAlgebra.Moore.realTrace (A * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  let Q := OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x
  have hQ : Q.IsHermitian := OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e (hB.add hu).contDiffAt
  have hs := OAI.LinearAlgebra.Moore.schur_determinant_energy_inequality A hA (Q 0 0).re (fun i => Q i.succ 0)
    (Q.submatrix Fin.succ Fin.succ) hD lam hlam.le hdet
  rw [← OAI.LinearAlgebra.Moore.hermitianBlock_reconstruct Q hQ] at hs
  change OAI.LinearAlgebra.Moore.mooreDet (n + 1) Q ≤ lam * OAI.LinearAlgebra.Moore.realTrace (A * Q) at hs
  have hpair : OAI.LinearAlgebra.Moore.realTrace (A * Q) = OAI.LinearAlgebra.Moore.realTrace (A * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
    dsimp only [Q]
    rw [hessian_sum e hB hu, Matrix.mul_add, OAI.LinearAlgebra.Moore.realTrace_add, hann, zero_add]
  rw [hpair] at hs
  rw [← div_eq_inv_mul]
  exact (div_le_iff₀ hlam).mpr (by simpa only [mul_comm] using hs)

end OAI.Analysis.PDE.Energy
