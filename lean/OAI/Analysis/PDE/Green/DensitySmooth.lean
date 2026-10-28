import OAI.Analysis.PDE.Green.CombinedDensity
import OAI.Analysis.PDE.Green.ParametricSet

/-! Smoothness of the actual determinant-pencil and combined current energy
densities, obtained by differentiating the compact pencil integral. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped ContDiff Matrix.Norms.Elementwise

theorem contDiff_quaternionHessian_infty {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {ψ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) :=
    (hψ.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hH : ContDiff ℝ ∞ (OAI.Analysis.PDE.Dirichlet.realHessian ψ) := by
    apply contDiff_pi.mpr
    intro p
    apply contDiff_pi.mpr
    intro q
    exact (hD.clm_apply contDiff_const).clm_apply contDiff_const
  exact (OAI.Analysis.Calculus.Quaternion.hessianCLM e).contDiff.comp hH

theorem contDiff_spatialPencilEnergyDensity {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    (hB : ContDiff ℝ ∞ B) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (spatialPencilEnergyDensity e B u) := by
  have hBH := contDiff_quaternionHessian_infty e hB
  have huH := contDiff_quaternionHessian_infty e hu
  have hmat : ContDiff ℝ ∞ (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s × ℝ =>
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e B p.1 + p.2 • OAI.Analysis.PDE.Dirichlet.quaternionHessian e u p.1) :=
    (hBH.comp contDiff_fst).add (contDiff_snd.smul (huH.comp contDiff_fst))
  have hsub : ContDiff ℝ ∞ (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s × ℝ =>
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B p.1 + p.2 • OAI.Analysis.PDE.Dirichlet.quaternionHessian e u p.1).submatrix
        Fin.succ Fin.succ) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_apply_apply ℝ (Quaternion ℝ) i.succ j.succ).comp hmat
  let f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s × ℝ → ℝ := fun p =>
    OAI.LinearAlgebra.Moore.mooreDet n ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e B p.1 + p.2 • OAI.Analysis.PDE.Dirichlet.quaternionHessian e u p.1).submatrix
      Fin.succ Fin.succ)
  have hf : ContDiff ℝ ∞ f := by
    simpa only [f] using! (OAI.LinearAlgebra.Moore.contDiff_mooreDet n ∞).comp hsub
  have hI : ContDiff ℝ ∞ (fun x => ∫ t in Ioc (0 : ℝ) 1, f (x, t)) := by
    apply contDiffOn_univ.mp
    exact contDiffOn_compact_setIntegral volume isCompact_Icc measurableSet_Ioc
      Ioc_subset_Icc_self isCompact_Icc.measure_lt_top isOpen_univ isOpen_univ
      f hf.contDiffOn (by intros; trivial)
  have he : spatialPencilEnergyDensity e B u =
      (fun x => u x * ∫ t in Ioc (0 : ℝ) 1, f (x, t)) := by
    funext x
    simp only [spatialPencilEnergyDensity, f,
      quaternionHessian_add_mul e (hB.of_le (by simp)) (hu.of_le (by simp)),
      intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [he]
  exact hu.mul hI

theorem contDiff_quaternion_real (k : ℕ∞ω) :
    ContDiff ℝ k (fun q : Quaternion ℝ => q.re) := by
  let L : Quaternion ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun q => q.re
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact L.toContinuousLinearMap.contDiff

theorem contDiff_combinedEnergyDensity {n s : ℕ} (e : Fin s → Quaternion ℝ) (lam : ℝ)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ ∞ A) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ}
    (hB : ContDiff ℝ ∞ B) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (combinedEnergyDensity e lam A B u) := by
  have hmass : ContDiff ℝ ∞ (fun x => (A x 0 0).re) :=
    (contDiff_quaternion_real ∞).comp ((contDiff_apply_apply ℝ (Quaternion ℝ) 0 0).comp hA)
  exact (hu.neg.mul hmass).add (contDiff_const.mul (contDiff_spatialPencilEnergyDensity e hB hu))

end OAI.Analysis.PDE.Green
