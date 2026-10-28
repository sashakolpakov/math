import OAI.Analysis.PDE.Green.Physical.Change
import OAI.Analysis.PDE.Green.ParametricSet

/-! Smoothness of the ordinary real-volume Jacobian on the nonsingular
physical parameter domain. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open OAI.Analysis.Calculus.Current
open scoped ContDiff Matrix.Norms.Elementwise

theorem contDiff_continuousLinearMap_det (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (k : ℕ∞ω) :
    ContDiff ℝ k (fun L : E →L[ℝ] E => L.det) := by
  classical
  let b := Module.finBasis ℝ E
  let T : (E →L[ℝ] E) →L[ℝ]
      Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    ((LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap
  have he (L : E →L[ℝ] E) : L.det = (T L).det := by
    exact (LinearMap.det_toMatrix b L.toLinearMap).symm
  simp_rw [he, Matrix.det_apply]
  apply ContDiff.sum
  intro σ _
  simp only [Units.smul_def, zsmul_eq_mul]
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact (contDiff_apply_apply ℝ ℝ (σ i) i).comp T.contDiff

theorem contDiffAt_physicalInverseJacobian {d : ℕ} (a : ℝ) (τ : ℂ)
    (u : Option (Fin d) → ℂ) (hD : OAI.Analysis.Calculus.Current.fiberDenominator (fun i => u (some i)) ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℂ × (Option (Fin d) → ℂ) =>
      OAI.Analysis.Calculus.Current.physicalInverseJacobian a p.1 p.2) (τ, u) := by
  let E := Option (Fin d) → ℂ
  let P := ℂ × E
  have hj := (OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse_joint a τ u hD).restrict_scalars ℝ
  have hf : ContDiffAt ℝ ⊤
      (Function.uncurry (fun (p : P) (v : E) => OAI.Analysis.Calculus.Current.physicalFiberInverse a p.1 v)) ((τ, u), u) := by
    have hg : ContDiffAt ℝ ⊤ (fun v : P × E => (v.1.1, v.2)) ((τ, u), u) := by
      dsimp only [P, E]
      fun_prop
    simpa only [Function.comp_def, Function.uncurry] using! hj.comp ((τ, u), u) hg
  have hp : ContDiffAt ℝ ∞
      (fun p : P => fderiv ℝ (OAI.Analysis.Calculus.Current.physicalFiberInverse a p.1) p.2) (τ, u) :=
    hf.fderiv contDiffAt_snd (by simp)
  exact (contDiff_continuousLinearMap_det E ∞).contDiffAt.comp (τ, u) hp

theorem contDiffAt_abs_physicalInverseJacobian {d : ℕ} (a : ℝ) (τ : ℂ)
    (u : Option (Fin d) → ℂ) (ha : a ≠ 0)
    (hN : Real.sqrt 2 • τ + a • u none ≠ 0)
    (hD : OAI.Analysis.Calculus.Current.fiberDenominator (fun i => u (some i)) ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℂ × (Option (Fin d) → ℂ) =>
      |OAI.Analysis.Calculus.Current.physicalInverseJacobian a p.1 p.2|) (τ, u) := by
  exact (contDiffAt_physicalInverseJacobian a τ u hD).abs
    (OAI.Analysis.Calculus.Current.physicalInverseJacobian_ne_zero a τ u ha hN hD)

end OAI.Analysis.PDE.Green
