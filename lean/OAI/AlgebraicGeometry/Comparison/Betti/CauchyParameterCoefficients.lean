import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ContourDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Cauchy Parameter Coefficients -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CauchyParameterCoefficients.Dolbeault

noncomputable section

/-! Smooth dependence and the actual parameter derivative of the
coefficients of the original Cauchy power series. -/

open Set _root_.Metric _root_.Complex
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def cauchyParameterCoefficient (g : P × ℂ → F) (c : ℂ) (r : ℝ) (n : ℕ) (p : P) : F :=
  (2 * Real.pi * I : ℂ)⁻¹ •
    circleIntegral (fun z => (z - c)⁻¹ ^ n • (z - c)⁻¹ • g (p, z)) c r

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem cauchyPowerSeries_eq_parameterCoefficient (g : P × ℂ → F)
    (c : ℂ) (r : ℝ) (n : ℕ) (p : P) (w : ℂ) :
    cauchyPowerSeries (fun z => g (p, z)) c r n (fun _ => w) =
      w ^ n • cauchyParameterCoefficient g c r n p := by
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
    Fin.prod_const, cauchyParameterCoefficient]

variable [FiniteDimensional ℝ P]

theorem cauchyParameterCoefficient_smooth {g : P × ℂ → F} {W : Set (P × ℂ)}
    (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g W) {S : Set P} (hS : IsOpen S)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hSW : S ×ˢ sphere c r ⊆ W) (n : ℕ) :
    ContDiffOn ℝ ∞ (cauchyParameterCoefficient g c r n) S := by
  let V : Set (P × ℂ) := W ∩ {q | q.2 - c ≠ 0}
  have hV : IsOpen V := hW.inter (isOpen_ne_fun (continuous_snd.sub continuous_const) continuous_const)
  have hi : ContDiffOn ℝ ∞ (fun q : P × ℂ => (q.2 - c)⁻¹) V :=
    (contDiffOn_snd.sub contDiffOn_const).inv (fun q hq => hq.2)
  have hG : ContDiffOn ℝ ∞ (fun q : P × ℂ =>
      (q.2 - c)⁻¹ ^ n • (q.2 - c)⁻¹ • g q) V :=
    (hi.pow n).smul (hi.smul (hg.mono inter_subset_left))
  have hSV : S ×ˢ sphere c r ⊆ V := by
    intro q hq
    refine ⟨hSW hq, ?_⟩
    intro he
    have hqc := sub_eq_zero.mp he
    have hz := hq.2
    rw [hqc, mem_sphere, dist_self] at hz
    exact (ne_of_gt hr) hz.symm
  exact (Smooth.ContourDerivative.Dolbeault.contDiffOn_circleIntegral_smooth hV hG hS hr.le hSV).const_smul _

theorem hasFDerivAt_cauchyParameterCoefficient {g : P × ℂ → F} {W : Set (P × ℂ)}
    (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g W) {S : Set P} (hS : IsOpen S)
    {p : P} (hp : p ∈ S) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hSW : S ×ˢ sphere c r ⊆ W) (n : ℕ) :
    HasFDerivAt (cauchyParameterCoefficient g c r n)
      (cauchyParameterCoefficient (Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g) c r n p) p := by
  have hi : ContinuousOn (fun q : P × ℂ => (q.2 - c)⁻¹) (S ×ˢ sphere c r) := by
    apply (continuousOn_snd.sub continuousOn_const).inv₀
    intro q hq he
    have hz := hq.2
    rw [sub_eq_zero.mp he, mem_sphere, dist_self] at hz
    exact (ne_of_gt hr) hz.symm
  have hG := (hi.pow n).smul (hi.smul (hg.continuousOn.mono hSW))
  have hG' := (hi.pow n).smul
    (hi.smul ((Smooth.ContourDerivative.Dolbeault.circleParameterDerivative_smooth hW hg).continuousOn.mono hSW))
  have hD : HasFDerivAt
      (fun q => circleIntegral (fun z => (z - c)⁻¹ ^ n • (z - c)⁻¹ • g (q, z)) c r)
      (circleIntegral (fun z =>
        (z - c)⁻¹ ^ n • (z - c)⁻¹ • Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g (p, z)) c r) p := by
    apply Smooth.ParameterCircleIntegral.Dolbeault.hasFDerivAt_parameter_circleIntegral
      (g := fun q z => (z - c)⁻¹ ^ n • (z - c)⁻¹ • g (q, z))
      (g' := fun q z => (z - c)⁻¹ ^ n • (z - c)⁻¹ • Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g (q, z))
      hS hp hr.le hG hG'
    intro q hq z hz
    have hqz : (q, z) ∈ W := hSW ⟨hq, hz⟩
    have hd : HasFDerivAt (fun x => g (x, z)) (Smooth.ContourDerivative.Dolbeault.circleParameterDerivative g (q, z)) q :=
      ((hg.contDiffAt (hW.mem_nhds hqz)).differentiableAt (by simp)).hasFDerivAt.comp q
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) q z)
    exact (hd.const_smul (z - c)⁻¹).const_smul ((z - c)⁻¹ ^ n)
  exact hD.const_smul (2 * Real.pi * I : ℂ)⁻¹

end

end OAI.AlgebraicGeometry.Comparison.Betti.CauchyParameterCoefficients.Dolbeault
