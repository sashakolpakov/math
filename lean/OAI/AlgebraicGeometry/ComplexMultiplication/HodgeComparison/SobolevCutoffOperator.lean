import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Sobolev Cutoff Operator -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevCutoffOperator.CM.Construction

noncomputable section

/-! Smooth cutoff multiplication is a bounded operator on every natural-order
Sobolev space, proved using its genuine closed graph in distributions. -/

open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def sobolevDistributionCLM (s : ℝ) : Lp ℂ 2 (volume : Measure E) →L[ℂ] 𝓢'(E, ℂ) :=
  (besselPotential E ℂ (-s)).comp (Lp.toTemperedDistributionCLM ℂ (volume : Measure E) 2)

theorem sobolevDistributionCLM_injective (s : ℝ) :
    Function.Injective (sobolevDistributionCLM (E := E) s) := by
  intro u v h
  apply Bounds.CM.Construction.sobolevCoordinateMap_injective E ℂ s
  exact Subtype.ext h

def sobolevCutoffLinear (n : ℕ) (g : 𝓢(E, ℂ)) :
    Lp ℂ 2 (volume : Measure E) →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (Bounds.CM.Construction.sobolevCoordinateEquiv E ℂ (n : ℝ)).symm.toLinearMap.comp
    (((smulLeftCLM ℂ g).toLinearMap.comp (sobolevDistributionCLM (n : ℝ)).toLinearMap).codRestrict
      (Bounds.CM.Construction.sobolevDistributionSubmodule E ℂ (n : ℝ)) (fun u =>
        SobolevInv.CM.Construction.memSobolev_nat_schwartz_cutoff n g (Bounds.CM.Construction.sobolevCoordinateMap E ℂ (n : ℝ) u).property))

theorem sobolevCutoffLinear_distribution (n : ℕ) (g : 𝓢(E, ℂ)) (u : Lp ℂ 2 (volume : Measure E)) :
    sobolevDistributionCLM (n : ℝ) (sobolevCutoffLinear n g u) =
      smulLeftCLM ℂ g (sobolevDistributionCLM (n : ℝ) u) := by
  have h := (Bounds.CM.Construction.sobolevCoordinateEquiv E ℂ (n : ℝ)).apply_symm_apply
    ⟨smulLeftCLM ℂ g (sobolevDistributionCLM (n : ℝ) u),
      SobolevInv.CM.Construction.memSobolev_nat_schwartz_cutoff n g (Bounds.CM.Construction.sobolevCoordinateMap E ℂ (n : ℝ) u).property⟩
  exact congrArg Subtype.val h

theorem sobolevCutoffLinear_closed_graph (n : ℕ) (g : 𝓢(E, ℂ)) :
    IsClosed ((sobolevCutoffLinear n g).graph :
      Set (Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E))) := by
  let J := sobolevDistributionCLM (E := E) (n : ℝ)
  have heq : ((sobolevCutoffLinear n g).graph :
      Set (Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E))) =
      {p | J p.2 = smulLeftCLM ℂ g (J p.1)} := by
    ext p
    change p.2 = sobolevCutoffLinear n g p.1 ↔ J p.2 = smulLeftCLM ℂ g (J p.1)
    constructor
    · intro h
      rw [h]
      exact sobolevCutoffLinear_distribution n g p.1
    · intro h
      symm
      apply sobolevDistributionCLM_injective (n : ℝ)
      exact (sobolevCutoffLinear_distribution n g p.1).trans h.symm
  rw [heq]
  exact isClosed_eq (J.continuous.comp continuous_snd)
    ((smulLeftCLM ℂ g).continuous.comp (J.continuous.comp continuous_fst))

def sobolevCutoffCLM (n : ℕ) (g : 𝓢(E, ℂ)) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  ContinuousLinearMap.ofIsClosedGraph (sobolevCutoffLinear_closed_graph n g)

theorem sobolevCutoffCLM_distribution (n : ℕ) (g : 𝓢(E, ℂ)) (u : Lp ℂ 2 (volume : Measure E)) :
    sobolevDistributionCLM (n : ℝ) (sobolevCutoffCLM n g u) =
      smulLeftCLM ℂ g (sobolevDistributionCLM (n : ℝ) u) :=
  sobolevCutoffLinear_distribution n g u

theorem sobolevCutoffCLM_norm_le (n : ℕ) (g : 𝓢(E, ℂ)) (u : Lp ℂ 2 (volume : Measure E)) :
    ‖sobolevCutoffCLM n g u‖ ≤ ‖sobolevCutoffCLM n g‖ * ‖u‖ :=
  (sobolevCutoffCLM n g).le_opNorm u

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevCutoffOperator.CM.Construction
