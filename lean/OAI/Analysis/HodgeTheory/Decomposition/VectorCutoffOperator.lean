import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Vector Cutoff Operator -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions

noncomputable section

/-! Smooth cutoff multiplication is a bounded operator on every natural-order
Sobolev space, proved using its genuine closed graph in distributions. -/

open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def vectorSobolevDistributionCLM (s : ℝ) : Lp F 2 (volume : Measure E) →L[ℂ] 𝓢'(E, F) :=
  (besselPotential E F (-s)).comp (Lp.toTemperedDistributionCLM F (volume : Measure E) 2)

theorem vectorSobolevDistributionCLM_injective (s : ℝ) :
    Function.Injective (vectorSobolevDistributionCLM (E := E) (F := F) s) := by
  intro u v h
  apply AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateMap_injective E F s
  exact Subtype.ext h

def vectorSobolevCutoffLinear (n : ℕ) (g : 𝓢(E, ℂ)) :
    Lp F 2 (volume : Measure E) →ₗ[ℂ] Lp F 2 (volume : Measure E) :=
  (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateEquiv E F (n : ℝ)).symm.toLinearMap.comp
    (((smulLeftCLM F g).toLinearMap.comp (vectorSobolevDistributionCLM (n : ℝ)).toLinearMap).codRestrict
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevDistributionSubmodule E F (n : ℝ)) (fun u =>
        AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.memSobolev_nat_schwartz_cutoff n g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateMap E F (n : ℝ) u).property))

theorem vectorSobolevCutoffLinear_distribution (n : ℕ) (g : 𝓢(E, ℂ)) (u : Lp F 2 (volume : Measure E)) :
    vectorSobolevDistributionCLM (n : ℝ) (vectorSobolevCutoffLinear n g u) =
      smulLeftCLM F g (vectorSobolevDistributionCLM (n : ℝ) u) := by
  have h := (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateEquiv E F (n : ℝ)).apply_symm_apply
    ⟨smulLeftCLM F g (vectorSobolevDistributionCLM (n : ℝ) u),
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.memSobolev_nat_schwartz_cutoff n g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateMap E F (n : ℝ) u).property⟩
  exact congrArg Subtype.val h

theorem vectorSobolevCutoffLinear_closed_graph (n : ℕ) (g : 𝓢(E, ℂ)) :
    IsClosed ((vectorSobolevCutoffLinear (F := F) n g).graph :
      Set (Lp F 2 (volume : Measure E) × Lp F 2 (volume : Measure E))) := by
  let J := vectorSobolevDistributionCLM (E := E) (F := F) (n : ℝ)
  have heq : ((vectorSobolevCutoffLinear (F := F) n g).graph :
      Set (Lp F 2 (volume : Measure E) × Lp F 2 (volume : Measure E))) =
      {p | J p.2 = smulLeftCLM F g (J p.1)} := by
    ext p
    change p.2 = vectorSobolevCutoffLinear n g p.1 ↔ J p.2 = smulLeftCLM F g (J p.1)
    constructor
    · intro h
      rw [h]
      exact vectorSobolevCutoffLinear_distribution n g p.1
    · intro h
      symm
      apply vectorSobolevDistributionCLM_injective (n : ℝ)
      exact (vectorSobolevCutoffLinear_distribution n g p.1).trans h.symm
  rw [heq]
  exact isClosed_eq (J.continuous.comp continuous_snd)
    ((smulLeftCLM F g).continuous.comp (J.continuous.comp continuous_fst))

def vectorSobolevCutoffCLM (n : ℕ) (g : 𝓢(E, ℂ)) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  ContinuousLinearMap.ofIsClosedGraph (vectorSobolevCutoffLinear_closed_graph n g)

theorem vectorSobolevCutoffCLM_distribution (n : ℕ) (g : 𝓢(E, ℂ)) (u : Lp F 2 (volume : Measure E)) :
    vectorSobolevDistributionCLM (n : ℝ) (vectorSobolevCutoffCLM n g u) =
      smulLeftCLM F g (vectorSobolevDistributionCLM (n : ℝ) u) :=
  vectorSobolevCutoffLinear_distribution n g u

theorem vectorSobolevCutoffCLM_norm_le (n : ℕ) (g : 𝓢(E, ℂ)) (u : Lp F 2 (volume : Measure E)) :
    ‖vectorSobolevCutoffCLM n g u‖ ≤ ‖vectorSobolevCutoffCLM (F := F) n g‖ * ‖u‖ :=
  (vectorSobolevCutoffCLM n g).le_opNorm u

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions
