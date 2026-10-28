import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ParameterHalfDet
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Slots
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.InitialTensor

/-! # Total Graph Slots -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalGraphSlots.CM

noncomputable section

/-! ThetaCycle: the actual total graph rows that project Jacobi tensors to
the distinguished ball cotangent and multiplicity factors. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

def totalGraphCoefficient (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (a : Fin 2 × Fin 2) :
    (Sum (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places) → ℂ) →ₗ[ℂ] ℂ where
  toFun x := (ComplexTransition.CM.totalComplexCoordinates K C).symm x a.2 (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) a.1.castSucc
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def totalGraphSlot (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (Z : Matrix (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places) ℂ)
    (a : Fin 2 × Fin 2) : PeriodTotal.CM.TotalPositions K places → ℂ := fun j =>
  totalGraphCoefficient K C a (Sum.elim (Z *ᵥ (Pi.basisFun ℂ _) j) ((Pi.basisFun ℂ _) j))

theorem total_graph_slot_apply (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (PeriodTotal.CM.TotalPositions K places)) (a : Fin 2 × Fin 2)
    (j : PeriodTotal.CM.TotalPositions K places) :
    totalGraphSlot K C Z.matrix a j =
      TotalPeriodGraphs.CM.totalGraphInAmbient K C Z ((Pi.basisFun ℂ _) j) a.2 (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) a.1.castSucc := rfl

theorem total_graph_slot_holomorphic
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V}
    (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (Z : V → Matrix (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places) ℂ)
    (hZ : DifferentiableOn ℂ Z s) (a : Fin 2 × Fin 2) :
    DifferentiableOn ℂ (fun z => totalGraphSlot K C (Z z) a) s := by
  apply differentiableOn_pi.mpr
  intro j
  apply (totalGraphCoefficient K C a).toContinuousLinearMap.differentiable.comp_differentiableOn
  apply differentiableOn_pi.mpr
  intro i
  cases i with
  | inl i =>
    change DifferentiableOn ℂ (fun z => ∑ k, Z z i k * ((Pi.basisFun ℂ _) j) k) s
    fun_prop
  | inr i => exact differentiableOn_const _

theorem total_graph_slot_block {d₀ d₁ : Gal(K/ℚ) → Bool}
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (a : Fin 2 × Fin 2) :
    totalGraphSlot K ![L₀.coordinates, L₁.coordinates]
      (BlockPeriod.CM.blockPeriod (L₀.period z) (L₁.period z)).matrix a = InitialTensor.CM.splitThetaSlot K L₀ L₁ z a := by
  funext j
  rw [total_graph_slot_apply, TotalPeriodGraphs.CM.total_block_graph]
  rcases a with ⟨i, k⟩
  have hs (j : HeckeCycles.GeometricSource.CM.Positions K places) :
      (fun l => if l = j then (1 : ℂ) else 0) = Pi.single j 1 := by
    funext l
    simp only [Pi.single_apply]
  have hzero (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (HeckeCycles.GeometricSource.CM.Positions K places)) :
      HeckeCycles.GeometricSource.CM.graphInAmbient K C Z (fun _ => 0) = 0 := map_zero _
  fin_cases k <;> cases j with
  | inl j =>
    simp [InitialTensor.CM.splitThetaSlot, Slots.CM.thetaJacobiSlot, Slots.CM.graphCoefficient, Pi.basisFun_apply, Pi.single_apply, hs, hzero]
  | inr j =>
    simp [InitialTensor.CM.splitThetaSlot, Slots.CM.thetaJacobiSlot, Slots.CM.graphCoefficient, Pi.basisFun_apply, Pi.single_apply, hs, hzero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalGraphSlots.CM
