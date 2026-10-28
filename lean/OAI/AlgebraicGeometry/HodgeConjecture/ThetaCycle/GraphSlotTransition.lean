import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ApproximationCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalGraphSlots
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactComplex

/-! # Graph Slot Transition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.GraphSlotTransition.CM

noncomputable section

/-! ThetaCycle: the actual inverse Jacobi substitution carries the original
graph rows through the same multiplicity basis as the rational splitting. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

theorem linear_map_basis_row {I V : Type*} [Fintype I]
    [AddCommGroup V] [Module ℂ V] (f : (I → ℂ) →ₗ[ℂ] V) (x : I → ℂ) :
    f x = ∑ j, x j • f ((Pi.basisFun ℂ I) j) := by
  conv_lhs => rw [← (Pi.basisFun ℂ I).sum_repr x]
  simp only [map_sum, map_smul, Pi.basisFun_repr]

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)

def approximationMultiplicityMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) A.basis

theorem approximation_multiplicity_matrix_apply (i k : Fin 2) :
    approximationMultiplicityMatrix K D A i k = (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (A.basis k i) : ℂ) := rfl

theorem approximation_multiplicity_matrix_det_ne_zero :
    (approximationMultiplicityMatrix K D A).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp
    (CompactComplex.CM.local_basis_matrix_isUnit (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) A.basis)).ne_zero

theorem total_graph_slot_pairing
    (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K D.ball D.places)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (PeriodTotal.CM.TotalPositions K D.places)) (a : Fin 2 × Fin 2)
    (x : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    TotalGraphSlots.CM.totalGraphSlot K C Z.matrix a ⬝ᵥ x =
      TotalPeriodGraphs.CM.totalGraphInAmbient K C Z x a.2 (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) a.1.castSucc := by
  have h := congrArg (fun w : ComplexTransition.CM.TotalAmbient K => w a.2 (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) a.1.castSucc)
    (linear_map_basis_row (TotalPeriodGraphs.CM.totalGraphInAmbient K C Z) x)
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, TotalGraphSlots.CM.total_graph_slot_apply,
    dotProduct, mul_comm] using h.symm

theorem approximation_graph_slot_transition (z : HeckeCycles.GeometricSource.CM.BallChart) (a : Fin 2 × Fin 2) :
    ApproximationCovariance.CM.approximationJacobiPullback K D A z
        (TotalGraphSlots.CM.totalGraphSlot K (fun i => (D.initialPeriods i).coordinates)
          (MovingTotalPeriod.CM.approximationTotalPeriod K D A z).matrix a) =
      ∑ k : Fin 2, approximationMultiplicityMatrix K D A a.2 k •
        InitialTensor.CM.splitThetaSlot K (A.periods 0) (A.periods 1) z (a.1, k) := by
  rw [ApproximationCovariance.CM.approximation_jacobi_pullback_apply]
  let J := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator
    (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z)).matrix
  let C := fun i => (D.initialPeriods i).coordinates
  let C' := fun i => (A.periods i).coordinates
  let W := MovingTotalPeriod.CM.approximationTotalPeriod K D A z
  let Z := BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z)
  have hC' : C' = ![(A.periods 0).coordinates, (A.periods 1).coordinates] := by
    funext i
    fin_cases i <;> rfl
  funext j
  calc
    _ = TotalGraphSlots.CM.totalGraphSlot K C W.matrix a ⬝ᵥ (J *ᵥ (Pi.basisFun ℂ _) j) := by
      simp only [Pi.basisFun_apply, Matrix.mulVec_single_one]
      change (J.transpose *ᵥ TotalGraphSlots.CM.totalGraphSlot K C W.matrix a) j = _
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.col_apply, mul_comm]
    _ = TotalPeriodGraphs.CM.totalGraphInAmbient K C W (J *ᵥ (Pi.basisFun ℂ _) j) a.2 (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) a.1.castSucc :=
      total_graph_slot_pairing K D C W a _
    _ = (ComplexTransition.CM.complexTensorBasisChange K A.basis (TotalPeriodGraphs.CM.totalGraphInAmbient K C' Z ((Pi.basisFun ℂ _) j)))
        a.2 (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) a.1.castSucc := by rw [MovingTotalPeriod.CM.approximation_total_graph]
    _ = ∑ k : Fin 2, approximationMultiplicityMatrix K D A a.2 k *
        TotalGraphSlots.CM.totalGraphSlot K C' Z.matrix (a.1, k) j := rfl
    _ = _ := by
      simp only [hC', Z, TotalGraphSlots.CM.total_graph_slot_block, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.GraphSlotTransition.CM
