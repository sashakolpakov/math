import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactComplex
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MovingTotalPeriod

/-! # Total Projector -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalProjector.CM

noncomputable section

/-! ThetaCycle: total period projectors and their actual graph images in the
original tensor coordinates. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

def totalSourceProjector (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) : ComplexTransition.CM.TotalAmbient K →ₗ[ℂ] ComplexTransition.CM.TotalAmbient K where
  toFun w i := CompactComplex.CM.sourcePeriodProjector K B places (d i) z (w i)
  map_add' w u := by
    funext i
    exact map_add (CompactComplex.CM.sourcePeriodProjector K B places (d i) z) (w i) (u i)
  map_smul' c w := by
    funext i
    exact map_smul (CompactComplex.CM.sourcePeriodProjector K B places (d i) z) c (w i)

theorem total_source_projector_graph_fixed {d : Fin 2 → Gal(K/ℚ) → Bool}
    (L : (i : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d i))
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    totalSourceProjector K B places d z
      (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (L i).coordinates)
        (BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z)) x) =
    TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (L i).coordinates)
      (BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z)) x := by
  rw [TotalPeriodGraphs.CM.total_block_graph]
  funext i
  fin_cases i
  · exact CompactComplex.CM.source_period_graph_fixed K (L 0) z hz _
  · exact CompactComplex.CM.source_period_graph_fixed K (L 1) z hz _

theorem total_source_projector_graph_image {d : Fin 2 → Gal(K/ℚ) → Bool}
    (L : (i : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d i))
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (w : ComplexTransition.CM.TotalAmbient K) :
    ∃ x : PeriodTotal.CM.TotalPositions K places → ℂ,
      totalSourceProjector K B places d z w =
        TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (L i).coordinates)
          (BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z)) x := by
  let u := totalSourceProjector K B places d z w
  have hu (i : Fin 2) : HeckeCycles.GeometricSource.CM.graphInAmbient K (L i).coordinates ((L i).period z)
      (((L i).coordinates.complex (u i)).2) = u i := by
    have hp := CompactComplex.CM.source_period_projector_prescribed K B places (d i) z (w i)
    have hc := ((L i).graph_prescribed z hz _).mp hp
    change ((L i).coordinates.complex (u i)).1 =
      ((L i).period z).matrix.mulVec (((L i).coordinates.complex (u i)).2) at hc
    apply (L i).coordinates.complex.injective
    change (L i).coordinates.complex ((L i).coordinates.complex.symm
      (((L i).period z).matrix.mulVec (((L i).coordinates.complex (u i)).2),
        ((L i).coordinates.complex (u i)).2)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext hc.symm rfl
  refine ⟨Sum.elim (((L 0).coordinates.complex (u 0)).2)
    (((L 1).coordinates.complex (u 1)).2), ?_⟩
  rw [TotalPeriodGraphs.CM.total_block_graph]
  funext i
  fin_cases i
  · exact (hu 0).symm
  · exact (hu 1).symm

variable {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)

def approximationProjector (z : HeckeCycles.GeometricSource.CM.BallChart) : ComplexTransition.CM.TotalAmbient K →ₗ[ℂ] ComplexTransition.CM.TotalAmbient K :=
  (CompactComplex.CM.complexTensorBasisEquiv K A.basis).toLinearMap.comp <|
    (totalSourceProjector K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z).comp
      (CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm.toLinearMap

/-- The transported projector lands in the literal moving Siegel graph in
the fixed original coordinates. -/
theorem approximation_projector_graph_image (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ D.ball.domain)
    (w : ComplexTransition.CM.TotalAmbient K) :
    ∃ x : PeriodTotal.CM.TotalPositions K D.places → ℂ,
      approximationProjector K D A z w =
        TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (D.initialPeriods i).coordinates)
          (MovingTotalPeriod.CM.approximationTotalPeriod K D A z) x := by
  obtain ⟨x, hx⟩ := total_source_projector_graph_image K A.periods z hz
    ((CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm w)
  let Z := BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z)
  let J := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator Z.matrix
  refine ⟨J *ᵥ x, ?_⟩
  change ComplexTransition.CM.complexTensorBasisChange K A.basis
    (totalSourceProjector K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z
      ((CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm w)) = _
  rw [hx]
  exact (MovingTotalPeriod.CM.approximation_total_graph K D A z x).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalProjector.CM
