import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPrescribedAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MovingTotalPeriod

/-! # Source Period Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourcePeriodAction.CM

noncomputable section

/-! ThetaCycle: the actual source period at the image ball point is the
Siegel transform by the actual rational matrix in its retained basis. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

theorem siegel_matrix_ext {I : Type*} [Fintype I] (Z W : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (h : Z.matrix = W.matrix) : Z = W := by
  cases Z
  cases W
  cases h
  rfl

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool}

theorem source_graph_sum_coordinates (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (HeckeCycles.GeometricSource.CM.Positions K places)) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    SourceSymplecticAction.CM.sourceComplexSumCoordinates K C (HeckeCycles.GeometricSource.CM.graphInAmbient K C Z x) =
      Sum.elim (Z.matrix *ᵥ x) x := by
  change (LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ).symm
    (C.complex (C.complex.symm _)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem source_graph_prescribed (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d) (z : B.Domain)
    (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    HeckeCycles.GeometricSource.CM.prescribed K B places d z.val (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z.val) x) := by
  apply (L.graph_prescribed z.val z.property _).mpr
  change (L.coordinates.complex (L.coordinates.complex.symm _)).1 =
    (L.period z.val).matrix *ᵥ (L.coordinates.complex (L.coordinates.complex.symm _)).2
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable [IsGalois ℚ K]

theorem source_ball_period_graph (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)
    (z : B.Domain) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    let γ := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)
    let J := γ.complexify.denominator (L.period z.val).matrix
    (γ.transformSiegel (L.period z.val)).matrix *ᵥ (J *ᵥ x) =
      (L.period (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)).matrix *ᵥ (J *ᵥ x) := by
  dsimp only
  let w := HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z.val) x
  have hp := BallPrescribedAction.CM.ball_action_prescribed K B places d g hg z w (source_graph_prescribed K L z x)
  have he := (L.graph_prescribed (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
    (BallLineAction.CM.ball_line_action_mem K B g hg z) (SourceSymplecticAction.CM.ballAmbientAction K g w)).mp hp
  have hcoords : SourceSymplecticAction.CM.sourceComplexSumCoordinates K L.coordinates (SourceSymplecticAction.CM.ballAmbientAction K g w) =
      Sum.elim
        (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)).transformSiegel
          (L.period z.val)).matrix *ᵥ
            ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)).complexify.denominator
              (L.period z.val).matrix *ᵥ x))
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)).complexify.denominator
          (L.period z.val).matrix *ᵥ x) := by
    rw [← SourceSymplecticAction.CM.source_rational_matrix_complex_action]
    change (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg).val.map (algebraMap ℚ ℂ) *ᵥ
      SourceSymplecticAction.CM.sourceComplexSumCoordinates K L.coordinates
        (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z.val) x) = _
    rw [source_graph_sum_coordinates]
    exact MovingTotalPeriod.CM.rational_symplectic_graph_substitution (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)
      (L.period z.val) x
  have hfirst := congrArg (fun u => fun i => u (Sum.inl i)) hcoords
  have hsecond := congrArg (fun u => fun i => u (Sum.inr i)) hcoords
  change (L.coordinates.complex (SourceSymplecticAction.CM.ballAmbientAction K g w)).1 = _ at hfirst
  change (L.coordinates.complex (SourceSymplecticAction.CM.ballAmbientAction K g w)).2 = _ at hsecond
  rwa [hfirst, hsecond] at he

theorem source_ball_period_transform (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)
    (z : B.Domain) :
    L.period (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)).transformSiegel (L.period z.val) := by
  apply siegel_matrix_ext
  apply Matrix.ext_iff_mulVec.mpr
  intro y
  let γ := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)
  let J := γ.complexify.denominator (L.period z.val).matrix
  have hJ : J *ᵥ (J⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (γ.denominator_det_isUnit (L.period z.val)),
      Matrix.one_mulVec]
  have he := source_ball_period_graph K L g hg z (J⁻¹ *ᵥ y)
  dsimp only at he
  change (γ.transformSiegel (L.period z.val)).matrix *ᵥ (J *ᵥ (J⁻¹ *ᵥ y)) =
    (L.period (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)).matrix *ᵥ (J *ᵥ (J⁻¹ *ᵥ y)) at he
  rw [hJ] at he
  exact he.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourcePeriodAction.CM
