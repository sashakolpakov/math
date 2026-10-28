import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineComponents
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceGeometricFrame

/-! # Single Line Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineFrame.CM

noncomputable section

/-! The actual source frame of each individual line maps to the native
one-line frame through a constant invertible coefficient map. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]

def sourceSingleIndexEquiv (places : HeckeCycles.GeometricSource.CM.Places K) : HeckeCycles.GeometricSource.CM.Positions K places ≃ Fin places.count × (Fin 3 × Fin 1) where
  toFun p := (p.1, p.2, 0)
  invFun p := (p.1, p.2.1)
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨v, i, j⟩
    exact congrArg (fun k => (v, i, k)) (Subsingleton.elim 0 j)

variable {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true) (j : Fin 2)

def directSingleLineFrameCoefficients : (HeckeCycles.GeometricSource.CM.Positions K places → ℂ) →ₗ[ℂ]
    (Fin places.count × (Fin 3 × Fin 1) → ℂ) where
  toFun u p := SourceFrameComponents.CM.directSourceFrameScale K Q p.1 (p.2.1, j) * u (p.1, p.2.1)
  map_add' u v := by funext p; exact mul_add _ _ _
  map_smul' c u := by funext p; exact mul_left_comm _ _ _

theorem direct_single_line_frame_coefficients_bijective :
    Function.Bijective (directSingleLineFrameCoefficients K Q j) := by
  constructor
  · intro u w h
    funext p
    exact mul_left_cancel₀ (SourceFrameComponents.CM.direct_source_frame_scale_ne_zero K Q p.1 (p.2, j)) (congrFun h (p.1, p.2, 0))
  · intro w
    refine ⟨fun p => w (p.1, p.2, 0) / SourceFrameComponents.CM.directSourceFrameScale K Q p.1 (p.2, j), ?_⟩
    funext p
    rcases p with ⟨v, i, k⟩
    fin_cases k
    exact mul_div_cancel₀ _ (SourceFrameComponents.CM.direct_source_frame_scale_ne_zero K Q v (i, j))

def directSingleLineFrameCoefficientEquiv : (HeckeCycles.GeometricSource.CM.Positions K places → ℂ) ≃ₗ[ℂ]
    (Fin places.count × (Fin 3 × Fin 1) → ℂ) :=
  LinearEquiv.ofBijective (directSingleLineFrameCoefficients K Q j)
    (direct_single_line_frame_coefficients_bijective K Q j)

def singleNativePhaseProjection : RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ B.other_place) →
    RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) :=
  fun w v => (fun i => (w v).1 (i.1, j), fun i => (w v).2 (i.1, j))

theorem direct_single_line_geometric_frame_projection (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball)
    (u : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    singleNativePhaseProjection K Q hμ j
      (RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ B.other_place) z
        (SourceFrameComponents.CM.directSourceFrameCoefficients K Q (Sum.elim u u))) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) z (directSingleLineFrameCoefficients K Q j u) := by
  fin_cases j <;> rfl

omit d Q hμ j in
theorem direct_single_line_geometric_frame
    (d : Fin 2 → Gal(K/ℚ) → Bool)
    (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
    (hμ : ∀ k, d k (places.representative places.distinguished) = true)
    (j : Fin 2) (z : B.Domain) (u : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j (Prescribed.CM.nativePeriodFrame K B places (d j) z.val u) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
        (directSingleLineFrameCoefficients K Q j u) := by
  let w := AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val (Sum.elim u u)
  have hw : w j = Prescribed.CM.nativePeriodFrame K B places (d j) z.val u := by
    fin_cases j <;> rfl
  have hc := (congrArg (SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j) hw).symm.trans
    (SingleLineComponents.CM.direct_single_line_components_projection K Q hμ j w)
  have hf := congrArg (singleNativePhaseProjection K Q hμ j)
    (SourceGeometricFrame.CM.direct_source_geometric_frame K d Q hμ B.other_place z (Sum.elim u u))
  exact hc.trans (hf.trans (direct_single_line_geometric_frame_projection K Q hμ j (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) u))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineFrame.CM
