import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartSections

/-! # Intrinsic Fixed Slots -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedSlots.Intrinsic

noncomputable section

/-! The compact-family top projection uses the fixed distinguished
dual slots. All its remaining compact dependence is in the positive
period, hence in the actual moved Hodge subspace. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicCompactSlots
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartSections.IntrinsicNormalized
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorAnalytic.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}

theorem second_projection_eq_on_slots (T : Adelic.DataTheta.TaylorTensor (A := A) 2)
    (L M : (Adelic.BallGeometryData.FrameIndex A → ℂ) →L[ℂ] (Adelic.BallGeometryData.FrameIndex A → ℂ))
    (h : ∀ r u, L (IntrinsicSecondProjection.Intrinsic.slotEmbedding r u) = M (IntrinsicSecondProjection.Intrinsic.slotEmbedding r u)) :
    IntrinsicSecondProjection.Intrinsic.secondProjection (T.compContinuousLinearMap (fun _ => L)) =
      IntrinsicSecondProjection.Intrinsic.secondProjection (T.compContinuousLinearMap (fun _ => M)) := by
  have he (r s : Fin 2) (u v : IntrinsicExterior.Intrinsic.Tangent) :
      (T.compContinuousLinearMap (fun _ => L)) ![IntrinsicSecondProjection.Intrinsic.slotEmbedding r u,IntrinsicSecondProjection.Intrinsic.slotEmbedding s v] =
        (T.compContinuousLinearMap (fun _ => M)) ![IntrinsicSecondProjection.Intrinsic.slotEmbedding r u,IntrinsicSecondProjection.Intrinsic.slotEmbedding s v] := by
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    fin_cases i <;> exact h _ _
  ext w
  have hw : w = ![w 0,w 1] := by funext i; fin_cases i <;> rfl
  rw [hw,IntrinsicSecondProjection.Intrinsic.secondProjection_apply,IntrinsicSecondProjection.Intrinsic.secondProjection_apply,he,he,he,he]

def fixedSlotsTop (B : Adelic.DataTheta.ComparisonData F H K A) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (z : Adelic.BallNatural.Ball) (Z : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ) : IntrinsicExterior.Intrinsic.TopCovector :=
  (B.halfFrame z)⁻¹ • IntrinsicSecondProjection.Intrinsic.secondProjection ((Adelic.DataTheta.completedTensor B f 2 Z).compContinuousLinearMap
    (fun _ => IntrinsicTensorAnalytic.Intrinsic.matrixLinear (B.frame z).invᵀ))

variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem normalized_top_fixed_slots (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (z : Adelic.BallNatural.Ball) :
    IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTop B f (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) =
      fixedSlotsTop B f z (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)) := by
  have he := second_projection_eq_on_slots
    (Adelic.DataTheta.completedTensor B f 2 (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)))
    (IntrinsicTensorAnalytic.Intrinsic.matrixLinear (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ)
    (IntrinsicTensorAnalytic.Intrinsic.matrixLinear (B.frame z).invᵀ)
    (fun r u => IntrinsicFrameOn.IntrinsicCompactSlots.action_inverse_slot p B Bp hC hCp hG hGp z r u)
  have hh : IntrinsicParameterGraph.IntrinsicHalfFrame.halfFrameExtension B z.val = B.halfFrame z := dite_eq_left z.property
  unfold IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTop IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTensor fixedSlotsTop
  rw [map_smul,he,hh]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicFixedSlots.Intrinsic
