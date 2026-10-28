import OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartSections
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactZero

/-! # Intrinsic Normalized Base -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicNormalizedBase.IntrinsicCompactFamily

/-! The explicit normalized completed tensors are continuous in the
topology of all derivatives on compact subsets for every actual compact
frame choice. Pointwise full native comparisons prove positivity; their
choice is not assumed to be continuous. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactZero.IntrinsicPositivePeriod OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartSections.IntrinsicNormalized OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : ∀ p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A, Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}
variable (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
variable (hCp : ∀ p, Adelic.DataTheta.CoordinateIdentification (Bp p) P) (hGp : ∀ p, Adelic.DataTheta.GeometryIdentification (Bp p))

include Bp hC hG hCp hGp in
theorem action_parameter_positive_graph (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) :
    IntrinsicCompactActionParameter.Intrinsic.actionParameter A p ∈ IntrinsicChartSections.IntrinsicNormalized.positiveGraphParameters B := by
  intro z
  exact ⟨IntrinsicCompactFrameComparison.Intrinsic.action_parameter_graph_domain p B (Bp p) hC (hCp p) hG (hGp p) z,
    IntrinsicCompactZero.IntrinsicPositivePeriod.compact_chart_symmetric p B (Bp p) hC (hCp p) hG (hGp p) z,
    IntrinsicCompactZero.IntrinsicPositivePeriod.compact_chart_imaginary_positive p B (Bp p) hC (hCp p) hG (hGp p) z⟩

def compactGraphParameter (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) : IntrinsicChartSections.IntrinsicNormalized.positiveGraphParameters B :=
  ⟨IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,action_parameter_positive_graph B Bp hC hG hCp hGp p⟩

theorem compact_graph_parameter_continuous :
    Continuous (compactGraphParameter B Bp hC hG hCp hGp) := by
  apply Continuous.subtype_mk
  exact IntrinsicCompactActionParameter.Intrinsic.action_parameter_continuous A

variable (hL : Adelic.DataTheta.Descent.LatticeIdentification B) (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))

def compactNormalizedTensorSection (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (a : ℕ) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) :
    IntrinsicSmooth.IntrinsicSections.SmoothSection (Adelic.DataTheta.TaylorTensor (A := A) a) :=
  IntrinsicChartSections.IntrinsicNormalized.normalizedTensorSection B hG hL hE f a (compactGraphParameter B Bp hC hG hCp hGp p)

def compactNormalizedTopSection (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) :
    IntrinsicSmooth.IntrinsicSections.SmoothSection IntrinsicExterior.Intrinsic.TopCovector :=
  IntrinsicChartSections.IntrinsicNormalized.normalizedTopSection B hG hL hE f (compactGraphParameter B Bp hC hG hCp hGp p)

theorem compact_normalized_tensor_continuous (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (a : ℕ) :
    Continuous (compactNormalizedTensorSection B Bp hC hG hCp hGp hL hE f a) :=
  (IntrinsicChartSections.IntrinsicNormalized.normalized_tensor_section_continuous B hG hL hE f a).comp
    (compact_graph_parameter_continuous B Bp hC hG hCp hGp)

theorem compact_normalized_top_continuous (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) :
    Continuous (compactNormalizedTopSection B Bp hC hG hCp hGp hL hE f) :=
  (IntrinsicChartSections.IntrinsicNormalized.normalized_top_section_continuous B hG hL hE f).comp
    (compact_graph_parameter_continuous B Bp hC hG hCp hGp)

theorem compact_normalized_top_value (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (z : Adelic.BallNatural.Ball) :
    (compactNormalizedTopSection B Bp hC hG hCp hGp hL hE f p).value z =
      IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTop B f (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) := rfl

end RepresentationTheory.Theta.Kernel.IntrinsicNormalizedBase.IntrinsicCompactFamily

namespace RepresentationTheory.Theta.Kernel.IntrinsicNormalizedBase.Intrinsic

/-! The normalized family recovers the actual native completed tensor
and its literal order-two top projection at the identity compact choice. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicMultiplicityPhase OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphCalculus.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartSections.IntrinsicNormalized OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem action_identity_graph (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) (x : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A (IntrinsicCompactChoices.Intrinsic.identityChoice A)) z.val).mulVec
      (Sum.elim x ((B.period z).matrix.mulVec x)) = Sum.elim x ((B.period z).matrix.mulVec x) := by
  let a : Adelic.BallGeometryData.FrameIndex A → ℂ := (B.frame z).inv.mulVec x
  have ha : (B.frame z).val.mulVec a = x := by
    change (B.frame z).val.mulVec ((B.frame z).inv.mulVec x) = x
    rw [Matrix.mulVec_mulVec,(B.frame z).val_inv,Matrix.one_mulVec]
  have h := IntrinsicCompactActionParameter.Intrinsic.coordinate_action_frame A B hG (IntrinsicCompactChoices.Intrinsic.identityChoice A) z a
  have hm : IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A (IntrinsicCompactChoices.Intrinsic.identityChoice A) z a = Adelic.BallGeometryData.geometricFrame A z a := by
    funext v
    apply Prod.ext <;> funext ij <;>
      simp [IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame,IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase,IntrinsicCompactOne.IntrinsicMultiplicityPhase.multiplicityPhase,IntrinsicCompactChoices.Intrinsic.identityChoice]
  rw [hm,← hG.2.2.2.2.2.2.1 z a,ContinuousLinearEquiv.symm_apply_apply,ha] at h
  exact h

theorem action_identity_blocks (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A (IntrinsicCompactChoices.Intrinsic.identityChoice A),z.val) = 1 ∧
      IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A (IntrinsicCompactChoices.Intrinsic.identityChoice A),z.val) = (B.period z).matrix := by
  have hb := IntrinsicGraphCalculus.Intrinsic.blocks_of_fixed_graph _ _ (action_identity_graph B hG z)
  constructor
  · simpa only [IntrinsicParameterGraph.Intrinsic.parameterPositionBlock,IntrinsicParameterGraph.Intrinsic.periodExtension_ball] using hb.1
  · unfold IntrinsicParameterGraph.Intrinsic.parameterPeriodChart IntrinsicGraphCalculus.Intrinsic.graphChart
    rw [IntrinsicParameterGraph.Intrinsic.periodExtension_ball,hb.1,hb.2]
    simp

theorem normalized_tensor_identity (hG : Adelic.DataTheta.GeometryIdentification B)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (a : ℕ) (z : Adelic.BallNatural.Ball) :
    IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTensor B f a (IntrinsicCompactActionParameter.Intrinsic.actionParameter A (IntrinsicCompactChoices.Intrinsic.identityChoice A),z.val) =
      Adelic.DataTheta.geometricTensor B f a z := by
  have hp := action_identity_blocks B hG z
  have hf : IntrinsicParameterGraph.IntrinsicHalfFrame.frameExtension B z.val = (B.frame z).val := dite_eq_left z.property
  have hh : IntrinsicParameterGraph.IntrinsicHalfFrame.halfFrameExtension B z.val = B.halfFrame z := dite_eq_left z.property
  unfold IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTensor Adelic.DataTheta.geometricTensor
  rw [hp.2,IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame,hp.1,Matrix.one_mul,hf,hh,
    Matrix.inv_eq_left_inv (B.frame z).inv_val]
  rfl

theorem normalized_top_identity (hG : Adelic.DataTheta.GeometryIdentification B)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (z : Adelic.BallNatural.Ball) :
    IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTop B f (IntrinsicCompactActionParameter.Intrinsic.actionParameter A (IntrinsicCompactChoices.Intrinsic.identityChoice A),z.val) = IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z := by
  unfold IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTop IntrinsicSecondProjection.Intrinsic.thetaTopForm
  rw [normalized_tensor_identity B hG f 2 z]

end RepresentationTheory.Theta.Kernel.IntrinsicNormalizedBase.Intrinsic

end

end OAI
