import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompact
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactHalfComparison
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicOriginNormalizedDescent
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartSections

/-! # Intrinsic Compact Tensor Match -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactTensorMatch.Intrinsic

noncomputable section

/-! Differentiating the exact compact completed-kernel identity matches
every normalized chart tensor with an actual native tensor after the
constructed finite rational-phase transport. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise ContDiff

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompact.IntrinsicKernel OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactShear.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactHalfComparison.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactZero.IntrinsicPositivePeriod OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame OAI.RepresentationTheory.Theta.Kernel.IntrinsicChartSections.IntrinsicNormalized OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorAnalytic.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicOriginNormalizedDescent.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicAnalysis.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem compact_tensor_frame_match (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B) (hΘp : Adelic.DataTheta.Descent.ThetaConstruction Bp) (f g : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hw : ∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp) x *
        Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) (a : ℕ) (z : Adelic.BallNatural.Ball) :
    (Adelic.DataTheta.completedTensor Bp g a (Bp.period z).matrix).compContinuousLinearMap
        (fun _ => IntrinsicTensorAnalytic.Intrinsic.matrixLinear (Bp.frame z).invᵀ) =
      (Adelic.DataTheta.completedTensor B f a (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))).compContinuousLinearMap
        (fun _ => IntrinsicTensorAnalytic.Intrinsic.matrixLinear (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ) := by
  let L : (Adelic.BallGeometryData.FrameIndex A → ℂ) →L[ℂ] (Adelic.BallGeometryData.FrameIndex A → ℂ) :=
    IntrinsicTensorAnalytic.Intrinsic.matrixLinear (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))⁻¹ᵀ
  let Lp : (Adelic.BallGeometryData.FrameIndex A → ℂ) →L[ℂ] (Adelic.BallGeometryData.FrameIndex A → ℂ) := IntrinsicTensorAnalytic.Intrinsic.matrixLinear (Bp.frame z).invᵀ
  have he : Adelic.DataTheta.completedTheta Bp g (Bp.period z).matrix ∘ Lp =
      Adelic.DataTheta.completedTheta B f (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)) ∘ L :=
    funext (IntrinsicCompact.IntrinsicKernel.compact_completed_kernel_of_weights p B Bp hC hCp hG hGp f g hw z)
  have h := congrArg (fun k => iteratedFDeriv ℂ a k 0) he
  have hLp := Lp.iteratedFDeriv_comp_right (IntrinsicAnalysis.Intrinsic.completed_contDiff Bp hE hΘp g (Bp.period z))
    0 (show (a : ℕ∞ω) ≤ ⊤ from le_top)
  have hL := L.iteratedFDeriv_comp_right
    (IntrinsicAnalysis.Intrinsic.completed_contDiff B hE hΘ f (IntrinsicCompactZero.IntrinsicPositivePeriod.compactActionSiegel p B Bp hC hCp hG hGp z))
    0 (show (a : ℕ∞ω) ≤ ⊤ from le_top)
  simp only [map_zero] at hLp hL
  have hderiv := hLp.symm.trans (h.trans hL)
  apply ContinuousMultilinearMap.ext
  intro v
  exact congrArg (fun T : Adelic.DataTheta.TaylorTensor (A := A) a => (Nat.factorial a : ℂ)⁻¹ * T v) hderiv

theorem compact_normalized_tensor_match (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B) (hΘp : Adelic.DataTheta.Descent.ThetaConstruction Bp) (f g : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hw : ∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp) x *
        Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) (a : ℕ) (z : Adelic.BallNatural.Ball) :
    (Bp.halfFrame IntrinsicBallTopology.Intrinsic.origin / B.halfFrame IntrinsicBallTopology.Intrinsic.origin) • Adelic.DataTheta.geometricTensor Bp g a z =
      IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTensor B f a (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) := by
  have hc : Bp.halfFrame IntrinsicBallTopology.Intrinsic.origin / B.halfFrame IntrinsicBallTopology.Intrinsic.origin ≠ 0 :=
    div_ne_zero (hGp.2.2.2.2.2.1 IntrinsicBallTopology.Intrinsic.origin).1 (hG.2.2.2.2.2.1 IntrinsicBallTopology.Intrinsic.origin).1
  have hs : (Bp.halfFrame IntrinsicBallTopology.Intrinsic.origin / B.halfFrame IntrinsicBallTopology.Intrinsic.origin) * (Bp.halfFrame z)⁻¹ = (B.halfFrame z)⁻¹ := by
    rw [IntrinsicCompactHalfComparison.Intrinsic.compact_half_frame_normalized p B Bp hC hCp hG hGp z,mul_inv_rev]
    rw [mul_left_comm, mul_inv_cancel₀ hc,mul_one]
  have hh : IntrinsicParameterGraph.IntrinsicHalfFrame.halfFrameExtension B z.val = B.halfFrame z := dite_eq_left z.property
  unfold Adelic.DataTheta.geometricTensor IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTensor
  rw [smul_smul,hs,hh]
  exact congrArg (fun T : Adelic.DataTheta.TaylorTensor (A := A) a => (B.halfFrame z)⁻¹ • T)
    (compact_tensor_frame_match p B Bp hC hCp hG hGp hE hΘ hΘp f g hw a z)

theorem compact_normalized_top_transport (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B) (hΘp : Adelic.DataTheta.Descent.ThetaConstruction Bp) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) :
    ∃ g : Adelic.FiniteSchwartz.finiteSchwartz F 6,
      (∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
        IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp) x *
          Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) ∧
      ∀ z, IntrinsicOriginNormalizedDescent.Intrinsic.originNormalizedTop B p Bp g z = IntrinsicChartSections.IntrinsicNormalized.normalizedParameterTop B f (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) := by
  obtain ⟨g,hg⟩ := IntrinsicQuadraticPhase.Intrinsic.native_quadratic_phase_input F 6 f (-IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp)
  refine ⟨g,hg,?_⟩
  intro z
  have h := congrArg (IntrinsicSecondProjection.Intrinsic.secondProjection (A := A))
    (compact_normalized_tensor_match p B Bp hC hCp hG hGp hE hΘ hΘp f g hg 2 z)
  exact ((IntrinsicSecondProjection.Intrinsic.secondProjection (A := A)).map_smul (Bp.halfFrame IntrinsicBallTopology.Intrinsic.origin / B.halfFrame IntrinsicBallTopology.Intrinsic.origin)
    (Adelic.DataTheta.geometricTensor Bp g 2 z)).symm.trans h

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactTensorMatch.Intrinsic
