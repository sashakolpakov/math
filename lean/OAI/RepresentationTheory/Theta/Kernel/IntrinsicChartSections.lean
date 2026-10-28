import OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterTensor
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth

/-! # Intrinsic Chart Sections -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicChartSections.Intrinsic

/-! The actual completed tensors and top forms on positive local period
charts vary continuously in the topology of all derivatives on compact
subsets of the ball. The parameter domain is defined by explicit period
positivity and the local determinant branch. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise ContDiff

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterTensor.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicLocal OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)

def positiveChartParameters : Set (IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A) :=
  {p | ∀ z : Adelic.BallNatural.Ball, (p,z.val) ∈ IntrinsicParameterGraph.IntrinsicHalfFrame.parameterHalfDomain B ∧
    IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (p,z.val) ∈ Definitions.siegelDomain}

theorem positive_chart_base (hG : Adelic.DataTheta.GeometryIdentification B) :
    IntrinsicCompactProjector.IntrinsicParameter.baseParameter A ∈ positiveChartParameters B := by
  intro z
  refine ⟨IntrinsicParameterGraph.IntrinsicHalfFrame.parameter_half_domain_base B hG z,?_⟩
  rw [IntrinsicParameterGraph.Intrinsic.parameter_period_base B hG z]
  exact ⟨(B.period z).symmetric,(B.period z).imaginary_posDef⟩

theorem chart_tensor_ambient (hG : Adelic.DataTheta.GeometryIdentification B) (hL : Adelic.DataTheta.Descent.LatticeIdentification B)
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A)) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (a : ℕ)
    (p : IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A) (hp : p ∈ positiveChartParameters B)
    (z : IntrinsicExterior.Intrinsic.Tangent) (hz : z ∈ Adelic.BallGeometryData.ballDomain) :
    ContDiffAt ℝ ⊤ (IntrinsicParameterTensor.Intrinsic.parameterTensor B f a) (p,z) := by
  obtain ⟨hh,hZ⟩ := hp ⟨z,hz⟩
  exact IntrinsicParameterTensor.Intrinsic.parameter_tensor_analytic B hG hL hE f a (p,z) hh
    ⟨IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (p,z),hZ.1,hZ.2⟩ rfl

def chartTensorSection (hG : Adelic.DataTheta.GeometryIdentification B) (hL : Adelic.DataTheta.Descent.LatticeIdentification B)
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A)) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (a : ℕ)
    (p : positiveChartParameters B) : IntrinsicSmooth.IntrinsicSections.SmoothSection (Adelic.DataTheta.TaylorTensor (A := A) a) :=
  IntrinsicSmooth.IntrinsicLocal.localSection (positiveChartParameters B) (fun p z => IntrinsicParameterTensor.Intrinsic.parameterTensor B f a (p,z))
    (chart_tensor_ambient B hG hL hE f a) p

def chartTopSection (hG : Adelic.DataTheta.GeometryIdentification B) (hL : Adelic.DataTheta.Descent.LatticeIdentification B)
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A)) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2))
    (p : positiveChartParameters B) : IntrinsicSmooth.IntrinsicSections.SmoothSection IntrinsicExterior.Intrinsic.TopCovector :=
  IntrinsicSmooth.IntrinsicSections.mapSection ((IntrinsicSecondProjection.Intrinsic.secondProjection (A := A)).restrictScalars ℝ)
    (chartTensorSection B hG hL hE f 2 p)

theorem chart_tensor_section_continuous (hG : Adelic.DataTheta.GeometryIdentification B) (hL : Adelic.DataTheta.Descent.LatticeIdentification B)
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A)) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (a : ℕ) :
    Continuous (chartTensorSection B hG hL hE f a) :=
  IntrinsicSmooth.IntrinsicLocal.localSection_continuous (positiveChartParameters B) (fun p z => IntrinsicParameterTensor.Intrinsic.parameterTensor B f a (p,z))
    (chart_tensor_ambient B hG hL hE f a)

theorem chart_top_section_continuous (hG : Adelic.DataTheta.GeometryIdentification B) (hL : Adelic.DataTheta.Descent.LatticeIdentification B)
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A)) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) :
    Continuous (chartTopSection B hG hL hE f) :=
  (IntrinsicSmooth.IntrinsicSections.mapSection_continuous _).comp (chart_tensor_section_continuous B hG hL hE f 2)

theorem chart_top_section_value (hG : Adelic.DataTheta.GeometryIdentification B) (hL : Adelic.DataTheta.Descent.LatticeIdentification B)
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A)) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2))
    (p : positiveChartParameters B) (z : Adelic.BallNatural.Ball) :
    (chartTopSection B hG hL hE f p).value z = IntrinsicParameterTensor.Intrinsic.parameterTopForm B f (p.val,z.val) := rfl

theorem chart_top_section_base (hG : Adelic.DataTheta.GeometryIdentification B) (hL : Adelic.DataTheta.Descent.LatticeIdentification B)
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A)) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 2)) (z : Adelic.BallNatural.Ball) :
    (chartTopSection B hG hL hE f ⟨IntrinsicCompactProjector.IntrinsicParameter.baseParameter A,positive_chart_base B hG⟩).value z =
      IntrinsicSecondProjection.Intrinsic.thetaTopForm B f z :=
  IntrinsicParameterTensor.Intrinsic.parameter_top_base B hG f z

end RepresentationTheory.Theta.Kernel.IntrinsicChartSections.Intrinsic

namespace RepresentationTheory.Theta.Kernel.IntrinsicChartSections.IntrinsicNormalized

/-! Normalized completed tensors using the reference half frame.
They are analytic on every positive graph chart, with no choice of a
square root in the compact parameter. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise ContDiff

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameAnalytic.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameAnalytic.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicAmbientRegularity.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorAnalytic.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterTensor.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicLocal OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)

def normalizedParameterTensor (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (a : ℕ)
    (q : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A)) : Adelic.DataTheta.TaylorTensor (A := A) a :=
  (IntrinsicParameterGraph.IntrinsicHalfFrame.halfFrameExtension B q.2)⁻¹ •
    (Adelic.DataTheta.completedTensor B f a (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B q)).compContinuousLinearMap
      (fun _ => IntrinsicTensorAnalytic.Intrinsic.matrixLinear (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B q)⁻¹ᵀ)

def normalizedParameterTop (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (q : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A)) : IntrinsicExterior.Intrinsic.TopCovector :=
  IntrinsicSecondProjection.Intrinsic.secondProjection (normalizedParameterTensor B f 2 q)

theorem normalized_parameter_tensor_analytic (hG : Adelic.DataTheta.GeometryIdentification B)
    (hL : Adelic.DataTheta.Descent.LatticeIdentification B) (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (a : ℕ) (q : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A))
    (hq : q ∈ IntrinsicParameterGraph.Intrinsic.parameterGraphDomain B)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) (hZ : IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B q = Z.matrix) :
    ContDiffAt ℝ ⊤ (normalizedParameterTensor B f a) q := by
  have ht : ContDiffAt ℝ ⊤ (Adelic.DataTheta.completedTensor B f a) (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B q) := by
    rw [hZ]
    exact IntrinsicAmbientRegularity.Intrinsic.completedTensor_ambient_contDiffAt B hE hL f a Z
  have hp := (IntrinsicFrameAnalytic.IntrinsicParameter.parameter_period_analytic B hG q hq).restrict_scalars ℝ
  have hm := IntrinsicFrameAnalytic.IntrinsicParameter.parameter_frame_analytic B hG q hq.1
  have hf : IntrinsicParameterGraph.IntrinsicHalfFrame.frameExtension B q.2 = (B.frame ⟨q.2,hq.1⟩).val := dite_eq_left hq.1
  have hd : (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B q).det ≠ 0 := by
    rw [IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame,Matrix.det_mul,hf]
    exact mul_ne_zero hq.2 (isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (B.frame ⟨q.2,hq.1⟩))))
  have hl := (IntrinsicTensorAnalytic.Intrinsic.inverseTransposeLinear_analytic _ hm hd).restrict_scalars ℝ
  have hh : ContDiffAt ℂ ⊤ (fun r : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A) => IntrinsicParameterGraph.IntrinsicHalfFrame.halfFrameExtension B r.2) q :=
    (IntrinsicFrameAnalytic.Intrinsic.halfFrameExtension_analytic B hG ⟨q.2,hq.1⟩).comp q contDiffAt_snd
  have hn : IntrinsicParameterGraph.IntrinsicHalfFrame.halfFrameExtension B q.2 ≠ 0 := by
    rw [IntrinsicParameterGraph.IntrinsicHalfFrame.halfFrameExtension,dite_eq_left hq.1]
    exact (hG.2.2.2.2.2.1 ⟨q.2,hq.1⟩).1
  exact ((hh.restrict_scalars ℝ).inv hn).smul
    (IntrinsicTensorAnalytic.Intrinsic.tensor_precomposition_analytic a _ _ (ht.comp q hp) hl)

def positiveGraphParameters : Set (IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A) :=
  {p | ∀ z : Adelic.BallNatural.Ball, (p,z.val) ∈ IntrinsicParameterGraph.Intrinsic.parameterGraphDomain B ∧
    IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (p,z.val) ∈ Definitions.siegelDomain}

theorem normalized_chart_ambient (hG : Adelic.DataTheta.GeometryIdentification B) (hL : Adelic.DataTheta.Descent.LatticeIdentification B)
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A)) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (a : ℕ)
    (p : IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A) (hp : p ∈ positiveGraphParameters B)
    (z : IntrinsicExterior.Intrinsic.Tangent) (hz : z ∈ Adelic.BallGeometryData.ballDomain) :
    ContDiffAt ℝ ⊤ (normalizedParameterTensor B f a) (p,z) := by
  obtain ⟨hg,hZ⟩ := hp ⟨z,hz⟩
  exact normalized_parameter_tensor_analytic B hG hL hE f a (p,z) hg
    ⟨IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (p,z),hZ.1,hZ.2⟩ rfl

def normalizedTensorSection (hG : Adelic.DataTheta.GeometryIdentification B) (hL : Adelic.DataTheta.Descent.LatticeIdentification B)
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A)) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (a : ℕ)
    (p : positiveGraphParameters B) : IntrinsicSmooth.IntrinsicSections.SmoothSection (Adelic.DataTheta.TaylorTensor (A := A) a) :=
  IntrinsicSmooth.IntrinsicLocal.localSection (positiveGraphParameters B) (fun p z => normalizedParameterTensor B f a (p,z))
    (normalized_chart_ambient B hG hL hE f a) p

def normalizedTopSection (hG : Adelic.DataTheta.GeometryIdentification B) (hL : Adelic.DataTheta.Descent.LatticeIdentification B)
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A)) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (p : positiveGraphParameters B) : IntrinsicSmooth.IntrinsicSections.SmoothSection IntrinsicExterior.Intrinsic.TopCovector :=
  IntrinsicSmooth.IntrinsicSections.mapSection ((IntrinsicSecondProjection.Intrinsic.secondProjection (A := A)).restrictScalars ℝ)
    (normalizedTensorSection B hG hL hE f 2 p)

theorem normalized_tensor_section_continuous (hG : Adelic.DataTheta.GeometryIdentification B)
    (hL : Adelic.DataTheta.Descent.LatticeIdentification B) (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) (a : ℕ) :
    Continuous (normalizedTensorSection B hG hL hE f a) :=
  IntrinsicSmooth.IntrinsicLocal.localSection_continuous (positiveGraphParameters B) (fun p z => normalizedParameterTensor B f a (p,z))
    (normalized_chart_ambient B hG hL hE f a)

theorem normalized_top_section_continuous (hG : Adelic.DataTheta.GeometryIdentification B)
    (hL : Adelic.DataTheta.Descent.LatticeIdentification B) (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) : Continuous (normalizedTopSection B hG hL hE f) :=
  (IntrinsicSmooth.IntrinsicSections.mapSection_continuous _).comp (normalized_tensor_section_continuous B hG hL hE f 2)

end RepresentationTheory.Theta.Kernel.IntrinsicChartSections.IntrinsicNormalized

end

end OAI
