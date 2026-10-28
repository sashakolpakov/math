import OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterLinear
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphCalculus

/-! # Intrinsic Parameter Graph -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic

/-! Explicit local period charts for the native compact-place projector
family. The chart recovers the original native period at every ball
point and varies holomorphically wherever its position block is invertible. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Topology _root_.Matrix.Norms.Elementwise

open Filter
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterLinear.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphCalculus.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)

abbrev ParameterPoint := IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A × IntrinsicExterior.Intrinsic.Tangent

def periodExtension (z : IntrinsicExterior.Intrinsic.Tangent) : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ :=
  if hz : z ∈ Adelic.BallGeometryData.ballDomain then (B.period ⟨z,hz⟩).matrix else 0

def parameterBaseDomain : Set (ParameterPoint (A := A)) := {q | q.2 ∈ Adelic.BallGeometryData.ballDomain}

def parameterPositionBlock (q : ParameterPoint (A := A)) : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ :=
  IntrinsicGraphCalculus.Intrinsic.positionBlock (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B q.1 q.2) (periodExtension B q.2)

def parameterGraphDomain : Set (ParameterPoint (A := A)) :=
  {q | q.2 ∈ Adelic.BallGeometryData.ballDomain ∧ (parameterPositionBlock B q).det ≠ 0}

def parameterPeriodChart (q : ParameterPoint (A := A)) : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ :=
  IntrinsicGraphCalculus.Intrinsic.graphChart (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B q.1 q.2) (periodExtension B q.2)

theorem periodExtension_ball (z : Adelic.BallNatural.Ball) : periodExtension B z.val = (B.period z).matrix :=
  dite_eq_left z.property

theorem parameter_base_period_holomorphic (hG : Adelic.DataTheta.GeometryIdentification B) :
    DifferentiableOn ℂ (fun q : ParameterPoint (A := A) => periodExtension B q.2) (parameterBaseDomain (A := A)) :=
  hG.2.2.1.comp differentiableOn_snd (fun _ h => h)

theorem parameter_position_holomorphic (hG : Adelic.DataTheta.GeometryIdentification B) :
    DifferentiableOn ℂ (parameterPositionBlock B) (parameterBaseDomain (A := A)) :=
  (IntrinsicGraphCalculus.Intrinsic.blocks_holomorphic _ _ (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector_holomorphic A B).differentiableOn
    (parameter_base_period_holomorphic B hG)).1

theorem parameter_graph_domain_open (hG : Adelic.DataTheta.GeometryIdentification B) : IsOpen (parameterGraphDomain B) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hs : parameterBaseDomain (A := A) ∈ 𝓝 q :=
    (IntrinsicSmooth.IntrinsicSections.ballDomain_open.preimage continuous_snd).mem_nhds hq.1
  have hc : ContinuousAt (fun r => (parameterPositionBlock B r).det) q :=
    ((AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM.matrix_determinant_holomorphic _
      (parameter_position_holomorphic B hG)).differentiableAt hs).continuousAt
  exact inter_mem hs (hc.eventually_ne hq.2)

theorem parameter_position_base (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    parameterPositionBlock B (IntrinsicCompactProjector.IntrinsicParameter.baseParameter A,z.val) = 1 := by
  unfold parameterPositionBlock
  rw [periodExtension_ball]
  exact (IntrinsicGraphCalculus.Intrinsic.blocks_of_fixed_graph _ _ (IntrinsicParameterLinear.Intrinsic.coordinateProjector_base_graph A B hG z)).1

theorem parameter_graph_domain_base (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    (IntrinsicCompactProjector.IntrinsicParameter.baseParameter A,z.val) ∈ parameterGraphDomain B := by
  refine ⟨z.property,?_⟩
  rw [parameter_position_base B hG z,Matrix.det_one]
  exact one_ne_zero

theorem parameter_period_holomorphic (hG : Adelic.DataTheta.GeometryIdentification B) :
    DifferentiableOn ℂ (parameterPeriodChart B) (parameterGraphDomain B) :=
  IntrinsicGraphCalculus.Intrinsic.graphChart_holomorphic _ _ (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector_holomorphic A B).differentiableOn
    ((parameter_base_period_holomorphic B hG).mono (fun _ h => h.1)) (fun _ h => h.2)

theorem parameter_period_base (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    parameterPeriodChart B (IntrinsicCompactProjector.IntrinsicParameter.baseParameter A,z.val) = (B.period z).matrix := by
  unfold parameterPeriodChart IntrinsicGraphCalculus.Intrinsic.graphChart
  rw [periodExtension_ball]
  obtain ⟨hp,hq⟩ := IntrinsicGraphCalculus.Intrinsic.blocks_of_fixed_graph _ _ (IntrinsicParameterLinear.Intrinsic.coordinateProjector_base_graph A B hG z)
  rw [hp,hq]
  simp

end RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic

namespace RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame

/-! A local square-root determinant frame for the actual projected
native Hodge frame, agreeing with the original half frame at the base
compact choice. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Topology _root_.Matrix.Norms.Elementwise

open Filter
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)

def frameExtension (z : Fin 2 → ℂ) : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ :=
  if hz : z ∈ Adelic.BallGeometryData.ballDomain then (B.frame ⟨z,hz⟩).val else 0

def halfFrameExtension (z : Fin 2 → ℂ) : ℂ :=
  if hz : z ∈ Adelic.BallGeometryData.ballDomain then B.halfFrame ⟨z,hz⟩ else 0

def parameterFrame (q : Intrinsic.ParameterPoint (A := A)) : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ :=
  Intrinsic.parameterPositionBlock B q * frameExtension B q.2

def parameterHalfDomain : Set (Intrinsic.ParameterPoint (A := A)) :=
  {q | q ∈ Intrinsic.parameterGraphDomain B ∧ (Intrinsic.parameterPositionBlock B q).det ∈ Complex.slitPlane}

def parameterHalfFrame (q : Intrinsic.ParameterPoint (A := A)) : ℂ :=
  halfFrameExtension B q.2 * Complex.sqrt (Intrinsic.parameterPositionBlock B q).det

theorem parameter_half_domain_open (hG : Adelic.DataTheta.GeometryIdentification B) : IsOpen (parameterHalfDomain B) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hs : Intrinsic.parameterBaseDomain (A := A) ∈ 𝓝 q :=
    (IntrinsicSmooth.IntrinsicSections.ballDomain_open.preimage continuous_snd).mem_nhds hq.1.1
  have hc : ContinuousAt (fun r => (Intrinsic.parameterPositionBlock B r).det) q :=
    ((AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM.matrix_determinant_holomorphic _
      (Intrinsic.parameter_position_holomorphic B hG)).differentiableAt hs).continuousAt
  exact inter_mem ((Intrinsic.parameter_graph_domain_open B hG).mem_nhds hq.1)
    (hc (Complex.isOpen_slitPlane.mem_nhds hq.2))

theorem parameter_half_domain_base (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    (IntrinsicCompactProjector.IntrinsicParameter.baseParameter A,z.val) ∈ parameterHalfDomain B := by
  refine ⟨Intrinsic.parameter_graph_domain_base B hG z,?_⟩
  rw [Intrinsic.parameter_position_base B hG z,Matrix.det_one]
  exact Complex.one_mem_slitPlane

theorem parameter_frame_base (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    parameterFrame B (IntrinsicCompactProjector.IntrinsicParameter.baseParameter A,z.val) = (B.frame z).val := by
  unfold parameterFrame frameExtension
  rw [Intrinsic.parameter_position_base B hG z,Matrix.one_mul]
  exact dite_eq_left (show z.val ∈ Adelic.BallGeometryData.ballDomain from z.property)

theorem parameter_half_base (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    parameterHalfFrame B (IntrinsicCompactProjector.IntrinsicParameter.baseParameter A,z.val) = B.halfFrame z := by
  unfold parameterHalfFrame halfFrameExtension
  rw [Intrinsic.parameter_position_base B hG z,Matrix.det_one,Complex.sqrt_one,mul_one]
  exact dite_eq_left (show z.val ∈ Adelic.BallGeometryData.ballDomain from z.property)

theorem parameter_half_square (hG : Adelic.DataTheta.GeometryIdentification B) (q : Intrinsic.ParameterPoint (A := A))
    (hq : q.2 ∈ Adelic.BallGeometryData.ballDomain) : (parameterHalfFrame B q) ^ 2 = (parameterFrame B q).det := by
  have hs : (Complex.sqrt (Intrinsic.parameterPositionBlock B q).det) ^ 2 = (Intrinsic.parameterPositionBlock B q).det :=
    Complex.cpow_ofNat_inv_pow _ 2
  unfold parameterHalfFrame parameterFrame halfFrameExtension frameExtension
  rw [mul_pow,hs,dite_eq_left hq,Matrix.det_mul,dite_eq_left hq,(hG.2.2.2.2.2.1 ⟨q.2,hq⟩).2]
  exact mul_comm _ _

theorem parameter_half_nonzero (hG : Adelic.DataTheta.GeometryIdentification B) (q : Intrinsic.ParameterPoint (A := A))
    (hq : q ∈ parameterHalfDomain B) : parameterHalfFrame B q ≠ 0 := by
  apply mul_ne_zero
  · change (if hz : q.2 ∈ Adelic.BallGeometryData.ballDomain then B.halfFrame ⟨q.2,hz⟩ else 0) ≠ 0
    rw [dite_eq_left hq.1.1]
    exact (hG.2.2.2.2.2.1 _).1
  · intro h
    have hs : (Complex.sqrt (Intrinsic.parameterPositionBlock B q).det) ^ 2 = (Intrinsic.parameterPositionBlock B q).det :=
      Complex.cpow_ofNat_inv_pow _ 2
    rw [h,zero_pow (by decide)] at hs
    exact hq.1.2 hs.symm

theorem parameter_half_holomorphic (hG : Adelic.DataTheta.GeometryIdentification B) :
    DifferentiableOn ℂ (parameterHalfFrame B) (parameterHalfDomain B) := by
  have hh : DifferentiableOn ℂ (fun q : Intrinsic.ParameterPoint (A := A) => halfFrameExtension B q.2)
      (parameterHalfDomain B) :=
    hG.2.2.2.2.1.comp differentiableOn_snd (fun _ h => h.1.1)
  have hd := (AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM.matrix_determinant_holomorphic _
    (Intrinsic.parameter_position_holomorphic B hG)).mono (show parameterHalfDomain B ⊆ Intrinsic.parameterBaseDomain (A := A)
      from fun _ h => h.1.1)
  exact hh.mul (Complex.differentiableOn_sqrt.comp hd (fun _ h => h.2))

end RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame

end

end OAI
