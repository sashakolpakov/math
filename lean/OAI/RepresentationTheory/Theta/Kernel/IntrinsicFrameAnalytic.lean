import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPeriodAnalytic
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSquareRootAnalytic
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph

/-! # Intrinsic Frame Analytic -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicFrameAnalytic.Intrinsic

/-! Local ambient analyticity of the native frame and its given half
frame. The half-frame branch follows from its actual continuous value
and determinant square, not from an assumed analytic branch. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Topology _root_.Matrix.Norms.Elementwise ContDiff

open Filter
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGeometricPolynomial.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicMatrixAnalytic.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPeriodAnalytic.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSquareRootAnalytic.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem frameExtension_analytic (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    ContDiffAt ℂ ⊤ (IntrinsicParameterGraph.IntrinsicHalfFrame.frameExtension B) z.val := by
  apply (IntrinsicGeometricPolynomial.Intrinsic.framePolynomial_analytic A B).contDiffAt.congr_of_eventuallyEq
  filter_upwards [IntrinsicSmooth.IntrinsicSections.ballDomain_open.mem_nhds (show z.val ∈ Adelic.BallGeometryData.ballDomain from z.property)] with w hw
  change (if hz : w ∈ Adelic.BallGeometryData.ballDomain then (B.frame ⟨w,hz⟩).val else 0) = IntrinsicGeometricPolynomial.Intrinsic.framePolynomial A B w
  rw [dite_eq_left hw]
  exact (IntrinsicGeometricPolynomial.Intrinsic.framePolynomial_ball A B hG ⟨w,hw⟩).symm

theorem halfFrameExtension_analytic (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    ContDiffAt ℂ ⊤ (IntrinsicParameterGraph.IntrinsicHalfFrame.halfFrameExtension B) z.val := by
  apply IntrinsicSquareRootAnalytic.Intrinsic.contDiffAt_of_square (D := fun w => (IntrinsicGeometricPolynomial.Intrinsic.framePolynomial A B w).det)
  · exact (hG.2.2.2.2.1.differentiableAt
      (IntrinsicSmooth.IntrinsicSections.ballDomain_open.mem_nhds (show z.val ∈ Adelic.BallGeometryData.ballDomain from z.property))).continuousAt
  · change (if hz : z.val ∈ Adelic.BallGeometryData.ballDomain then B.halfFrame ⟨z.val,hz⟩ else 0) ≠ 0
    rw [dite_eq_left (show z.val ∈ Adelic.BallGeometryData.ballDomain from z.property)]
    exact (hG.2.2.2.2.2.1 z).1
  · filter_upwards [IntrinsicSmooth.IntrinsicSections.ballDomain_open.mem_nhds (show z.val ∈ Adelic.BallGeometryData.ballDomain from z.property)] with w hw
    change (if hz : w ∈ Adelic.BallGeometryData.ballDomain then B.halfFrame ⟨w,hz⟩ else 0) ^ 2 = (IntrinsicGeometricPolynomial.Intrinsic.framePolynomial A B w).det
    rw [dite_eq_left hw,IntrinsicGeometricPolynomial.Intrinsic.framePolynomial_ball A B hG ⟨w,hw⟩]
    exact (hG.2.2.2.2.2.1 ⟨w,hw⟩).2
  · exact IntrinsicMatrixAnalytic.Intrinsic.matrix_determinant_contDiffAt _ (IntrinsicGeometricPolynomial.Intrinsic.framePolynomial_analytic A B).contDiffAt

end RepresentationTheory.Theta.Kernel.IntrinsicFrameAnalytic.Intrinsic

namespace RepresentationTheory.Theta.Kernel.IntrinsicFrameAnalytic.IntrinsicParameter

/-! Ambient analytic regularity of the explicit native compact-place
projector, period, Hodge frame, and half-determinant charts. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise ContDiff

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphCalculus.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicMatrixAnalytic.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPeriodAnalytic.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameAnalytic.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

theorem ambientParameter_analytic (w : Adelic.BallGeometryData.ComplexPhase A) :
    ContDiff ℂ ⊤ (fun q : IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A × IntrinsicExterior.Intrinsic.Tangent => IntrinsicCompactProjector.IntrinsicParameter.ambientParameter A q.1 q.2 w) := by
  apply contDiff_pi.mpr
  intro v
  by_cases hv : v = A.distinguished
  · simp only [IntrinsicCompactProjector.IntrinsicParameter.ambientParameter,ite_eq_left hv]
    apply ContDiff.prodMk
    · apply contDiff_pi.mpr
      rintro ⟨i,j⟩
      fin_cases i <;> dsimp [Adelic.DeterminantCoordinates.lineVector] <;> fun_prop
    · apply contDiff_pi.mpr
      rintro ⟨i,j⟩
      fin_cases i <;> dsimp [Adelic.DeterminantCoordinates.annihilatorVector] <;> fun_prop
  · simp only [IntrinsicCompactProjector.IntrinsicParameter.ambientParameter,ite_eq_right hv]
    apply ContDiff.prodMk
    all_goals
      apply contDiff_pi.mpr
      intro ij
      fun_prop

theorem coordinateProjector_analytic (B : Adelic.DataTheta.ComparisonData F H K A) :
    ContDiff ℂ ⊤ (fun q : IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A × IntrinsicExterior.Intrinsic.Tangent => IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B q.1 q.2) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_apply ℂ ℂ i).comp (B.complexPhase.symm.contDiff.comp (ambientParameter_analytic A _))

variable {A} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem parameter_position_analytic (hG : Adelic.DataTheta.GeometryIdentification B) (q : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A))
    (hq : q.2 ∈ Adelic.BallGeometryData.ballDomain) : ContDiffAt ℂ ⊤ (IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B) q := by
  have hP := (coordinateProjector_analytic A B).contDiffAt (x := q)
  have hZ : ContDiffAt ℂ ⊤ (fun r : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A) => IntrinsicParameterGraph.Intrinsic.periodExtension B r.2) q :=
    (IntrinsicPeriodAnalytic.Intrinsic.periodExtension_analytic B hG ⟨q.2,hq⟩).comp q contDiffAt_snd
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [IntrinsicParameterGraph.Intrinsic.parameterPositionBlock,IntrinsicGraphCalculus.Intrinsic.positionBlock,Matrix.add_apply,Matrix.mul_apply,Matrix.submatrix_apply]
  fun_prop

theorem parameter_momentum_analytic (hG : Adelic.DataTheta.GeometryIdentification B) (q : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A))
    (hq : q.2 ∈ Adelic.BallGeometryData.ballDomain) : ContDiffAt ℂ ⊤
      (fun r : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A) => IntrinsicGraphCalculus.Intrinsic.momentumBlock (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B r.1 r.2) (IntrinsicParameterGraph.Intrinsic.periodExtension B r.2)) q := by
  have hP := (coordinateProjector_analytic A B).contDiffAt (x := q)
  have hZ : ContDiffAt ℂ ⊤ (fun r : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A) => IntrinsicParameterGraph.Intrinsic.periodExtension B r.2) q :=
    (IntrinsicPeriodAnalytic.Intrinsic.periodExtension_analytic B hG ⟨q.2,hq⟩).comp q contDiffAt_snd
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [IntrinsicGraphCalculus.Intrinsic.momentumBlock,Matrix.add_apply,Matrix.mul_apply,Matrix.submatrix_apply]
  fun_prop

theorem parameter_period_analytic (hG : Adelic.DataTheta.GeometryIdentification B) (q : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A))
    (hq : q ∈ IntrinsicParameterGraph.Intrinsic.parameterGraphDomain B) : ContDiffAt ℂ ⊤ (IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B) q :=
  IntrinsicMatrixAnalytic.Intrinsic.matrix_product_contDiffAt _ _ (parameter_momentum_analytic B hG q hq.1)
    (IntrinsicMatrixAnalytic.Intrinsic.matrix_inverse_contDiffAt _ (parameter_position_analytic B hG q hq.1) hq.2)

theorem parameter_frame_analytic (hG : Adelic.DataTheta.GeometryIdentification B) (q : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A))
    (hq : q.2 ∈ Adelic.BallGeometryData.ballDomain) : ContDiffAt ℂ ⊤ (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B) q :=
  IntrinsicMatrixAnalytic.Intrinsic.matrix_product_contDiffAt _ _ (parameter_position_analytic B hG q hq)
    ((Intrinsic.frameExtension_analytic B hG ⟨q.2,hq⟩).comp q contDiffAt_snd)

theorem parameter_half_analytic (hG : Adelic.DataTheta.GeometryIdentification B) (q : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A))
    (hq : q ∈ IntrinsicParameterGraph.IntrinsicHalfFrame.parameterHalfDomain B) : ContDiffAt ℂ ⊤ (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterHalfFrame B) q := by
  have hh : ContDiffAt ℂ ⊤ (fun r : IntrinsicParameterGraph.Intrinsic.ParameterPoint (A := A) => IntrinsicParameterGraph.IntrinsicHalfFrame.halfFrameExtension B r.2) q :=
    (Intrinsic.halfFrameExtension_analytic B hG ⟨q.2,hq.1.1⟩).comp q contDiffAt_snd
  have hd := IntrinsicMatrixAnalytic.Intrinsic.matrix_determinant_contDiffAt _ (parameter_position_analytic B hG q hq.1.1)
  have hr : ContDiffAt ℂ ⊤ Complex.sqrt (IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B q).det :=
    (Complex.differentiableOn_sqrt.contDiffOn Complex.isOpen_slitPlane).contDiffAt
      (Complex.isOpen_slitPlane.mem_nhds hq.2)
  have hc : ContDiffAt ℂ ⊤ (fun r => Complex.sqrt (IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B r).det) q :=
    ContDiffAt.comp (f := fun r => (IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B r).det) (g := Complex.sqrt) q hr hd
  exact hh.mul hc

end RepresentationTheory.Theta.Kernel.IntrinsicFrameAnalytic.IntrinsicParameter

end

end OAI
