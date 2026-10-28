import OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior

/-! # Intrinsic One Smooth -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicOneSmooth.Intrinsic

noncomputable section

/-! Real C-infinity regularity of the actual ThetaOneForms one-forms, obtained
directly from the native geometric tensors by a fixed continuous linear
projection. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K}

def oneProjection : Adelic.DataTheta.TaylorTensor (A := A) 1 →L[ℂ] IntrinsicExterior.Intrinsic.Cotangent :=
  ((ContinuousLinearMap.compL ℂ IntrinsicExterior.Intrinsic.Tangent (Adelic.BallGeometryData.FrameIndex A → ℂ) ℂ).flip
    (OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding (A := A))).comp
      (continuousMultilinearCurryFin1 ℂ (Adelic.BallGeometryData.FrameIndex A → ℂ) ℂ).toContinuousLinearEquiv.toContinuousLinearMap

theorem oneProjection_geometricTensor (B : Adelic.DataTheta.ComparisonData F H K A)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1)) (z : Adelic.BallNatural.Ball) :
    oneProjection (Adelic.DataTheta.geometricTensor B f 1 z) = OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f z := by
  apply ContinuousLinearMap.ext
  intro u
  change (continuousMultilinearCurryFin1 ℂ (Adelic.BallGeometryData.FrameIndex A → ℂ) ℂ
    (Adelic.DataTheta.geometricTensor B f 1 z)) (OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding (A := A) u) = _
  rw [continuousMultilinearCurryFin1_apply, OneFormsIntrinsicLattice.IntrinsicProjection.geometricTensor_one_apply,
    OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm_apply]
  rfl

theorem thetaOneForm_smooth (B : Adelic.DataTheta.ComparisonData F H K A)
    (hTheta : Adelic.DataTheta.Descent.ThetaConstruction B) (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1)) :
    Adelic.BallGeometryData.BallSmooth (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f) := by
  have hc := (oneProjection (A := A)).restrictScalars ℝ |>.contDiff.comp_contDiffOn
    (hTheta.2.2.2.2.2 f 1)
  apply hc.congr
  intro z hz
  simp only [Function.comp_apply, dite_eq_left hz]
  exact (oneProjection_geometricTensor B f ⟨z,hz⟩).symm

theorem wedge_smooth (a b : Adelic.BallNatural.Ball → IntrinsicExterior.Intrinsic.Cotangent) (ha : Adelic.BallGeometryData.BallSmooth a) (hb : Adelic.BallGeometryData.BallSmooth b) :
    Adelic.BallGeometryData.BallSmooth (fun z => IntrinsicExterior.Intrinsic.wedge (a z) (b z)) := by
  let e₀ : IntrinsicExterior.Intrinsic.Cotangent →L[ℝ] ℂ := (ContinuousLinearMap.apply ℂ ℂ (![1,0] : IntrinsicExterior.Intrinsic.Tangent)).restrictScalars ℝ
  let e₁ : IntrinsicExterior.Intrinsic.Cotangent →L[ℝ] ℂ := (ContinuousLinearMap.apply ℂ ℂ (![0,1] : IntrinsicExterior.Intrinsic.Tangent)).restrictScalars ℝ
  have ha₀ := e₀.contDiff.comp_contDiffOn ha
  have ha₁ := e₁.contDiff.comp_contDiffOn ha
  have hb₀ := e₀.contDiff.comp_contDiffOn hb
  have hb₁ := e₁.contDiff.comp_contDiffOn hb
  have hc := ((ha₀.mul hb₁).sub (ha₁.mul hb₀)).smul_const IntrinsicExterior.Intrinsic.area
  apply hc.congr
  intro z hz
  simp [hz, e₀, e₁, IntrinsicExterior.Intrinsic.wedge, IntrinsicExterior.Intrinsic.wedgeCoefficient]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicOneSmooth.Intrinsic
