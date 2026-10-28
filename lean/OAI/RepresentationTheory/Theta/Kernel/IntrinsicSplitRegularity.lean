import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitFactorization
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicOneSmooth
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth

/-! # Intrinsic Split Regularity -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitRegularity.Intrinsic

noncomputable section

/-! Smooth split top-form sections and nonvanishing, with regularity and
spanning derived from the native theta constructions. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitTensor.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitWedge.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitFactorization.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicOneSmooth.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSmooth.IntrinsicSections

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))

theorem splitTopForm_smooth (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) : Adelic.BallGeometryData.BallSmooth (IntrinsicSplitTensor.Intrinsic.splitTopForm B₁ B₂ f) := by
  obtain ⟨n,a,b,_,hform⟩ := IntrinsicSplitFactorization.Intrinsic.finite_wedge_factorization B₁ B₂ hE₁ hE₂ hTensorDecomposition hΘ₁ hΘ₂ f
  have hs (j : Fin n) : Adelic.BallGeometryData.BallSmooth (fun z =>
      IntrinsicExterior.Intrinsic.wedge (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₁ (a j) z)
        (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₂ (b j) z)) :=
    IntrinsicOneSmooth.Intrinsic.wedge_smooth _ _ (IntrinsicOneSmooth.Intrinsic.thetaOneForm_smooth B₁ hΘ₁ (a j)) (IntrinsicOneSmooth.Intrinsic.thetaOneForm_smooth B₂ hΘ₂ (b j))
  have hsum := ContDiffOn.sum (fun j (_ : j ∈ Finset.univ) => hs j)
  apply hsum.congr
  intro z hz
  simp only [dite_eq_left hz]
  exact hform ⟨z,hz⟩

def splitTopSection (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) : IntrinsicSmooth.IntrinsicSections.SmoothSection IntrinsicExterior.Intrinsic.TopCovector :=
  ⟨IntrinsicSplitTensor.Intrinsic.splitTopForm B₁ B₂ f, splitTopForm_smooth B₁ B₂ hE₁ hE₂ hTensorDecomposition hΘ₁ hΘ₂ f⟩

theorem splitTopForm_nonzero (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂) (z : Adelic.BallNatural.Ball) :
    ∃ f : Adelic.FiniteSchwartz.finiteSchwartz F 6, IntrinsicSplitTensor.Intrinsic.splitTopForm B₁ B₂ f z ≠ 0 := by
  obtain ⟨f₁,f₂,hne⟩ := IntrinsicExterior.Intrinsic.spanning_wedge_nonzero
    (fun f : Adelic.FiniteSchwartz.finiteSchwartz F 3 => OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₁ f z)
    (fun f : Adelic.FiniteSchwartz.finiteSchwartz F 3 => OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B₂ f z)
    (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm_span B₁ hG₁ hΘ₁ z)
    (OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm_span B₂ hG₂ hΘ₂ z)
  refine ⟨IntrinsicSchwartz.Intrinsic.productInput F 3 3 f₁ f₂, ?_⟩
  rw [IntrinsicSplitWedge.Intrinsic.splitTopForm_product B₁ B₂ hE₁ hE₂ hΘ₁ hΘ₂]
  exact hne

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitRegularity.Intrinsic
