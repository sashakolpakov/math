import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.MarkedLevel
import OAI.RepresentationTheory.Theta.Geometric.Torus.Derivative

/-! # Model Derivative -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelDerivative.ReferenceAlgebraicModel

noncomputable section

/-! The derivative of the actual algebraic period uniformization is an
isomorphism and intertwines the algebraic integral CM endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.vectorPeriod (t : F.periodData.space) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver :=
  M.period (QuotientAddGroup.mk t)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.vectorPeriod_contMDiff : ContMDiff 𝓘(ℂ, F.periodData.space)
    𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) ∞ M.vectorPeriod :=
  M.period.contMDiff.comp F.periodData.periodProjection_contMDiff

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.vectorPeriod_zero : M.vectorPeriod 0 = 1 := by
  exact congrArg Additive.toMul M.periodAddEquiv.map_zero

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.vectorPeriod_mfderiv (t : F.periodData.space) :
    mfderiv 𝓘(ℂ, F.periodData.space) 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      M.vectorPeriod t =
      mfderiv 𝓘(ℂ, F.periodData.space) 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
        M.period (QuotientAddGroup.mk t) := by
  have h := mfderiv_comp t
    (M.period.contMDiff.mdifferentiableAt (x := QuotientAddGroup.mk t) (by simp))
    (F.periodData.periodProjection_contMDiff.mdifferentiableAt (x := t) (by simp))
  rw [F.periodData.periodProjection_mfderiv] at h
  exact h

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.periodDifferential : F.periodData.space ≃L[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian :=
  (M.period.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
    (x := (0 : F.periodData.periodTorus)) (by trivial)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.periodDifferential_eq : M.periodDifferential.toContinuousLinearMap =
    mfderiv 𝓘(ℂ, F.periodData.space) 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      M.vectorPeriod 0 := by
  rw [M.vectorPeriod_mfderiv]
  rfl

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.actionDifferential (a : NumberField.RingOfIntegers E) :
    RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian →L[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian :=
  mfderiv 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a))) 1

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.vectorPeriod_action (a : NumberField.RingOfIntegers E)
    (t : F.periodData.space) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) (M.vectorPeriod t) =
      M.vectorPeriod (F.action a t) :=
  M.period_action a (QuotientAddGroup.mk t)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel.periodDifferential_action (a : NumberField.RingOfIntegers E)
    (t : F.periodData.space) :
    M.actionDifferential a (M.periodDifferential t) =
      M.periodDifferential (F.action a t) := by
  let f := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a))
  let r : F.periodData.space →L[ℂ] F.periodData.space :=
    LinearMap.toContinuousLinearMap (F.action a)
  have hf : MDifferentiable 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) f :=
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (AbelianScheme.TateComparison.End.endSchemeMap M.abelian.toOver (M.functorAction a)) ∞).mdifferentiable
      (by simp)
  have hl := mfderiv_comp (0 : F.periodData.space)
    (hf (M.vectorPeriod 0)) (M.vectorPeriod_contMDiff.mdifferentiableAt (by simp))
  have hr := mfderiv_comp (0 : F.periodData.space)
    (M.vectorPeriod_contMDiff.mdifferentiableAt (x := r 0) (by simp))
    r.differentiableAt.mdifferentiableAt
  have he : f ∘ M.vectorPeriod = M.vectorPeriod ∘ r := funext (M.vectorPeriod_action a)
  rw [he, hr, M.vectorPeriod_zero, map_zero, r.mfderiv_eq] at hl
  have ht := congrArg (fun l => l t) hl
  have hp (u : F.periodData.space) :=
    congrArg (fun l => l u) M.periodDifferential_eq
  exact (congrArg (M.actionDifferential a) (hp t)).trans
    (ht.symm.trans (hp (F.action a t)).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ModelDerivative.ReferenceAlgebraicModel
