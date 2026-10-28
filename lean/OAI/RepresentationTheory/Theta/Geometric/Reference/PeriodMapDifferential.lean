import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.MarkedAction

/-! # Period Map Differential -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.PeriodMapDifferential

noncomputable section

/-! A map between the actual reference period models has the derivative
and rational-period action specified by its original vector-period formula. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P z} {G : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    (M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (N : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel G hP)
    (f : M.abelian.toOver ⟶ N.abelian.toOver) [IsMonHom f]
    (u : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceTangent s →ₗ[ℂ] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceTangent s)

local instance : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance : IsIntegral N.abelian.toOver.left := N.abelian.variety.property
local instance : Smooth N.abelian.toOver.hom := N.abelian.variety.presentation.smooth

theorem reference_vectorPeriod_derivative
    (he : ∀ v : F.periodData.space,
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.vectorPeriod v) = N.vectorPeriod (u v))
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceTangent s) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicLinearMaps.linearLift f (M.periodDifferential v) = N.periodDifferential (u v) := by
  let g := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f
  let r : F.periodData.space →L[ℂ] G.periodData.space := u.toContinuousLinearMap
  have hg : MDifferentiable 𝓘(ℂ, AlgebraicAction.AbelianModel M.abelian) 𝓘(ℂ, AlgebraicAction.AbelianModel N.abelian) g :=
    (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map f ∞).mdifferentiable (by simp)
  have hl := mfderiv_comp (0 : F.periodData.space)
    (hg (M.vectorPeriod 0)) (M.vectorPeriod_contMDiff.mdifferentiableAt (by simp))
  have hr := mfderiv_comp (0 : F.periodData.space)
    (N.vectorPeriod_contMDiff.mdifferentiableAt (x := r 0) (by simp))
    r.differentiableAt.mdifferentiableAt
  have he' : g ∘ M.vectorPeriod = N.vectorPeriod ∘ r := funext he
  rw [he', hr, M.vectorPeriod_zero, map_zero, r.mfderiv_eq] at hl
  have hv := congrArg (fun l => l v) hl
  have hs := congrArg (fun l => l v) M.periodDifferential_eq
  have ht := congrArg (fun l => l (u v)) N.periodDifferential_eq
  have hf := congrArg (fun L : AlgebraicAction.AbelianModel M.abelian →ₗ[ℂ] AlgebraicAction.AbelianModel N.abelian =>
    L (M.periodDifferential v)) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LiftDifferential.IntrinsicLinearMaps.linearLift_eq_nativeDifferential f)
  exact hf.trans ((congrArg
    (mfderiv 𝓘(ℂ, AlgebraicAction.AbelianModel M.abelian) 𝓘(ℂ, AlgebraicAction.AbelianModel N.abelian) g 1) hs).trans
      (hv.symm.trans ht.symm))

theorem reference_rationalPeriod_action
    (he : ∀ v : F.periodData.space,
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.vectorPeriod v) = N.vectorPeriod (u v))
    (t : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hu : ∀ v, u (F.periodEmbedding v) = G.periodEmbedding (t v)) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f (M.nativeReferenceMarking v) = N.nativeReferenceMarking (t v) := by
  apply Subtype.ext
  exact (reference_vectorPeriod_derivative M N f u he (F.periodEmbedding v)).trans
    (congrArg N.periodDifferential (hu v))

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.PeriodMapDifferential
