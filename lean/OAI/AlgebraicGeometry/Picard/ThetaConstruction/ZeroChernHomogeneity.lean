import OAI.AlgebraicGeometry.Picard.ThetaConstruction.Points
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualDifferenceDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPointLine

/-! # Zero Chern Homogeneity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ZeroChernHomogeneity.Geometric.AlgebraicPeriodModel

noncomputable section

/-! A line bundle with zero native integral Chern obstruction on the
actual algebraic period model is homogeneous on every test scheme.
The proof constructs its algebraic parameter in the descended theta
family and transports the family's proved homogeneity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPointLine

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.zeroChern_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.zeroChern_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

local instance : AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.integralSheafCohomologyTwo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))) 2

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.zeroIntegralChern_homogeneous (hE : E.transpose = -E)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety L) = 0) :
    AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass M.abelianScheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
  obtain ⟨N, ⟨p⟩⟩ := IntegralDualIsogenyKernel.Geometric.exists_integralDualLatticeIsogeny M
  obtain ⟨U, V, jU, jV, Q, _hpos, hdeg, _hjU, _hjV, heU, heV, _hamp, _hcube, _hpair,
    hQ, ⟨recover⟩, _eN, _eM⟩ := p.exists_normalized_homogeneous_primitive_difference hE
  obtain ⟨x, hx, _hunique⟩ :=
    p.existsUnique_descendedThetaAlgebraicFiber U V hdeg jU jV heU heV Q recover L hL
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine Q x) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L :=
    Quotient.sound hx
  have hf : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily M.abelianScheme (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Q.pullback (x ⊗ₘ 𝟙 M.abelianScheme.scheme).left) :=
    (congrArg (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) M.abelianScheme.scheme).left) hc).symm.trans
      (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine_constant_recovery Q x)
  change M.abelianScheme.IsHomogeneousPicardClass (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) _
  rw [hf]
  exact hQ.pullback M.abelianScheme x

theorem _root_.OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel.Geometric.AlgebraicPeriodModel.homogeneous_iff_zeroIntegralChern (hE : E.transpose = -E)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left) :
    AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass M.abelianScheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) ↔
      DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) (AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety L) = 0 :=
  ⟨AbelianModuli.ReferenceFamily.Intrinsic.IntegralChernVanishing.homogeneousLineBundle_integralConnecting_eq_zero M.abelian L,
    M.zeroIntegralChern_homogeneous hE L⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ZeroChernHomogeneity.Geometric.AlgebraicPeriodModel
