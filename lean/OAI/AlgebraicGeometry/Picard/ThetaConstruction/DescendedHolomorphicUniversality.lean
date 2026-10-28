import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DescendedHolomorphicClass
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.HolomorphicZero

/-! # Descended Holomorphic Universality -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Actual fibers of the descended algebraic theta family classify
the zero-integral-Chern native holomorphic classes, with unique complex
parameters. This is a holomorphic classification; algebraic and relative
Picard representability are separate assertions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel F} {D : IntegralDualModel.Geometric.IntegralDualAlgebraicModel F}
    (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M D)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP)) (hdeg : V.degree = U.degree + 1)
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)).sheaf)

local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedUniversality_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedUniversality_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedUniversality_dualIntegral : IsIntegral D.abelian.toOver.left := D.abelian.variety.property
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedUniversality_dualSmooth : Smooth D.abelian.toOver.hom := D.abelian.variety.presentation.smooth
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedUniversality_unitCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedUniversality_integralCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.integralSheafCohomologyTwo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))) 2

include hdeg hf hg recover in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedThetaHolomorphicClass_zeroChern (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver) :
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine Q x)) = 0 := by
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (D.period.symm x)
  have hx : D.period (QuotientAddGroup.mk a) = x :=
    (congrArg D.period ha).trans (D.period.apply_symm_apply x)
  have hc := (congrArg (fun y => AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine Q y))
    hx).symm.trans (p.descendedThetaHolomorphicClass_mk U V hdeg f g hf hg Q recover a)
  exact (congrArg (fun u : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology M.abelian.variety.analyticModel
    M.abelian.variety.analyticSpace =>
      DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) u)
        hc).trans (M.translationHolomorphicClass_zeroChern (-a))

include hdeg hf hg recover in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.existsUnique_descendedThetaHolomorphicClass
    (u : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (hu : DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) u = 0) :
    ∃! x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver,
      AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine Q x) = u := by
  obtain ⟨a, ha⟩ := M.exists_translationClass_of_zeroChern u hu
  have hx : AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety
      (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine Q (D.period (QuotientAddGroup.mk (-a)))) = u := by
    exact (p.descendedThetaHolomorphicClass_mk U V hdeg f g hf hg Q recover (-a)).trans
      ((congrArg M.translationHolomorphicClass (neg_neg a)).trans ha)
  refine ⟨D.period (QuotientAddGroup.mk (-a)), hx, ?_⟩
  intro y hy
  exact p.descendedThetaHolomorphicClass_injective U V hdeg f g hf hg Q recover (hy.trans hx.symm)

include hdeg hf hg recover in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.homogeneousLineBundle_unique_descended_holomorphic_parameter
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    ∃! x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver,
      AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine Q x) =
        AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety L :=
  p.existsUnique_descendedThetaHolomorphicClass U V hdeg f g hf hg Q recover _
    (AbelianModuli.ReferenceFamily.Intrinsic.IntegralChernVanishing.homogeneousLineBundle_integralConnecting_eq_zero M.abelian L hL)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
