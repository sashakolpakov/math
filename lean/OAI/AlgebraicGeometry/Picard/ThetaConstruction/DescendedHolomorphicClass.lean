import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PointClass
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DualHolomorphicInjection
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualIsogenyKernel

/-! # Descended Holomorphic Class -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Exact native holomorphic classes of the algebraically descended
theta family on the constructed dual model. -/

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

local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedHolomorphic_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedHolomorphic_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedHolomorphic_dualIntegral : IsIntegral D.abelian.toOver.left := D.abelian.variety.property
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedHolomorphic_dualSmooth : Smooth D.abelian.toOver.hom := D.abelian.variety.presentation.smooth
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedHolomorphic_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1

include hdeg hf hg recover in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedThetaHolomorphicClass_mk (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine Q (D.period (QuotientAddGroup.mk a))) =
      M.translationHolomorphicClass (-a) := by
  have hp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom (M.vectorPeriod a) = D.period (QuotientAddGroup.mk a) :=
    p.comparison (QuotientAddGroup.mk a)
  have hc := (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine_baseChange Q p.isogeny.hom (M.vectorPeriod a)).symm.trans
    (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine_congr _ _ recover (M.vectorPeriod a))
  rw [hp] at hc
  exact (congrArg (AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass.nativeHolomorphicPicardClass M.abelian.variety) hc).trans
    (M.thetaPointDifference_holomorphicClass U V f g hf hg hdeg a)

include hdeg hf hg recover in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedThetaHolomorphicClass (q : F.integralDualPeriodData.periodTorus) :
    AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine Q (D.period q)) =
      -M.dualTorusHolomorphicHom q := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact (p.descendedThetaHolomorphicClass_mk U V hdeg f g hf hg Q recover a).trans
    (map_neg M.translationHolomorphicHom a)

include hdeg hf hg recover in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.descendedThetaHolomorphicClass_injective :
    Function.Injective (fun x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver =>
      AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine Q x)) := by
  intro x y h
  apply D.period.symm.injective
  apply M.dualTorusHolomorphicHom_injective
  apply neg_injective
  have hx := p.descendedThetaHolomorphicClass U V hdeg f g hf hg Q recover (D.period.symm x)
  have hy := p.descendedThetaHolomorphicClass U V hdeg f g hf hg Q recover (D.period.symm y)
  rw [D.period.apply_symm_apply] at hx hy
  exact hx.symm.trans (h.trans hy)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
