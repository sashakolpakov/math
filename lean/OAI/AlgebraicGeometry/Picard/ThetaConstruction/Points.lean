import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DescendedHolomorphicUniversality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicFaithfulness

/-! # Points -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Every homogeneous algebraic line bundle on the ThetaConstruction algebraic model
is an actual fiber of the descended theta family, up to algebraic sheaf
isomorphism, at one unique complex point of the constructed dual model.
The assertion here is about complex points; relative universality over
arbitrary test schemes remains a separate step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicFaithfulness

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

local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.algebraicPicardPoints_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.algebraicPicardPoints_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.algebraicPicardPoints_integralCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.integralSheafCohomologyTwo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))) 2

include hdeg hf hg recover in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.existsUnique_descendedThetaAlgebraicFiber
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety L) = 0) :
    ∃! x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver,
      Nonempty ((AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine Q x).sheaf ≅ L.sheaf) := by
  obtain ⟨x, hx, huniq⟩ := p.existsUnique_descendedThetaHolomorphicClass U V hdeg f g hf hg Q recover _ hL
  refine ⟨x, AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicFaithfulness.lineBundles_iso_of_nativeHolomorphicClass_eq M.abelian.variety _ L hx, ?_⟩
  intro y hy
  obtain ⟨e⟩ := hy
  exact huniq y (AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass.nativeHolomorphicLineClass_iso M.abelian.variety _ L e)

include hdeg hf hg recover in
theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.homogeneousLineBundle_unique_algebraic_parameter
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    ∃! x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver,
      Nonempty ((AbelianModuli.ReferenceFamily.IntrinsicPointLine.nativePointFamilyLine Q x).sheaf ≅ L.sheaf) :=
  p.existsUnique_descendedThetaAlgebraicFiber U V hdeg f g hf hg Q recover L
    (AbelianModuli.ReferenceFamily.Intrinsic.IntegralChernVanishing.homogeneousLineBundle_integralConnecting_eq_zero M.abelian L hL)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
