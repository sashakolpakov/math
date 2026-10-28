import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DescendedHolomorphicUniversality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicFaithfulness

/-! # Picard Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Every homogeneous algebraic line bundle on the reference model
is an actual fiber of the descended theta family, up to algebraic sheaf
isomorphism, at one unique complex point of the constructed dual model.
The assertion here is about complex points; relative universality over
arbitrary test schemes remains a separate step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : IsogenyKernel.ReferenceLatticeIsogeny M D)
    (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP)) (hdeg : V.degree = U.degree + 1)
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))
    (Q : HilbertConstruction.Line.Bundles.LineBundle (D.abelianScheme.scheme ⊗ M.abelianScheme.scheme).left)
    (recover : (Q.pullback (p.isogeny.hom ⊗ₘ 𝟙 M.abelianScheme.scheme).left).sheaf ≅
      (RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle.abelianDifferenceBundle M.abelianScheme (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)).sheaf)

local instance IsogenyKernel.ReferenceLatticeIsogeny.algebraicPicardPoints_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance IsogenyKernel.ReferenceLatticeIsogeny.algebraicPicardPoints_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance IsogenyKernel.ReferenceLatticeIsogeny.algebraicPicardPoints_integralCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.integralSheafCohomologyTwo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))) 2

include hdeg hf hg recover in
theorem IsogenyKernel.ReferenceLatticeIsogeny.existsUnique_descendedThetaAlgebraicFiber
    (L : HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety L) = 0) :
    ∃! x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver,
      Nonempty ((IntrinsicPointLine.nativePointFamilyLine Q x).sheaf ≅ L.sheaf) := by
  obtain ⟨x, hx, huniq⟩ := p.existsUnique_descendedThetaHolomorphicClass U V hdeg f g hf hg Q recover _ hL
  refine ⟨x, Intrinsic.HolomorphicFaithfulness.lineBundles_iso_of_nativeHolomorphicClass_eq M.abelian.variety _ L hx, ?_⟩
  intro y hy
  obtain ⟨e⟩ := hy
  exact huniq y (Intrinsic.HolomorphicIsoClass.nativeHolomorphicLineClass_iso M.abelian.variety _ L e)

include hdeg hf hg recover in
theorem IsogenyKernel.ReferenceLatticeIsogeny.homogeneousLineBundle_unique_algebraic_parameter
    (L : HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    ∃! x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver,
      Nonempty ((IntrinsicPointLine.nativePointFamilyLine Q x).sheaf ≅ L.sheaf) :=
  p.existsUnique_descendedThetaAlgebraicFiber U V hdeg f g hf hg Q recover L
    (Intrinsic.IntegralChernVanishing.homogeneousLineBundle_integralConnecting_eq_zero M.abelian L hL)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
