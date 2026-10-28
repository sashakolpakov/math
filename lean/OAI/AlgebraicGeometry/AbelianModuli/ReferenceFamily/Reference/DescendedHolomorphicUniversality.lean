import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DescendedHolomorphicClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DolbeaultSurjection

/-! # Descended Holomorphic Universality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Actual fibers of the descended algebraic theta family classify
the zero-integral-Chern native holomorphic classes, with unique complex
parameters. This is a holomorphic classification; algebraic and relative
Picard representability are separate assertions. -/

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

local instance IsogenyKernel.ReferenceLatticeIsogeny.descendedUniversality_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance IsogenyKernel.ReferenceLatticeIsogeny.descendedUniversality_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance IsogenyKernel.ReferenceLatticeIsogeny.descendedUniversality_dualIntegral : IsIntegral D.abelian.toOver.left := D.abelian.variety.property
local instance IsogenyKernel.ReferenceLatticeIsogeny.descendedUniversality_dualSmooth : Smooth D.abelian.toOver.hom := D.abelian.variety.presentation.smooth
local instance IsogenyKernel.ReferenceLatticeIsogeny.descendedUniversality_unitCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1
local instance IsogenyKernel.ReferenceLatticeIsogeny.descendedUniversality_integralCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.integralSheafCohomologyTwo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))) 2

include hdeg hf hg recover in
theorem IsogenyKernel.ReferenceLatticeIsogeny.descendedThetaHolomorphicClass_zeroChern (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver) :
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (IntrinsicPointLine.nativePointFamilyLine Q x)) = 0 := by
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (D.period.symm x)
  have hx : D.period (QuotientAddGroup.mk a) = x :=
    (congrArg D.period ha).trans (D.period.apply_symm_apply x)
  have hc := (congrArg (fun y => Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (IntrinsicPointLine.nativePointFamilyLine Q y))
    hx).symm.trans (p.descendedThetaHolomorphicClass_mk U V hdeg f g hf hg Q recover a)
  exact (congrArg (fun u : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology M.abelian.variety.analyticModel
    M.abelian.variety.analyticSpace =>
      DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) u)
        hc).trans (M.translationHolomorphicClass_zeroChern (-a))

include hdeg hf hg recover in
theorem IsogenyKernel.ReferenceLatticeIsogeny.existsUnique_descendedThetaHolomorphicClass
    (u : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (hu : DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) u = 0) :
    ∃! x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver,
      Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (IntrinsicPointLine.nativePointFamilyLine Q x) = u := by
  obtain ⟨a, ha⟩ := M.exists_translationClass_of_zeroChern u hu
  have hx : Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety
      (IntrinsicPointLine.nativePointFamilyLine Q (D.period (QuotientAddGroup.mk (-a)))) = u := by
    rw [p.descendedThetaHolomorphicClass_mk U V hdeg f g hf hg Q recover, neg_neg]
    exact ha
  refine ⟨D.period (QuotientAddGroup.mk (-a)), hx, ?_⟩
  intro y hy
  exact p.descendedThetaHolomorphicClass_injective U V hdeg f g hf hg Q recover (hy.trans hx.symm)

include hdeg hf hg recover in
theorem IsogenyKernel.ReferenceLatticeIsogeny.homogeneousLineBundle_unique_descended_holomorphic_parameter
    (L : HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    ∃! x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.abelian.toOver,
      Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety (IntrinsicPointLine.nativePointFamilyLine Q x) =
        Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety L :=
  p.existsUnique_descendedThetaHolomorphicClass U V hdeg f g hf hg Q recover _
    (Intrinsic.IntegralChernVanishing.homogeneousLineBundle_integralConnecting_eq_zero M.abelian L hL)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
