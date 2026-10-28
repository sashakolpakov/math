import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationTheta
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationDolbeaultSub

/-! # Translation Class Comparison -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Exact native holomorphic class of the actual algebraic theta
translation difference. The minus sign follows from its frame gauges. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix} {hP : matrix.transpose = -matrix}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel F) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationClass_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationClass_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationClass_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1
local instance PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationClass_nativeCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology M.abelian.variety.analyticModel M.abelian.variety.analyticSpace) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of M.abelian.variety.analyticSpace)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf M.abelian.variety.analyticModel M.abelian.variety.analyticSpace) 1

include hf hg in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.thetaTranslationDifference_class_add_eq_zero (hdeg : V.degree = U.degree + 1)
    (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    (show DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) from
    AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety
      (((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback (M.thetaTranslationMap a).left).tensor
        (Homomorphisms.LineBundleDual.Construction.lineBundleDual (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)))) +
          M.translationHolomorphicClass a = 0 := by
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let W := M.thetaTranslationCover U V f g a
  let S := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let : AddCommGroup (CategoryTheory.Sheaf.H S 1) := AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := T) S 1
  let k := M.thetaTranslationDifferenceCech U V f g a
  let l := M.thetaRefinedTranslationCech U V f g a
  have hk := M.thetaTranslationDifferenceCech_closed U V f g a
  have hl := M.thetaRefinedTranslationCech_closed U V f g a
  have hW := M.thetaTranslationCover_covers U V f g hf hg a
  have hsum := AbelianModuli.ReferenceFamily.Cech.Add.cechAdd_closed (X := T) W S.obj 1 k l hk hl
  have hz := AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass.holomorphicUnitCech_class_zero_of_trivialization (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) W hW (k + l) hsum
    (M.thetaTranslationGaugeUnit U V f g hf hg a) (by
      intro b q
      change (AbelianModuli.ReferenceFamily.Holomorphic.LogUnitClass.holomorphicUnitSection (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection W b) (k b)).val q *
        (AbelianModuli.ReferenceFamily.Holomorphic.LogUnitClass.holomorphicUnitSection (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
          (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection W b) (l b)).val q = _
      rw [M.thetaRefinedTranslationCech_value U V f g]
      exact M.thetaTranslationGaugeIdentity U V f g hf hg hdeg a b q)
  have ha := AbelianModuli.ReferenceFamily.Cech.Add.cechSheafClass_add (X := T) W S (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := T) W hW) 0 k l hk hl
  have he := congrArg₂ (fun x y : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology
    (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) => x + y)
      (M.thetaTranslationDifferenceCech_class U V f g hf hg a)
      (M.thetaRefinedTranslationCech_class U V f g hf hg a)
  exact he.symm.trans (ha.symm.trans hz)

include hf hg in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaTranslationClass_eq_neg (hdeg : V.degree = U.degree + 1)
    (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety
      (((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback (M.thetaTranslationMap a).left).tensor
        (Homomorphisms.LineBundleDual.Construction.lineBundleDual (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left))) =
          -M.translationHolomorphicClass a :=
  eq_neg_of_add_eq_zero_left (M.thetaTranslationDifference_class_add_eq_zero U V f g hf hg hdeg a)

include hf hg in
theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativeThetaTranslationClass_eq (hdeg : V.degree = U.degree + 1)
    (a : (ProjectivePeriodData.Geometric.projectivePeriodData F).space) :
    AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety
      (((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback (M.thetaTranslationMap a).left).tensor
        (Homomorphisms.LineBundleDual.Construction.lineBundleDual (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left))) =
          M.translationHolomorphicClass (-a) :=
  (M.nativeThetaTranslationClass_eq_neg U V f g hf hg hdeg a).trans
    (map_neg M.translationHolomorphicHom a).symm

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
