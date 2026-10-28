import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.TranslationOf
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicIsoClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.TranslationSub

/-! # Translation Class Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Exact native holomorphic class of the actual algebraic theta
translation difference. The minus sign follows from its frame gauges. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationClass_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationClass_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationClass_cohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationClass_nativeCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology M.abelian.variety.analyticModel M.abelian.variety.analyticSpace) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of M.abelian.variety.analyticSpace)
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf M.abelian.variety.analyticModel M.abelian.variety.analyticSpace) 1

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaTranslationDifference_class_add_eq_zero (hdeg : V.degree = U.degree + 1)
    (a : F.periodData.space) :
    (show DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) from
    Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety
      (((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback (M.thetaTranslationMap a).left).tensor
        (Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left)))) +
          M.translationHolomorphicClass a = 0 := by
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let W := M.thetaTranslationCover U V f g a
  let S := DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
  let : AddCommGroup (CategoryTheory.Sheaf.H S 1) := Cech.Add.cechClassAddCommGroup (X := T) S 1
  let k := M.thetaTranslationDifferenceCech U V f g a
  let l := M.thetaRefinedTranslationCech U V f g a
  have hk := M.thetaTranslationDifferenceCech_closed U V f g a
  have hl := M.thetaRefinedTranslationCech_closed U V f g a
  have hW := M.thetaTranslationCover_covers U V f g hf hg a
  have hsum := Cech.Add.cechAdd_closed (X := T) W S.obj 1 k l hk hl
  have hz := Intrinsic.HolomorphicIsoClass.holomorphicUnitCech_class_zero_of_trivialization (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) W hW (k + l) hsum
    (M.thetaTranslationGaugeUnit U V f g hf hg a) (by
      intro b q
      change (Holomorphic.LogUnitClass.holomorphicUnitSection (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection W b) (k b)).val q *
        (Holomorphic.LogUnitClass.holomorphicUnitSection (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
          (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection W b) (l b)).val q = _
      rw [M.thetaRefinedTranslationCech_value U V f g]
      exact M.thetaTranslationGaugeIdentity U V f g hf hg hdeg a b q)
  have ha := Cech.Add.cechSheafClass_add (X := T) W S (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := T) W hW) 0 k l hk hl
  have he := congrArg₂ (fun x y : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology
    (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) => x + y)
      (M.thetaTranslationDifferenceCech_class U V f g hf hg a)
      (M.thetaRefinedTranslationCech_class U V f g hf hg a)
  exact he.symm.trans (ha.symm.trans hz)

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaTranslationClass_eq_neg (hdeg : V.degree = U.degree + 1)
    (a : F.periodData.space) :
    Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety
      (((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback (M.thetaTranslationMap a).left).tensor
        (Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left))) =
          -M.translationHolomorphicClass a :=
  eq_neg_of_add_eq_zero_left (M.thetaTranslationDifference_class_add_eq_zero U V f g hf hg hdeg a)

include hf hg in
theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaTranslationClass_eq (hdeg : V.degree = U.degree + 1)
    (a : F.periodData.space) :
    Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety
      (((RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left).pullback (M.thetaTranslationMap a).left).tensor
        (Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual (RepresentationTheory.Theta.Geometric.AlgebraicQuotient.algebraicThetaQuotient f.left g.left))) =
          M.translationHolomorphicClass (-a) :=
  (M.nativeThetaTranslationClass_eq_neg U V f g hf hg hdeg a).trans
    (map_neg M.translationHolomorphicHom a).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
