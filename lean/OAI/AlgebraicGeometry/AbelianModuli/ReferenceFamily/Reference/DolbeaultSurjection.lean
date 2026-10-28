import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DolbeaultInjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousCovector

/-! # Dolbeault Surjection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

section

/-! The constructed complex-linear translation map fills the actual
native Dolbeault space. Both directions embed in the original finite
dimensional tangent space, so injectivity forces surjectivity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.dolbeaultSurjection_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.dolbeaultSurjection_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceHermitian : RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian →ₗ⋆[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian →ₗ[ℂ] ℂ :=
  (F.form.comp M.periodDifferential.symm.toLinearMap).compl₂ M.periodDifferential.symm.toLinearMap

theorem AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceHermitian_symm (a b : RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) :
    M.nativeReferenceHermitian b a = star (M.nativeReferenceHermitian a b) :=
  F.hermitian (M.periodDifferential.symm a) (M.periodDifferential.symm b)

theorem AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceHermitian_pos (a : RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ha : a ≠ 0) :
    0 < (M.nativeReferenceHermitian a a).re :=
  F.positive (M.periodDifferential.symm a)
    (fun h => ha (M.periodDifferential.symm.injective (h.trans M.periodDifferential.symm.map_zero.symm)))

def AlgebraicModel.ReferenceAlgebraicModel.referenceDolbeaultCoordinate :
    RepresentationTheory.Theta.Geometric.DolbeaultQuotient.DolbeaultOneSpace (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) →ₗ[ℂ] F.periodData.space :=
  M.periodDifferential.symm.toLinearMap.comp
    (Intrinsic.HomogeneousCovector.nativeDolbeaultHermitianCoordinate M.abelian M.nativeReferenceHermitian
      M.nativeReferenceHermitian_symm M.nativeReferenceHermitian_pos)

theorem AlgebraicModel.ReferenceAlgebraicModel.referenceDolbeaultCoordinate_injective : Function.Injective M.referenceDolbeaultCoordinate :=
  M.periodDifferential.symm.injective.comp
    (Intrinsic.HomogeneousCovector.nativeDolbeaultHermitianCoordinate_injective M.abelian M.nativeReferenceHermitian
      M.nativeReferenceHermitian_symm M.nativeReferenceHermitian_pos)

theorem AlgebraicModel.ReferenceAlgebraicModel.translationDolbeaultLinear_surjective : Function.Surjective M.translationDolbeaultLinear := by
  have hinj : Function.Injective (M.referenceDolbeaultCoordinate.comp M.translationDolbeaultLinear) :=
    M.referenceDolbeaultCoordinate_injective.comp M.translationDolbeaultLinear_injective
  have hsurj := LinearMap.surjective_of_injective hinj
  intro w
  obtain ⟨a, ha⟩ := hsurj (M.referenceDolbeaultCoordinate w)
  exact ⟨a, M.referenceDolbeaultCoordinate_injective ha⟩

def AlgebraicModel.ReferenceAlgebraicModel.translationDolbeaultEquiv : F.periodData.space ≃ₗ[ℂ]
    RepresentationTheory.Theta.Geometric.DolbeaultQuotient.DolbeaultOneSpace (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  LinearEquiv.ofBijective M.translationDolbeaultLinear
    ⟨M.translationDolbeaultLinear_injective, M.translationDolbeaultLinear_surjective⟩

end

/-! The actual dual period torus is the zero-integral-Chern subgroup
of the original native holomorphic unit cohomology. In particular every
homogeneous algebraic line bundle has an actual dual-torus parameter at
the holomorphic level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : AlgebraicModel.ReferenceAlgebraicModel F hP)

local instance AlgebraicModel.ReferenceAlgebraicModel.holomorphicPicardZero_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance AlgebraicModel.ReferenceAlgebraicModel.holomorphicPicardZero_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance AlgebraicModel.ReferenceAlgebraicModel.holomorphicPicardZero_unitCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1
local instance AlgebraicModel.ReferenceAlgebraicModel.holomorphicPicardZero_functionCohomologyGroup :
    AddCommGroup (CategoryTheory.Sheaf.H
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1
local instance AlgebraicModel.ReferenceAlgebraicModel.holomorphicPicardZero_integralCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.integralSheafCohomologyTwo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))) 2

def AlgebraicModel.ReferenceAlgebraicModel.translationHolomorphicH1Equiv : F.periodData.space ≃+
    CategoryTheory.Sheaf.H
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1 :=
  M.translationDolbeaultEquiv.toAddEquiv.trans
    (RepresentationTheory.Theta.Geometric.DolbeaultQuotient.dolbeaultOneClassEquiv (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))

theorem AlgebraicModel.ReferenceAlgebraicModel.translationHolomorphicH1Equiv_exponential (a : F.periodData.space) :
    RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (M.translationHolomorphicH1Equiv a) = M.translationHolomorphicClass a := rfl

theorem AlgebraicModel.ReferenceAlgebraicModel.exists_translationClass_of_zeroChern
    (u : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (hu : DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) u = 0) :
    ∃ a : F.periodData.space, M.translationHolomorphicClass a = u := by
  obtain ⟨v, hv⟩ := RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.exists_holomorphicH1_of_connecting_zero _ _ u hu
  refine ⟨M.translationHolomorphicH1Equiv.symm v, ?_⟩
  exact (M.translationHolomorphicH1Equiv_exponential (M.translationHolomorphicH1Equiv.symm v)).symm.trans
    ((congrArg (RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
      (M.translationHolomorphicH1Equiv.apply_symm_apply v)).trans hv)

theorem AlgebraicModel.ReferenceAlgebraicModel.dualTorusHolomorphicHom_zeroChern (q : (F.dualPeriodData hP).periodTorus) :
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (M.dualTorusHolomorphicHom q) = 0 := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact M.translationHolomorphicClass_zeroChern a

def AlgebraicModel.ReferenceAlgebraicModel.dualTorusZeroHolomorphicHom : (F.dualPeriodData hP).periodTorus →+
    (DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).ker where
  toFun q := ⟨M.dualTorusHolomorphicHom q, M.dualTorusHolomorphicHom_zeroChern q⟩
  map_zero' := Subtype.ext (map_zero M.dualTorusHolomorphicHom)
  map_add' a b := Subtype.ext (map_add M.dualTorusHolomorphicHom a b)

theorem AlgebraicModel.ReferenceAlgebraicModel.dualTorusZeroHolomorphicHom_bijective : Function.Bijective M.dualTorusZeroHolomorphicHom := by
  constructor
  · intro a b h
    exact M.dualTorusHolomorphicHom_injective (congrArg Subtype.val h)
  · intro u
    obtain ⟨a, ha⟩ := M.exists_translationClass_of_zeroChern u.val u.property
    exact ⟨QuotientAddGroup.mk a, Subtype.ext ha⟩

def AlgebraicModel.ReferenceAlgebraicModel.dualTorusZeroHolomorphicEquiv : (F.dualPeriodData hP).periodTorus ≃+
    (DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).ker :=
  AddEquiv.ofBijective M.dualTorusZeroHolomorphicHom M.dualTorusZeroHolomorphicHom_bijective

theorem AlgebraicModel.ReferenceAlgebraicModel.homogeneousLineBundle_dual_holomorphic_parameter
    (L : HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    ∃ q : (F.dualPeriodData hP).periodTorus,
      M.dualTorusHolomorphicHom q = Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety L := by
  obtain ⟨a, ha⟩ := M.exists_translationClass_of_zeroChern (Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety L)
    (Intrinsic.IntegralChernVanishing.homogeneousLineBundle_integralConnecting_eq_zero M.abelian L hL)
  exact ⟨QuotientAddGroup.mk a, ha⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
