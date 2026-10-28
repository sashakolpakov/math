import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DolbeaultSurjection

/-! # Holomorphic Zero -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The actual dual period torus is the zero-integral-Chern subgroup
of the original native holomorphic unit cohomology. In particular every
homogeneous algebraic line bundle has an actual dual-torus parameter at
the holomorphic level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.holomorphicPicardZero_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.holomorphicPicardZero_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
local instance PeriodModel.Geometric.AlgebraicPeriodModel.holomorphicPicardZero_unitCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1
local instance PeriodModel.Geometric.AlgebraicPeriodModel.holomorphicPicardZero_functionCohomologyGroup :
    AddCommGroup (CategoryTheory.Sheaf.H
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1
local instance PeriodModel.Geometric.AlgebraicPeriodModel.holomorphicPicardZero_integralCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.integralSheafCohomologyTwo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
  AbelianModuli.ReferenceFamily.Cech.Add.cechClassAddCommGroup (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))) 2

def PeriodModel.Geometric.AlgebraicPeriodModel.translationHolomorphicH1Equiv : DefinitionsIntegral.Tangent dim ≃+
    CategoryTheory.Sheaf.H
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 1 :=
  M.translationDolbeaultEquiv.toAddEquiv.trans
    (RepresentationTheory.Theta.Geometric.DolbeaultQuotient.dolbeaultOneClassEquiv (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationHolomorphicH1Equiv_exponential (a : DefinitionsIntegral.Tangent dim) :
    RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (M.translationHolomorphicH1Equiv a) = M.translationHolomorphicClass a := rfl

theorem PeriodModel.Geometric.AlgebraicPeriodModel.exists_translationClass_of_zeroChern
    (u : DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
    (hu : DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) u = 0) :
    ∃ a : DefinitionsIntegral.Tangent dim, M.translationHolomorphicClass a = u := by
  obtain ⟨v, hv⟩ := RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.exists_holomorphicH1_of_connecting_zero _ _ u hu
  refine ⟨M.translationHolomorphicH1Equiv.symm v, ?_⟩
  exact (M.translationHolomorphicH1Equiv_exponential (M.translationHolomorphicH1Equiv.symm v)).symm.trans
    ((congrArg (RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
      (M.translationHolomorphicH1Equiv.apply_symm_apply v)).trans hv)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.dualTorusHolomorphicHom_zeroChern (q : T.integralDualPeriodData.periodTorus) :
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)
      (M.dualTorusHolomorphicHom q) = 0 := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact M.translationHolomorphicClass_zeroChern a

def PeriodModel.Geometric.AlgebraicPeriodModel.dualTorusZeroHolomorphicHom : T.integralDualPeriodData.periodTorus →+
    (DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).ker where
  toFun q := ⟨M.dualTorusHolomorphicHom q, M.dualTorusHolomorphicHom_zeroChern q⟩
  map_zero' := Subtype.ext (map_zero M.dualTorusHolomorphicHom)
  map_add' a b := Subtype.ext (map_add M.dualTorusHolomorphicHom a b)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.dualTorusZeroHolomorphicHom_bijective : Function.Bijective M.dualTorusZeroHolomorphicHom := by
  constructor
  · intro a b h
    exact M.dualTorusHolomorphicHom_injective (congrArg Subtype.val h)
  · intro u
    obtain ⟨a, ha⟩ := M.exists_translationClass_of_zeroChern u.val u.property
    exact ⟨QuotientAddGroup.mk a, Subtype.ext ha⟩

def PeriodModel.Geometric.AlgebraicPeriodModel.dualTorusZeroHolomorphicEquiv : T.integralDualPeriodData.periodTorus ≃+
    (DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)).ker :=
  AddEquiv.ofBijective M.dualTorusZeroHolomorphicHom M.dualTorusZeroHolomorphicHom_bijective

theorem PeriodModel.Geometric.AlgebraicPeriodModel.homogeneousLineBundle_dual_holomorphic_parameter
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle M.abelian.toOver.left)
    (hL : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    ∃ q : T.integralDualPeriodData.periodTorus,
      M.dualTorusHolomorphicHom q = AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety L := by
  obtain ⟨a, ha⟩ := M.exists_translationClass_of_zeroChern (AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicLineClass.nativeHolomorphicLineClass M.abelian.variety L)
    (AbelianModuli.ReferenceFamily.Intrinsic.IntegralChernVanishing.homogeneousLineBundle_integralConnecting_eq_zero M.abelian L hL)
  exact ⟨QuotientAddGroup.mk a, ha⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
