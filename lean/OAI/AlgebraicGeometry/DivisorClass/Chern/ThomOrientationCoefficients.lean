import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.OrientationCoefficients
import OAI.AlgebraicGeometry.CycleClass.Geometric.RegularThom

/-! # Thom Orientation Coefficients -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ThomOrientationCoefficients

noncomputable section

/-!
# ChernClass: the original global Thom group has its actual locally constant coefficients

The original regular Thom section trivializes its cohomology sheaf along
the actual regular support. Its proved stalk normalization discharges the
basis premise in the sheaf gluing equivalence. No trace comparison is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

def regularThomOrientationStalkIso (x : Z.regularAnalyticSpace) :
    (Z.regularThomSheafComplex.homology (2 * p)).presheaf.stalk
      (Z.regularComplementInclusion x) ≅ ModuleCat.of ℚ ℚ :=
  (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso Z.regularThomSheafComplex
    (Z.regularComplementInclusion x) (2 * p)).symm ≪≫ Z.regularThomStalkNormalIso x

theorem regularThomOrientationSection_normalization (x : Z.regularAnalyticSpace) :
    Sheaf.OrientationCoefficients.sheafOrientationCoefficient (Z.regularThomSheafComplex.homology (2 * p))
      Z.regularComplementInclusion (regularThomOrientationStalkIso Z)
      (Z.regularThomFirstCohomologyIso.hom Z.regularThomClass) x = 1 :=
  Z.regularThomClass_normalization x

theorem regularThomOrientationStalk_zero (y : Z.regularAmbientSpace)
    (hy : y ∉ Set.range Z.regularComplementInclusion) :
    IsZero ((Z.regularThomSheafComplex.homology (2 * p)).presheaf.stalk y) :=
  CycleClass.Geometric.SupportStalkVanishes.Cycles.supportedSingularSheaf_cohomologySheaf_stalk_isZero_of_mem
    (X := TopCat.of Z.regularAmbientSpace) (ModuleCat.of ℚ ℚ)
    Z.regularThomComplementOpen y hy (2 * p)

def regularThomCoefficientsEquiv : Z.regularThomGroup ≃ₗ[ℚ]
    LocallyConstant Z.regularAnalyticSpace ℚ :=
  Z.regularThomFirstCohomologyIso.toLinearEquiv.trans
    (Sheaf.OrientationCoefficients.sheafOrientationCoefficientsEquiv (Z.regularThomSheafComplex.homology (2 * p))
      Z.regularComplementInclusion (regularThomOrientationStalkIso Z)
      (Z.regularThomFirstCohomologyIso.hom Z.regularThomClass)
      (regularThomOrientationSection_normalization Z)
      Z.isClosedEmbedding_regularComplementInclusion (regularThomOrientationStalk_zero Z))

theorem regularThomCoefficientsEquiv_apply (a : Z.regularThomGroup)
    (x : Z.regularAnalyticSpace) :
    regularThomCoefficientsEquiv Z a x = Z.regularThomLocalCoefficient x a := rfl

theorem regularThomCoefficientsEquiv_thom :
    regularThomCoefficientsEquiv Z Z.regularThomClass = 1 := by
  apply LocallyConstant.ext
  intro x
  exact Z.regularThomClass_normalization x

theorem regularThomLocalCoefficient_locallyConstant (a : Z.regularThomGroup) :
    IsLocallyConstant (fun x => Z.regularThomLocalCoefficient x a) :=
  (regularThomCoefficientsEquiv Z a).isLocallyConstant

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ThomOrientationCoefficients
