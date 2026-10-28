import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedCycleClass
import OAI.AlgebraicGeometry.CycleClass.Geometric.Span

/-! # Projective Cycle Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ProjectiveCycleClass.BundleCycles

noncomputable section

/-! On a projective variety the general supported class is the native
supported cycle class, with the same regular-locus normalization. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : AlgebraicGeometry.IsNoetherian V.toOver.left := inferInstanceAs (AlgebraicGeometry.IsNoetherian V.carrier)
local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints V.toOver) := inferInstanceAs (MetrizableSpace V.analyticSpace)

theorem schemeRegularSupportThomClass_projective :
    SupportedCycleClass.BundleCycles.schemeRegularSupportThomClass V.toOver Z.val p Z.dimension_add_codimension = Z.regularThomClass := by
  rfl

theorem schemeCycleSupportRestriction_projective :
    SupportedCycleClass.BundleCycles.schemeCycleSupportRestriction V.toOver Z.val p = Z.regularThomCohomologyRestriction (ModuleCat.of ℚ ℚ) (2 * p) := by
  rfl

theorem schemeSupportedCycleClass_projective :
    SupportedCycleClass.BundleCycles.schemeSupportedCycleClass V.toOver Z.val p Z.dimension_add_codimension = Z.rationalSupportedCycleClass := by
  apply Eq.symm
  apply SupportedCycleClass.BundleCycles.schemeSupportedCycleClass_unique V.toOver Z.val p Z.dimension_add_codimension
  exact (ConcreteCategory.congr_hom (schemeCycleSupportRestriction_projective V p Z) Z.rationalSupportedCycleClass).trans
    (Z.rationalSupportedCycleClass_regularPullback.trans (schemeRegularSupportThomClass_projective V p Z).symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ProjectiveCycleClass.BundleCycles
