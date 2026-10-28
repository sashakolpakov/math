import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenPrincipal
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift

/-! # Supported Coefficient Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SupportedCoefficientComparison.Constructions

noncomputable section

/-! Exact normalization coefficients identify actual supported classes
on an analytic open retaining the corresponding scheme fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenPrincipal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]
  {r : X.left.functionField} (R : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left r) (hr : r ≠ 0)
  (U : Opens V.analyticSpace) (S : Set U)

/-- Only equality of the actual finite cycle coefficients is used here;
the relative classes are obtained from their canonical linear map. -/
theorem supportedClass_eq_normalized
    (c : Open.SupportedLift.Constructions.Map.SupportedCycle V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1))
    (hc : Open.SupportedLift.Constructions.Map.forgetCycle V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1) c = OpenPrincipal.Constructions.openPrincipalCycle V W a R)
    (hcover : ∀ C : Geometric.DimensionCycles.DimensionCycleSupport V (Geometric.DimensionCycles.dimensionCodimension V W + 1),
      (∃ x : U, x.val ∈ Set.range C.analyticInclusion) →
      ∀ y : (AmbientMap.Constructions.smoothNormalizationOver V W).left,
        (PrincipalBoundary.Constructions.fullAmbientMap V W).left y = IntersectionGeometry.supportPoint C.val → y ∈ Set.range a.left) :
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1) c =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1)
        (Open.SupportedLift.Constructions.restrictCycle V U S (Geometric.DimensionCycles.dimensionCodimension V W + 1)
          (Principal.Constructions.normalizedPrincipalCycle V W (OpenFunctionField.Constructions.originalFunction V W a r) (OpenFunctionField.Constructions.originalFunction_ne_zero V W a r hr))) := by
  apply Open.SupportedLift.Constructions.relativeClassMap_eq_restrict_of_local_coefficients
  intro C hC
  rw [hc, Principal.Constructions.normalizedPrincipalCycle_coefficient]
  exact OpenPrincipal.Constructions.openPrincipalCycle_original_coefficient V W a R hr C (hcover C hC)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SupportedCoefficientComparison.Constructions
