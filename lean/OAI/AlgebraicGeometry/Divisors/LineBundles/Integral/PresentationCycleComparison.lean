import OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationCanonicalGenerator

/-! # Presentation Cycle Comparison -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PresentationCycleComparison.BundleCycles

noncomputable section

/-! The integral-variety and presentation cycle indices identify the same supports and geometric classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem integralPresentation_supportCodimension (W : IrreducibleCloseds V.carrier) :
    V.presentation.supportCodimension W = CycleClass.Geometric.DimensionCycles.dimensionCodimension V W := by
  unfold Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.supportCodimension
  rw [PresentationComponentSupportClass.BundleCycles.integralPresentation_componentDimension V.presentation]
  rfl

def integralVarietyPresentationSupport (p : ℕ) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    V.presentation.DimensionCycleSupport p :=
  ⟨Z.val, (integralPresentation_supportCodimension V Z.val).trans Z.property⟩

def integralVarietyPresentationCycle (p : ℕ) :
    CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V p →ₗ[ℚ] V.presentation.RationalDimensionCycle p :=
  Finsupp.lmapDomain ℚ ℚ (integralVarietyPresentationSupport V p)

theorem integralVarietyPresentationSupport_class (p : ℕ) (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    V.presentation.geometricCycleClassMap p (Finsupp.single (integralVarietyPresentationSupport V p Z) 1) =
      Z.geometricCycleClass :=
  (PresentationCanonicalGenerator.BundleCycles.integralPresentation_cycleSupportClass V.presentation p (integralVarietyPresentationSupport V p Z)).symm.trans
    (Scheme.GeometricCycleClass.BundleCycles.schemeCycleClass_geometric V p Z)

theorem integralVarietyPresentationCycle_class (p : ℕ) (z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V p) :
    V.presentation.geometricCycleClassMap p (integralVarietyPresentationCycle V p z) =
      V.geometricCycleClassMap p z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | single Z r =>
    change V.presentation.geometricCycleClassMap p
      (Finsupp.mapDomain (integralVarietyPresentationSupport V p) (Finsupp.single Z r)) = _
    rw [Finsupp.mapDomain_single, ← Finsupp.smul_single_one (integralVarietyPresentationSupport V p Z) r,
      map_smul, integralVarietyPresentationSupport_class, Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PresentationCycleComparison.BundleCycles
