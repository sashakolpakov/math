import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClass
import OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveRationalBettiIso

/-! # Linear Reduction -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# The geometric cycle-class square reduces to its actual generators

The cycle module is the genuine finite rational coefficient module on
irreducible algebraic supports. Linearity therefore reduces the new
geometric cycle-class naturality square to its generator identities.
-/

open _root_.CategoryTheory

variable {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}

/-- The actual geometric cycle-class square commutes exactly when the
geometric class of each transported algebraic support pulls back correctly. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_iso_naturality_iff (e : V.toOver ≅ W.toOver) (p : ℕ) :
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p)).hom.comp
        ((W.geometricCycleClassMap p).comp (CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv ℚ e p).toLinearMap) =
      V.geometricCycleClassMap p ↔
    ∀ Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p,
      Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p)
          (CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).geometricCycleClass = Z.geometricCycleClass := by
  constructor
  · intro h Z
    have hz := LinearMap.congr_fun h (Finsupp.single Z 1)
    change Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p)
        (W.geometricCycleClassMap p
          (CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv ℚ e p (Finsupp.single Z 1))) =
      V.geometricCycleClassMap p (Finsupp.single Z 1) at hz
    simpa only [CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv_single, Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single,
      one_smul] using hz
  · intro h
    apply Finsupp.lhom_ext
    intro Z q
    change Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p)
        (W.geometricCycleClassMap p
          (CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv ℚ e p (Finsupp.single Z q))) =
      V.geometricCycleClassMap p (Finsupp.single Z q)
    rw [CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv_single, Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single,
      Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single]
    change (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p)).hom
        (q • (CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).geometricCycleClass) =
      q • Z.geometricCycleClass
    rw [map_smul]
    exact congrArg (fun a => q • a) (h Z)

end

end OAI.AlgebraicGeometry
