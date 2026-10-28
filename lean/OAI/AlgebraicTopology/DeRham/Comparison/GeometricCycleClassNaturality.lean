import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClass
import OAI.AlgebraicTopology.DeRham.Comparison.RegularAmbientNaturality
import OAI.AlgebraicTopology.DeRham.Comparison.GeometricTraceNaturality
import OAI.AlgebraicTopology.Duality.Poincare.ComplexCapDiffeomorphism
import OAI.AlgebraicGeometry.CycleClass.Geometric.LinearReduction

/-! # Geometric Cycle Class Naturality -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClassNaturality

noncomputable section

/-!
# Naturality of the geometric cycle class defined by fundamental traces

The regular-locus class is identified by its evaluations on every
complementary compact-support class. Actual isomorphisms transport all
such tests bijectively and preserve both the canonical pairing and the
geometric trace functional. Ordinary restriction then determines the
ambient class, and linearity gives the square for finite rational cycles.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Duality.Poincare.ComplexCapDiffeomorphism

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace DimensionCycleSupport

variable {V W : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The geometric class on the regular ambient open set is natural because
its defining equality holds against every transported compact-support test. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricCycleClass_iso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyPullbackOfIso e Z (p + p)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularGeometricCycleClass =
      Z.regularGeometricCycleClass := by
  apply Z.regularGeometricCycleClass_unique
  intro b
  obtain ⟨c, rfl⟩ := (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso e Z).toLinearEquiv.surjective b
  calc
    _ = Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation W.complexDimension (p + p)
        (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularGeometricTrace_degree
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularGeometricCycleClass c := by
      change Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p)
        (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyPullbackOfIso e Z (p + p)
          (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularGeometricCycleClass)
        ((AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso e Z).hom c) = _
      rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso_hom_apply]
      exact Duality.Poincare.ComplexCapDiffeomorphism.compactSupportEvaluation_diffeomorph_of_dimension_eq
        (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_of_overIso e)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z 1) (p + p)
        (2 * Z.regularComplexDimension)
        (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension)
        (congrArg (fun n : ℕ => 2 * n) (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_iso e Z))
        Z.regularGeometricTrace_degree
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularGeometricTrace_degree
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularGeometricCycleClass c
    _ = (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularGeometricTrace c :=
      (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularGeometricCycleClass_evaluation c
    _ = Z.regularGeometricTrace ((AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso e Z).hom c) :=
      (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_iso e Z c).symm

/-- The independently defined ambient geometric cycle class is natural
under the actual isomorphism of algebraic varieties. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleClass_iso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).geometricCycleClass = Z.geometricCycleClass := by
  apply Z.regularAmbientCohomologyRestriction_injective
  rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyRestriction_iso_naturality_apply,
    (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).geometricCycleClass_regularRestriction,
    Z.geometricCycleClass_regularRestriction, AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricCycleClass_iso]

end DimensionCycleSupport

namespace IntegralProjectiveVariety

variable {V W : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}

/-- The actual geometric class map commutes with relabeling finite rational
algebraic cycles under a genuine isomorphism over the complex base. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_iso_naturality (e : V.toOver ≅ W.toOver) (p : ℕ) :
    (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p)).hom.comp
        ((W.geometricCycleClassMap p).comp (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv ℚ e p).toLinearMap) =
      V.geometricCycleClassMap p :=
  (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_iso_naturality_iff e p).mpr
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleClass_iso e)

/-- The same square evaluated on an actual finite rational cycle. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_iso_naturality_apply (e : V.toOver ≅ W.toOver) (p : ℕ)
    (z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V p) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p)
        (W.geometricCycleClassMap p (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv ℚ e p z)) =
      V.geometricCycleClassMap p z :=
  LinearMap.congr_fun (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_iso_naturality e p) z

/-- Pullback by the inverse support equivalence gives the ordinary
rational pullback of the independently constructed geometric class. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_isoPullback (e : V.toOver ≅ W.toOver) (p : ℕ)
    (z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.RationalDimensionCycle W p) :
    V.geometricCycleClassMap p (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycle.isoPullback ℚ e p z) =
      AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (p + p) (W.geometricCycleClassMap p z) := by
  have h := AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_iso_naturality_apply e p
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycle.isoPullback ℚ e p z)
  have hz : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv ℚ e p (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycle.isoPullback ℚ e p z) = z := by
    change AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv ℚ e p (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv ℚ e.symm p z) = z
    rw [← AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv_symm]
    exact (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycle.isoLinearEquiv ℚ e p).apply_symm_apply z
  rw [hz] at h
  exact h.symm

end IntegralProjectiveVariety

end

end OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClassNaturality
