import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Trace
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PrincipalPointSum

/-! # Principal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal

noncomputable section

/-! The finite sum of actual normalized divisor images is precisely the
principal cycle prescribed by ThomClass, including every pole and residue weight. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
  NormalizationDivisor.Image.Constructions Scheme.FiniteDivisorDetection.Constructions Point.Constructions

/-- Generic-point coordinates for the actual graded cycles. -/
def cyclePointMap (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Geometric.DimensionCycles.RationalDimensionCycle V p →ₗ[ℚ] (V.carrier →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (fun C : Geometric.DimensionCycles.DimensionCycleSupport V p => IntersectionGeometry.supportPoint C.val)

theorem cyclePointMap_single (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (C : Geometric.DimensionCycles.DimensionCycleSupport V p) (a : ℚ) :
    cyclePointMap V p (Finsupp.single C a) = Finsupp.single (IntersectionGeometry.supportPoint C.val) a :=
  Finsupp.mapDomain_single

theorem cyclePointMap_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (a : Geometric.DimensionCycles.RationalDimensionCycle V p) (C : Geometric.DimensionCycles.DimensionCycleSupport V p) :
    cyclePointMap V p a (IntersectionGeometry.supportPoint C.val) = a C :=
  Finsupp.mapDomain_apply_of_injective (fun _ _ h => Subtype.ext (irreducibleSetEquivPoints.injective h)) a C

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)

local instance : Smooth (AmbientMap.Constructions.smoothNormalizationOver V W).hom := AmbientMap.Constructions.smoothNormalization_smooth V W

abbrev DivisorPoint := Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint (AmbientMap.Constructions.smoothNormalizationOver V W)
  (PrincipalBoundary.Constructions.normalizedUnitRepresentative V W g hg).domain

local instance : Fintype (DivisorPoint V W g hg) := Fintype.ofFinite _

/-- The genuine finite normalized divisor, pushed to its original ambient
reduced supports with the original local orders and residue-field degrees. -/
def normalizedPrincipalCycle : Geometric.DimensionCycles.RationalDimensionCycle V (Geometric.DimensionCycles.dimensionCodimension V W + 1) :=
  ∑ z : DivisorPoint V W g hg,
    ((AmbientMap.Constructions.smoothNormalizationOver V W).left.ord (PrincipalBoundary.Constructions.normalizedFunction V W g) z.val : ℚ) •
      Finsupp.single (NormalizationDivisor.Image.Constructions.imageCycleSupport V W ⟨z.val, z.property.1⟩)
        ((PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree z.val : ℚ)

theorem normalizedPrincipalCycle_points :
    cyclePointMap V (Geometric.DimensionCycles.dimensionCodimension V W + 1) (normalizedPrincipalCycle V W g hg) =
    Point.Constructions.pointPushforward (PrincipalBoundary.Constructions.fullAmbientMap V W).left
      (Point.Constructions.rationalPrincipalPointDivisor (AmbientMap.Constructions.smoothNormalizationOver V W).left (PrincipalBoundary.Constructions.normalizedFunction V W g)) := by
  classical
  rw [Scheme.PrincipalPointSum.Constructions.principalPointDivisor_eq_sum (AmbientMap.Constructions.smoothNormalizationOver V W)
    (PrincipalBoundary.Constructions.normalizedUnitRepresentative V W g hg), normalizedPrincipalCycle, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul, cyclePointMap_single, Finsupp.smul_single, Point.Constructions.pointPushforward_single]
  have hp := NormalizationDivisor.Image.Constructions.imageSupport_genericPoint V W ⟨z.val, z.property.1⟩
  change IntersectionGeometry.supportPoint (NormalizationDivisor.Image.Constructions.imageCycleSupport V W ⟨z.val, z.property.1⟩).val =
    (PrincipalBoundary.Constructions.fullAmbientMap V W).left z.val at hp
  rw [hp]
  rfl

/-- Every coefficient is exactly the faithful ThomClass principal-divisor coefficient. -/
theorem normalizedPrincipalCycle_coefficient (C : Geometric.DimensionCycles.DimensionCycleSupport V (Geometric.DimensionCycles.dimensionCodimension V W + 1)) :
    normalizedPrincipalCycle V W g hg C = IntersectionGeometry.principalDivisorCoefficient V.presentation W g C.val := by
  have h := congrArg (fun a : V.carrier →₀ ℚ => a (IntersectionGeometry.supportPoint C.val))
    (normalizedPrincipalCycle_points V W g hg)
  rw [cyclePointMap_apply] at h
  exact h.trans (PrincipalBoundary.Constructions.normalizedPrincipal_coefficient V W g hg C.val)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal
