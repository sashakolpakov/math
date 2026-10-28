import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenPrincipalCoefficients
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField

/-! # Open Principal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenPrincipal.Constructions

noncomputable section

/-! The actual finite divisor sum on an arbitrary normalization open is
the genuine point pushforward; on fully retained fibers its coefficients
are the original principal-divisor coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenPrincipalCoefficients.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Point.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ResidueDegree.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.FiniteDivisorDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (AmbientMap.Constructions.smoothNormalizationOver V W).hom := AmbientMap.Constructions.smoothNormalization_smooth V W

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]
  {r : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left r)

local instance : Fintype (Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain) := Fintype.ofFinite _

def openPrincipalCycle : Geometric.DimensionCycles.RationalDimensionCycle V (Geometric.DimensionCycles.dimensionCodimension V W + 1) :=
  ∑ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain, (X.left.ord r z.val : ℚ) •
    Finsupp.single (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩))
      ((PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩).val : ℚ)

omit [Smooth X.hom] in
theorem openPrincipalCycle_points :
    Principal.Constructions.cyclePointMap V (Geometric.DimensionCycles.dimensionCodimension V W + 1) (openPrincipalCycle V W a D) =
      Point.Constructions.pointPushforward (a ≫ PrincipalBoundary.Constructions.fullAmbientMap V W).left (Point.Constructions.rationalPrincipalPointDivisor X.left r) := by
  classical
  rw [Scheme.PrincipalPointSum.Constructions.principalPointDivisor_eq_sum X D, openPrincipalCycle, map_sum, map_sum]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [map_smul, Principal.Constructions.cyclePointMap_single, Finsupp.smul_single, Point.Constructions.pointPushforward_single]
  have hp := NormalizationDivisor.Image.Constructions.imageSupport_genericPoint V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)
  change IntersectionGeometry.supportPoint (NormalizationDivisor.Image.Constructions.imageCycleSupport V W (Open.PrimeSupport.Constructions.ambientPrime a ⟨z.val, z.property.1⟩)).val =
    (PrincipalBoundary.Constructions.fullAmbientMap V W).left (a.left z.val) at hp
  rw [hp]
  have hd := ResidueDegree.Constructions.residueDegree_comp a.left (PrincipalBoundary.Constructions.fullAmbientMap V W).left z.val
  rw [ResidueDegree.Constructions.residueDegree_immersion a.left z.val, mul_one] at hd
  change (a ≫ PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree z.val =
    (PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree (a.left z.val) at hd
  exact congrArg (fun n : ℕ => Finsupp.single ((PrincipalBoundary.Constructions.fullAmbientMap V W).left (a.left z.val))
    ((X.left.ord r z.val : ℚ) * (n : ℚ))) hd.symm

omit [Smooth X.hom] in
theorem openPrincipalCycle_coefficient
    (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)
    (hr : r = RationalOrderTransport.Constructions.openFunctionFieldMap a.left (PrincipalBoundary.Constructions.normalizedFunction V W g))
    (C : Geometric.DimensionCycles.DimensionCycleSupport V (Geometric.DimensionCycles.dimensionCodimension V W + 1))
    (hcover : ∀ y : (AmbientMap.Constructions.smoothNormalizationOver V W).left,
      (PrincipalBoundary.Constructions.fullAmbientMap V W).left y = IntersectionGeometry.supportPoint C.val → y ∈ Set.range a.left) :
    openPrincipalCycle V W a D C = IntersectionGeometry.principalDivisorCoefficient V.presentation W g C.val := by
  have h := congrArg (fun c : V.carrier →₀ ℚ => c (IntersectionGeometry.supportPoint C.val)) (openPrincipalCycle_points V W a D)
  rw [Principal.Constructions.cyclePointMap_apply] at h
  have he := congrArg (fun t : X.left.functionField =>
    Point.Constructions.pointPushforward (a ≫ PrincipalBoundary.Constructions.fullAmbientMap V W).left (Point.Constructions.rationalPrincipalPointDivisor X.left t)
      (IntersectionGeometry.supportPoint C.val)) hr
  exact h.trans (he.trans (OpenPrincipalCoefficients.Constructions.openPrincipal_coefficient V W a g hg C.val hcover))

omit [Smooth X.hom] in
theorem openPrincipalCycle_original_coefficient (hr : r ≠ 0)
    (C : Geometric.DimensionCycles.DimensionCycleSupport V (Geometric.DimensionCycles.dimensionCodimension V W + 1))
    (hcover : ∀ y : (AmbientMap.Constructions.smoothNormalizationOver V W).left,
      (PrincipalBoundary.Constructions.fullAmbientMap V W).left y = IntersectionGeometry.supportPoint C.val → y ∈ Set.range a.left) :
    openPrincipalCycle V W a D C =
      IntersectionGeometry.principalDivisorCoefficient V.presentation W (OpenFunctionField.Constructions.originalFunction V W a r) C.val :=
  openPrincipalCycle_coefficient V W a D (OpenFunctionField.Constructions.originalFunction V W a r) (OpenFunctionField.Constructions.originalFunction_ne_zero V W a r hr)
    (OpenFunctionField.Constructions.originalFunction_pullback V W a r).symm C hcover

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenPrincipal.Constructions
