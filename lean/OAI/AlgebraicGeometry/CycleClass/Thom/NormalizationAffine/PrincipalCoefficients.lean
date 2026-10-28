import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenPrincipal
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.OpenRange
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.MeetingOpen

/-! # Principal Coefficients -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrincipalCoefficients.Constructions

noncomputable section

/-! The constructed affine normalization retains every fiber over its
actual base open. Therefore every cycle meeting the retained analytic
open has exactly the original parent principal-divisor coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.OpenRange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenPrincipal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenFunctionField.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.MeetingOpen.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) (hB : B ≤ Normalization.AmbientMap.Constructions.ambientOpen V D.val)

theorem affineSource_fiber_cover (x : V.carrier) (hx : x ∈ B) :
    ∀ y : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V D.val).left,
      (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V D.val).left y = x → y ∈ Set.range (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB).left := by
  intro y hy
  apply (OpenRange.Constructions.sourceToSmooth_mem_range D B hB y).mpr
  exact hy.symm ▸ hx

variable [IsIntegral (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left] [AlgebraicGeometry.IsNoetherian (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left]
  {r : (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left.functionField} (R : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left r)

theorem affinePrincipalCycle_coefficient_on_meeting (hr : r ≠ 0)
    (U : Opens V.analyticSpace)
    (hU : (U : Set V.analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver B)
    (C : Geometric.DimensionCycles.DimensionCycleSupport V (Geometric.DimensionCycles.dimensionCodimension V D.val + 1))
    (hC : ∃ x : U, x.val ∈ Set.range C.analyticInclusion) :
    Normalization.OpenPrincipal.Constructions.openPrincipalCycle V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) R C =
      IntersectionGeometry.principalDivisorCoefficient V.presentation D.val
        (Normalization.OpenFunctionField.Constructions.originalFunction V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) r) C.val :=
  Normalization.OpenPrincipal.Constructions.openPrincipalCycle_original_coefficient V D.val (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) R hr C
    (affineSource_fiber_cover D B hB (IntersectionGeometry.supportPoint C.val)
      (Cycle.MeetingOpen.Constructions.supportPoint_mem_of_analytic_meets V C B U hU hC))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrincipalCoefficients.Constructions
