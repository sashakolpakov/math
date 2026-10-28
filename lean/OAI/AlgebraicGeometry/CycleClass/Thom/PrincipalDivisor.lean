import OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDivisorComparison
import OAI.AlgebraicGeometry.CycleClass.Thom.GeometricTrace
import OAI.AlgebraicGeometry.Divisors.LineBundles.Ord

/-! # Principal Divisor -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDivisor

noncomputable section

/-! The principal divisor indexed by every genuine codimension-one support
has its exact scheme-theoretic order as coefficient and zero geometric class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDivisorComparison.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.PrincipalDivisor.Constructions
  Thom.Finite.DivisorDetection.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def divisorSupportPointEmbedding : Geometric.DimensionCycles.DimensionCycleSupport V 1 ↪ V.carrier where
  toFun C := IntersectionGeometry.supportPoint C.val
  inj' := by
    intro C D h
    apply Subtype.ext
    exact irreducibleSetEquivPoints.injective h

theorem finite_support_divisor_order (g : V.carrier.functionField) :
    (Function.support (fun C : Geometric.DimensionCycles.DimensionCycleSupport V 1 =>
      (V.carrier.ord g (IntersectionGeometry.supportPoint C.val) : ℚ))).Finite := by
  apply (Set.Finite.preimage_embedding (divisorSupportPointEmbedding V)
    (Divisors.LineBundles.Ord.BundleCycles.finite_support_ord V.carrier g)).subset
  intro C hC
  change V.carrier.ord g (IntersectionGeometry.supportPoint C.val) ≠ 0
  intro hzero
  apply hC
  change (V.carrier.ord g (IntersectionGeometry.supportPoint C.val) : ℚ) = 0
  rw [hzero, Int.cast_zero]

/-- Every coefficient is the actual local order, with genuine finite support. -/
def rationalFunctionDivisor (g : V.carrier.functionField) : Geometric.DimensionCycles.RationalDimensionCycle V 1 :=
  Finsupp.ofSupportFinite
    (fun C => (V.carrier.ord g (IntersectionGeometry.supportPoint C.val) : ℚ))
    (finite_support_divisor_order V g)

@[simp]
theorem rationalFunctionDivisor_apply (g : V.carrier.functionField) (C : Geometric.DimensionCycles.DimensionCycleSupport V 1) :
    rationalFunctionDivisor V g C = (V.carrier.ord g (IntersectionGeometry.supportPoint C.val) : ℚ) := rfl

theorem complementDivisorSupport_point (R : V.carrier.Opens)
    (z : Thom.Finite.DivisorDetection.Constructions.ComplementDivisorPoint V.presentation R) :
    IntersectionGeometry.supportPoint (Supported.PrincipalDivisor.Constructions.complementDivisorSupport V.presentation R z).val = z.val :=
  irreducibleSetEquivPoints.apply_symm_apply z.val

theorem principalDivisorCycle_eq_rationalFunctionDivisor {g : V.carrier.functionField}
    (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative V.carrier g) :
    Supported.PrincipalDivisor.Constructions.principalDivisorCycle V.presentation D.domain g = rationalFunctionDivisor V g := by
  classical
  let : Fintype (Thom.Finite.DivisorDetection.Constructions.ComplementDivisorPoint V.presentation D.domain) := Fintype.ofFinite _
  ext C
  change Supported.PrincipalDivisor.Constructions.principalDivisorCycle V.presentation D.domain g C =
    (V.carrier.ord g (IntersectionGeometry.supportPoint C.val) : ℚ)
  by_cases hC : C ∈ Set.range (Supported.PrincipalDivisor.Constructions.complementDivisorSupport V.presentation D.domain)
  · obtain ⟨z, rfl⟩ := hC
    rw [Supported.PrincipalDivisor.Constructions.principalDivisorCycle_apply, complementDivisorSupport_point]
  · have hsum : Supported.PrincipalDivisor.Constructions.principalDivisorCycle V.presentation D.domain g C = 0 := by
      unfold Supported.PrincipalDivisor.Constructions.principalDivisorCycle
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro z _
      exact Finsupp.single_eq_of_ne' (fun he => hC ⟨z, he⟩)
    rw [hsum]
    symm
    suffices V.carrier.ord g (IntersectionGeometry.supportPoint C.val) = 0 by exact_mod_cast this
    by_contra hm
    have hz : Order.coheight (IntersectionGeometry.supportPoint C.val) = 1 := by
      by_contra hn
      exact hm (Scheme.ord_eq_zero_of_coheight_neq_one hn g)
    have hR : IntersectionGeometry.supportPoint C.val ∉ D.domain := by
      intro h
      exact hm (D.ord_eq_zero _ h)
    let z : Thom.Finite.DivisorDetection.Constructions.ComplementDivisorPoint V.presentation D.domain :=
      ⟨IntersectionGeometry.supportPoint C.val, hz, hR⟩
    apply hC
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact irreducibleSetEquivPoints.symm_apply_apply C.val

theorem rationalFunctionDivisor_geometricClass_zero (g : V.carrier.functionField) (hg : g ≠ 0) :
    V.geometricCycleClassMap 1 (rationalFunctionDivisor V g) = 0 := by
  let D := RationalFunctionBoundary.Constructions.Principal.rationalUnitRepresentative V.carrier g hg
  have h := PrincipalDivisorComparison.Constructions.principalDivisorCycle_rationalCycleClass_zero V D hg
  rw [principalDivisorCycle_eq_rationalFunctionDivisor V D,
    GeometricTrace.Constructions.HigherThom.rationalCycleClassMap_eq_geometric V 1] at h
  exact h

theorem geometricClass_zero_of_principal_orders
    (g : V.carrier.functionField) (hg : g ≠ 0) (d : Geometric.DimensionCycles.RationalDimensionCycle V 1)
    (hd : ∀ C, d C = (V.carrier.ord g (IntersectionGeometry.supportPoint C.val) : ℚ)) :
    V.geometricCycleClassMap 1 d = 0 := by
  have he : d = rationalFunctionDivisor V g := Finsupp.ext hd
  rw [he]
  exact rationalFunctionDivisor_geometricClass_zero V g hg

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDivisor
