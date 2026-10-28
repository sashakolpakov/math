import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.Data.Finsupp.Basic

/-! # Finite Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteSupport.Cycles

/-!
# Finite support of algebraic cycles on quasi-compact schemes

Mathlib's algebraic cycles are functions on scheme points with locally finite
support. Compactness alone makes that support finite: no Hausdorff or T1
assumption is needed. The conversions below retain every coefficient.
-/

open _root_.AlgebraicGeometry

universe u v

/-- A locally finitely supported function on a compact space has finite support,
without any separation assumption on that space. -/
theorem finiteSupport_locallyFinsupp {T : Type u} [TopologicalSpace T]
    [CompactSpace T] {R : Type v} [Zero R] (c : Function.locallyFinsupp T R) :
    (Function.support c).Finite := by
  simpa only [Set.univ_inter, Function.locallyFinsuppWithin.toFun_eq_coe] using
    c.locallyFiniteSupport.finite_inter_support_of_isCompact isCompact_univ

/-- Quasi-compactness of the scheme suffices to turn mathlib's locally finite
algebraic cycles into finitely supported cycles. -/
theorem algebraicCycle_finiteSupport {X : Scheme.{u}} [CompactSpace X]
    {R : Type v} [Zero R] (c : AlgebraicCycle X R) :
    (Function.support c).Finite :=
  finiteSupport_locallyFinsupp c

/-- Every finite cycle defines a mathlib algebraic cycle, on any scheme. -/
def finsuppToAlgebraicCycle {X : Scheme.{u}} {R : Type v} [Zero R]
    (c : X →₀ R) : AlgebraicCycle X R where
  toFun := c
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' _ _ :=
    ⟨Set.univ, Filter.univ_mem, by
      simpa only [Set.univ_inter, Function.HasFiniteSupport] using c.hasFiniteSupport⟩

@[simp]
theorem finsuppToAlgebraicCycle_apply {X : Scheme.{u}} {R : Type v} [Zero R]
    (c : X →₀ R) (x : X) : finsuppToAlgebraicCycle c x = c x := rfl

/-- On a quasi-compact scheme, an algebraic cycle is a finite coefficient list. -/
noncomputable def algebraicCycleToFinsupp {X : Scheme.{u}} [CompactSpace X]
    {R : Type v} [Zero R] (c : AlgebraicCycle X R) : X →₀ R :=
  Finsupp.ofSupportFinite c (algebraicCycle_finiteSupport c)

@[simp]
theorem algebraicCycleToFinsupp_apply {X : Scheme.{u}} [CompactSpace X]
    {R : Type v} [Zero R] (c : AlgebraicCycle X R) (x : X) :
    algebraicCycleToFinsupp c x = c x := rfl

/-- This equivalence identifies coefficients, rather than selecting an arbitrary
bijection between the two notions of cycles. -/
noncomputable def algebraicCycleFinsuppEquiv (X : Scheme.{u}) [CompactSpace X]
    (R : Type v) [Zero R] : AlgebraicCycle X R ≃ (X →₀ R) where
  toFun := algebraicCycleToFinsupp
  invFun := finsuppToAlgebraicCycle
  left_inv _ := DFunLike.ext _ _ fun _ => rfl
  right_inv _ := Finsupp.ext fun _ => rfl

@[simp]
theorem algebraicCycleToFinsupp_finsuppToAlgebraicCycle {X : Scheme.{u}}
    [CompactSpace X] {R : Type v} [Zero R] (c : X →₀ R) :
    algebraicCycleToFinsupp (finsuppToAlgebraicCycle c) = c :=
  (algebraicCycleFinsuppEquiv X R).apply_symm_apply c

@[simp]
theorem finsuppToAlgebraicCycle_algebraicCycleToFinsupp {X : Scheme.{u}}
    [CompactSpace X] {R : Type v} [Zero R] (c : AlgebraicCycle X R) :
    finsuppToAlgebraicCycle (algebraicCycleToFinsupp c) = c :=
  (algebraicCycleFinsuppEquiv X R).symm_apply_apply c

/-- The equivalence also preserves addition of cycle coefficients. -/
noncomputable def algebraicCycleFinsuppAddEquiv (X : Scheme.{u}) [CompactSpace X]
    (R : Type v) [AddMonoid R] : AlgebraicCycle X R ≃+ (X →₀ R) where
  toEquiv := algebraicCycleFinsuppEquiv X R
  map_add' _ _ := Finsupp.ext fun _ => rfl

end OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteSupport.Cycles
