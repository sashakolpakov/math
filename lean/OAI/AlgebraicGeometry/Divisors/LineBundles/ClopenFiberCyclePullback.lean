import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClopenComponents
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiberFundamentalCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.ClopenCoverBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint

/-! # Clopen Fiber Cycle Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ClopenFiberCyclePullback.BundleCycles

noncomputable section

section

/-! The full fundamental cycle of a reduced fiber decomposes along an
actual finite clopen cover whose component projections have integral fibers. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {E X : Scheme.{0}} (p : E ⟶ X) [LocallyOfFiniteType p] [QuasiCompact p]
    {ι : Type} [Fintype ι] (U : ι → Scheme.{0}) (i : ∀ k, U k ⟶ E)
    [∀ k, IsOpenImmersion (i k)] [∀ k, IsClosedImmersion (i k)]
    [∀ k, GeometricallyIntegral (i k ≫ p)]
    (hcover : ∀ x : E, ∃! k, x ∈ Set.range (i k))

include hcover in
theorem clopenFiber_fundamentalPointCycle (y : X) [IsReduced (p.fiber y)] :
    FiberFundamentalCycle.BundleCycles.fiberFundamentalPointCycle p y =
      ∑ k, Finsupp.single (i k (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (i k ≫ p) y)) 1 := by
  classical
  let V : ι → Scheme := fun k => (i k ≫ p).fiber y
  let j : ∀ k, V k ⟶ p.fiber y := fun k =>
    Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap p (i k ≫ p) (i k) rfl (X.fromSpecResidueField y)
  let : ∀ k, IsIntegral (V k) := fun k => inferInstanceAs (IsIntegral ((i k ≫ p).fiber y))
  let : ∀ k, IsOpenImmersion (j k) := fun k =>
    ClopenCoverBaseChange.BundleCycles.clopenCoverBaseChangeMap_isOpenImmersion p U i (X.fromSpecResidueField y) k
  let : ∀ k, IsClosedImmersion (j k) := fun k =>
    Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_isClosedImmersion _ _ _ _ _
  have hc : ∀ x : p.fiber y, ∃! k, x ∈ Set.range (j k) :=
    ClopenCoverBaseChange.BundleCycles.clopenCoverBaseChange_covers p U i (X.fromSpecResidueField y) hcover
  let e := Integral.ClopenComponents.BundleCycles.integralClopenComponentsEquiv V j hc
  let := (NoetherianSpace.finite_irreducibleComponents (α := p.fiber y)).fintype
  change (∑ C : irreducibleComponents (p.fiber y),
    Finsupp.single (p.fiberι y (FiberFundamentalCycle.BundleCycles.componentGenericPoint (p.fiber y) C))
      ((Module.length ((p.fiber y).presheaf.stalk (FiberFundamentalCycle.BundleCycles.componentGenericPoint (p.fiber y) C))
        ((p.fiber y).presheaf.stalk (FiberFundamentalCycle.BundleCycles.componentGenericPoint (p.fiber y) C))).toNat : ℚ)) = _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [FiberFundamentalCycle.BundleCycles.componentGenericPoint_length_one_of_reduced]
  have hpoint : p.fiberι y (FiberFundamentalCycle.BundleCycles.componentGenericPoint (p.fiber y) (e k)) =
      i k (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (i k ≫ p) y) := by
    change p.fiberι y (FiberFundamentalCycle.BundleCycles.componentGenericPoint (p.fiber y) (Integral.ClopenComponents.BundleCycles.integralClopenComponent V j k)) = _
    rw [Integral.ClopenComponents.BundleCycles.integralClopenComponent_genericPoint]
    exact congrArg (fun t : V k ⟶ E => t (genericPoint (V k)))
      (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_fst p (i k ≫ p) (i k) rfl (X.fromSpecResidueField y))
  exact congrArg₂ Finsupp.single hpoint rfl

end

/-! The actual flat point-cycle formula is the sum of its integral
component formulas on a finite disjoint clopen cover. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} (p : E ⟶ X) [LocallyOfFiniteType p] [QuasiCompact p]
    {ι : Type} [Fintype ι] (U : ι → Scheme.{0}) (i : ∀ k, U k ⟶ E)
    [∀ k, IsOpenImmersion (i k)] [∀ k, IsClosedImmersion (i k)]
    [∀ k, GeometricallyIntegral (i k ≫ p)] [∀ y, IsReduced (p.fiber y)]
    (hcover : ∀ x : E, ∃! k, x ∈ Set.range (i k))

include hcover in
theorem clopenFiberCyclePullback_eq_sum : FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback p =
    ∑ k, (Finsupp.lmapDomain ℚ ℚ (i k)).comp (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (i k ≫ p)) := by
  apply Finsupp.lhom_ext
  intro y a
  rw [FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback_single, clopenFiber_fundamentalPointCycle p U i hcover,
    Finset.smul_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  change a • Finsupp.single (i k (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (i k ≫ p) y)) 1 =
    Finsupp.mapDomain (i k)
      (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (i k ≫ p)) (Finsupp.single y a))
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul, mul_one]

include hcover in
theorem clopenFiberCyclePullback_apply (z : X →₀ ℚ) : FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback p z =
    ∑ k, Finsupp.mapDomain (i k) (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (i k ≫ p) z) := by
  rw [clopenFiberCyclePullback_eq_sum p U i hcover, LinearMap.sum_apply]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ClopenFiberCyclePullback.BundleCycles
