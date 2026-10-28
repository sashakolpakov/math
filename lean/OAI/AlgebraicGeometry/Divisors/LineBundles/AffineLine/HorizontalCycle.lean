import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.LineVerticalDivisors

/-! # Horizontal Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCycle.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual horizontal affine-line points differ from extended finite cycles by genuine principal divisors -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem affineLineHorizontalPoint_residual_extended (y : Charts.BundleCycles.affineLine X)
    (hy : Charts.BundleCycles.affineLineProjection X y = genericPoint X) (hne : y ≠ genericPoint (Charts.BundleCycles.affineLine X)) :
    ∃ g : (Charts.BundleCycles.affineLine X).functionField, g ≠ 0 ∧
      ((RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g - Finsupp.single y 1).support : Set (Charts.BundleCycles.affineLine X)) ⊆
        Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) := by
  obtain ⟨g, hg, hvertical⟩ := HorizontalCharts.BundleCycles.affineLineHorizontalPoint_relation X y hy hne
  refine ⟨g, hg, ?_⟩
  intro q hq
  have hbaseq := hvertical q hq
  have hqy : q ≠ y := fun h => hbaseq (h ▸ hy)
  have hnonzero : RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g q ≠ 0 := by
    intro hz
    exact Finsupp.mem_support_iff.mp hq (by rw [Finsupp.sub_apply, hz, Finsupp.single_eq_of_ne hqy, sub_self])
  have hh : Order.coheight q = 1 := by
    by_contra h
    apply hnonzero
    rw [RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply, Scheme.ord_eq_zero_of_coheight_neq_one h, Int.cast_zero]
  exact ⟨Charts.BundleCycles.affineLineProjection X q, LineVerticalDivisors.BundleCycles.affineLineVerticalHeightOne_generic X q hh hbaseq⟩

theorem affineLineHorizontalPoint_cycle_relation (y : Charts.BundleCycles.affineLine X)
    (hy : Charts.BundleCycles.affineLineProjection X y = genericPoint X) (hne : y ≠ genericPoint (Charts.BundleCycles.affineLine X)) :
    ∃ g : (Charts.BundleCycles.affineLine X).functionField, g ≠ 0 ∧ ∃ z : X →₀ ℚ,
      Finsupp.single y 1 + Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) z =
        RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g := by
  obtain ⟨g, hg, hs⟩ := affineLineHorizontalPoint_residual_extended X y hy hne
  let d := RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g - Finsupp.single y 1
  let z := Finsupp.comapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) d
    (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective (Charts.BundleCycles.affineLineProjection X)).injOn
  have he : Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) z = d :=
    Finsupp.mapDomain_comapDomain _ (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective (Charts.BundleCycles.affineLineProjection X)) d hs
  refine ⟨g, hg, z, ?_⟩
  rw [he]
  change Finsupp.single y 1 + (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Charts.BundleCycles.affineLine X) g - Finsupp.single y 1) = _
  rw [add_comm, sub_add_cancel]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCycle.BundleCycles
