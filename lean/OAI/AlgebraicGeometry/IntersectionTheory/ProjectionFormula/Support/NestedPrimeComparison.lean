import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportPoints
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.DivisorPrime

/-! # Nested Prime Comparison -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.NestedPrimeComparison

noncomputable section

/-! The inner reduced-support kernel and the direct nested-support
kernel define the same actual prime of the larger support stalk. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem prime_eq (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ) (W : X.DimensionCycleSupport r)
    (A : IrreducibleCloseds X.carrier) (hAW : A ≤ W.val)
    (x : X.carrier) (hxW : x ∈ (W.val : Set X.carrier)) (hxA : x ∈ (A : Set X.carrier)) :
    Stalk.PrimeQuotient.kernelPrime (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val) (NestedSupport.innerSupport X.carrier A W.val hAW)
      (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)
      ((NestedSupportPoints.preimage_mem_iff X.carrier A W.val hAW x hxW).mpr hxA) =
      DivisorPrime.prime X r W x hxW A hAW hxA := by
  apply ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)).isEmbedding.injective
  rw [Stalk.PrimeQuotient.kernelPrime_image, NestedSupport.innerSupport_point, DivisorPrime.prime, Integral.StalkImage.image,
    NestedSupport.inclusion_genericPoint]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.NestedPrimeComparison
