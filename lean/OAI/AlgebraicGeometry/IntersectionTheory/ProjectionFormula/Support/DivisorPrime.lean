import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalDivisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportStalk

/-! # Divisor Prime -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.DivisorPrime

noncomputable section

/-! The inverse correspondence sends an ambient support contained in another
support to the kernel of its actual nested stalk map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ) (W : X.DimensionCycleSupport r)
  (x : X.carrier) (hxW : x ∈ (W.val : Set X.carrier))

def prime (A : IrreducibleCloseds X.carrier) (hAW : A ≤ W.val) (hxA : x ∈ (A : Set X.carrier)) :
    PrimeSpectrum ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)) :=
  Integral.StalkImage.prime (NestedSupport.inclusion X.carrier A W.val hAW)
    (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA) (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)
    (NestedSupport.inclusion_preimage X.carrier A W.val hAW x hxA hxW)

theorem image (A : IrreducibleCloseds X.carrier) (hAW : A ≤ W.val) (hxA : x ∈ (A : Set X.carrier)) :
    LocalDivisor.support X r W x hxW (prime X r W x hxW A hAW hxA) = A := by
  apply irreducibleSetEquivPoints.injective
  change CycleClass.Thom.IntersectionGeometry.supportPoint (LocalDivisor.support X r W x hxW (prime X r W x hxW A hAW hxA)) = CycleClass.Thom.IntersectionGeometry.supportPoint A
  rw [LocalDivisor.support_point, prime, Integral.StalkImage.image,
    NestedSupport.inclusion_genericPoint, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]

theorem height (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport (r + 1)) (hAW : A.val ≤ W.val) (hxA : x ∈ (A.val : Set X.carrier)) :
    (prime X r W x hxW A.val hAW hxA).asIdeal.height = 1 :=
by
  rw [prime, Integral.StalkImage.height, NestedSupport.inclusion_genericPoint]
  exact AdjacentSupportStalk.coheight_one X m r W A _

theorem support_injective : Function.Injective (LocalDivisor.support X r W x hxW) := by
  intro p q he
  apply ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)).isEmbedding.injective
  apply (CycleClass.Geometric.GenericPoint.reducedSupportι W.val).isEmbedding.injective
  exact (LocalDivisor.support_point X r W x hxW p).symm.trans
    ((congrArg CycleClass.Thom.IntersectionGeometry.supportPoint he).trans (LocalDivisor.support_point X r W x hxW q))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.DivisorPrime
