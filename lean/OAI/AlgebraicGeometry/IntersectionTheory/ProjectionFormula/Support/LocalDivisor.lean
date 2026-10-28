import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.DivisorImage
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportPrime
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

/-! # Local Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalDivisor

noncomputable section

/-! Height-one primes of any support stalk give actual ambient supports
in the next codimension, with the exact nested stalk kernel retained. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (r : ℕ) (W : X.DimensionCycleSupport r)
  (x : X.carrier) (hxW : x ∈ (W.val : Set X.carrier))
  (p : PrimeSpectrum ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)))

def inner : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val) :=
  Stalk.DivisorSupport.primeClosure (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val) (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW) p

def support : IrreducibleCloseds X.carrier := DivisorImage.image X W.val (inner X r W x hxW p)

theorem support_point : CycleClass.Thom.IntersectionGeometry.supportPoint (support X r W x hxW p) =
    CycleClass.Geometric.GenericPoint.reducedSupportι W.val ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW) p) := by
  rw [support, DivisorImage.image_point, inner, Stalk.DivisorSupport.primeClosure_point]

theorem subset : support X r W x hxW p ≤ W.val := DivisorImage.image_le _ _ _

theorem point_mem : x ∈ (support X r W x hxW p : Set X.carrier) := by
  let Z := inner X r W x hxW p
  have hy : CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW ∈ (Z : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val)) :=
    Stalk.DivisorSupport.point_mem_primeClosure _ _ _
  have hs := ((Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).specializes hy).map
    (CycleClass.Geometric.GenericPoint.reducedSupportι W.val).continuous
  change CycleClass.Geometric.GenericPoint.reducedSupportι W.val (CycleClass.Thom.IntersectionGeometry.supportPoint Z) ⤳
    CycleClass.Geometric.GenericPoint.reducedSupportι W.val (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW) at hs
  rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec, ← DivisorImage.image_point] at hs
  exact hs.mem_closed (support X r W x hxW p).isClosed
    ((support X r W x hxW p).isIrreducible.isGenericPoint_genericPoint
      (support X r W x hxW p).isClosed).mem

theorem codimension (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] (hp : p.asIdeal.height = 1) :
    X.supportCodimension (support X r W x hxW p) = r + 1 := by
  have hz : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint (inner X r W x hxW p)) = 1 := by
    rw [inner, Stalk.DivisorSupport.primeClosure_point, ← Stalk.Localization.height_eq_coheight_image]
    exact hp
  have h := DivisorImage.codimension X W.val m (inner X r W x hxW p) hz
  simpa only [support, W.property] using h

theorem inner_eq : NestedSupport.innerSupport X.carrier (support X r W x hxW p) W.val (subset X r W x hxW p) =
    inner X r W x hxW p := by
  apply DivisorImage.image_injective X W.val
  rw [DivisorImage.image_innerSupport]
  rfl

theorem kernel_eq :
    RingHom.ker (NestedSupportStalk.stalkMap X.carrier (support X r W x hxW p) W.val
      (subset X r W x hxW p) x (point_mem X r W x hxW p) hxW).hom = p.asIdeal := by
  let A := support X r W x hxW p
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW
  let i := NestedSupport.inclusion X.carrier A W.val (subset X r W x hxW p)
  let z := CycleClass.Thom.IntersectionGeometry.supportPreimage A x (point_mem X r W x hxW p)
  let hiy := NestedSupport.inclusion_preimage X.carrier A W.val (subset X r W x hxW p) x
    (point_mem X r W x hxW p) hxW
  let q := Integral.StalkImage.prime i z y hiy
  have him : Y.fromSpecStalk y q = Y.fromSpecStalk y p := by
    rw [Integral.StalkImage.image, NestedSupport.inclusion_genericPoint]
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι W.val).isEmbedding.injective
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
    exact support_point X r W x hxW p
  have heq : q = p := (Y.fromSpecStalk y).isEmbedding.injective him
  exact congrArg PrimeSpectrum.asIdeal heq

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.LocalDivisor
