import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.DivisorImage
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportPrime
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

/-! # Surface Curve Prime -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfaceCurvePrime

noncomputable section

section

/-! Height-one primes of a surface-support stalk correspond to actual
ambient curve supports through the chosen point, with the exact nested
stalk kernel and the original inner support retained. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Local

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : X.DimensionCycleSupport 1)
  (x : X.carrier) (hxW : x ∈ (W.val : Set X.carrier))
  (p : PrimeSpectrum ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)))

def inner : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val) :=
  Stalk.DivisorSupport.primeClosure (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val) (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW) p

def support : IrreducibleCloseds X.carrier := Support.DivisorImage.image X W.val (inner X W x hxW p)

theorem support_point : CycleClass.Thom.IntersectionGeometry.supportPoint (support X W x hxW p) =
    CycleClass.Geometric.GenericPoint.reducedSupportι W.val ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW) p) := by
  rw [support, Support.DivisorImage.image_point, inner, Stalk.DivisorSupport.primeClosure_point]

theorem subset : support X W x hxW p ≤ W.val := Support.DivisorImage.image_le _ _ _

theorem point_mem : x ∈ (support X W x hxW p : Set X.carrier) := by
  let Z := inner X W x hxW p
  have hy : CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW ∈ (Z : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val)) :=
    Stalk.DivisorSupport.point_mem_primeClosure _ _ _
  have hs := ((Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).specializes hy).map
    (CycleClass.Geometric.GenericPoint.reducedSupportι W.val).continuous
  change CycleClass.Geometric.GenericPoint.reducedSupportι W.val (CycleClass.Thom.IntersectionGeometry.supportPoint Z) ⤳
    CycleClass.Geometric.GenericPoint.reducedSupportι W.val (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW) at hs
  rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec, ← Support.DivisorImage.image_point] at hs
  exact hs.mem_closed (support X W x hxW p).isClosed
    ((support X W x hxW p).isIrreducible.isGenericPoint_genericPoint
      (support X W x hxW p).isClosed).mem

theorem codimension (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] (hp : p.asIdeal.height = 1) :
    X.supportCodimension (support X W x hxW p) = 2 := by
  have hz : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint (inner X W x hxW p)) = 1 := by
    rw [inner, Stalk.DivisorSupport.primeClosure_point, ← Stalk.Localization.height_eq_coheight_image]
    exact hp
  have h := Support.DivisorImage.codimension X W.val m (inner X W x hxW p) hz
  simpa only [support, W.property, one_add_one_eq_two] using h

theorem inner_eq : NestedSupport.innerSupport X.carrier (support X W x hxW p) W.val (subset X W x hxW p) =
    inner X W x hxW p := by
  apply Support.DivisorImage.image_injective X W.val
  rw [Support.DivisorImage.image_innerSupport]
  rfl

theorem kernel_eq :
    RingHom.ker (NestedSupportStalk.stalkMap X.carrier (support X W x hxW p) W.val
      (subset X W x hxW p) x (point_mem X W x hxW p) hxW).hom = p.asIdeal := by
  let A := support X W x hxW p
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW
  let i := NestedSupport.inclusion X.carrier A W.val (subset X W x hxW p)
  let z := CycleClass.Thom.IntersectionGeometry.supportPreimage A x (point_mem X W x hxW p)
  let hiy := NestedSupport.inclusion_preimage X.carrier A W.val (subset X W x hxW p) x
    (point_mem X W x hxW p) hxW
  let q := Integral.StalkImage.prime i z y hiy
  have him : Y.fromSpecStalk y q = Y.fromSpecStalk y p := by
    rw [Integral.StalkImage.image, NestedSupport.inclusion_genericPoint]
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι W.val).isEmbedding.injective
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
    exact support_point X W x hxW p
  have heq : q = p := (Y.fromSpecStalk y).isEmbedding.injective him
  exact congrArg PrimeSpectrum.asIdeal heq

end Local

end

/-! The inverse correspondence sends an ambient curve contained in a
surface to the kernel of its actual nested stalk map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : X.DimensionCycleSupport 1)
  (x : X.carrier) (hxW : x ∈ (W.val : Set X.carrier))

def prime (A : IrreducibleCloseds X.carrier) (hAW : A ≤ W.val) (hxA : x ∈ (A : Set X.carrier)) :
    PrimeSpectrum ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)) :=
  Integral.StalkImage.prime (NestedSupport.inclusion X.carrier A W.val hAW)
    (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA) (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)
    (NestedSupport.inclusion_preimage X.carrier A W.val hAW x hxA hxW)

theorem image (A : IrreducibleCloseds X.carrier) (hAW : A ≤ W.val) (hxA : x ∈ (A : Set X.carrier)) :
    Local.support X W x hxW (prime X W x hxW A hAW hxA) = A := by
  apply irreducibleSetEquivPoints.injective
  change CycleClass.Thom.IntersectionGeometry.supportPoint (Local.support X W x hxW (prime X W x hxW A hAW hxA)) = CycleClass.Thom.IntersectionGeometry.supportPoint A
  rw [Local.support_point, prime, Integral.StalkImage.image,
    NestedSupport.inclusion_genericPoint, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]

theorem height (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport 2) (hAW : A.val ≤ W.val) (hxA : x ∈ (A.val : Set X.carrier)) :
    (prime X W x hxW A.val hAW hxA).asIdeal.height = 1 :=
  NestedSupportPrime.height X m W A hAW x hxA hxW

theorem support_injective : Function.Injective (Local.support X W x hxW) := by
  intro p q he
  apply ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)).isEmbedding.injective
  apply (CycleClass.Geometric.GenericPoint.reducedSupportι W.val).isEmbedding.injective
  exact (Local.support_point X W x hxW p).symm.trans
    ((congrArg CycleClass.Thom.IntersectionGeometry.supportPoint he).trans (Local.support_point X W x hxW q))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfaceCurvePrime
