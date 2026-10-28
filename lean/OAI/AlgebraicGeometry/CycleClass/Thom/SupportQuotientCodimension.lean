import OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient
import OAI.AlgebraicGeometry.CycleClass.Thom.FromStalkOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.MapDimension
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportCodimension

/-! # Support Quotient Codimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientCodimension.Constructions

noncomputable section

/-! Height-one points of the actual ambient prime quotient give
original cycle supports in precisely the next codimension, including
when the parent support is singular. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.FromStalkOrder.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.MapDimension.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem quotientSupportMap_coheight (X : Scheme) (D : IrreducibleCloseds X) (x : X) (hxD : x ∈ (D : Set X))
    (q : Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD))) :
    Order.coheight (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupportMap X D x hxD q) = Order.coheight q := by
  change Order.coheight ((Geometric.GenericPoint.reducedSupportScheme D).fromSpecStalk (IntersectionGeometry.supportPreimage D x hxD)
    ((Spec.map (StalkPrimeQuotient.Constructions.SupportScheme.quotientStalkEquiv X D x hxD).symm.toCommRingCatIso.hom) q)) = _
  rw [FromStalkOrder.Constructions.fromSpecStalk_coheight, coheight_eq_of_isOpenImmersion]

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

def parentPrimeSupport (y : D.scheme) : IrreducibleCloseds V.carrier :=
  irreducibleSetEquivPoints.symm (D.inclusion y)

theorem parentPrimeSupport_codimension (y : D.scheme) (hy : Order.coheight y = 1) :
    Geometric.DimensionCycles.dimensionCodimension V (parentPrimeSupport V D y) = p + 1 := by
  let Y := Thom.Scheme.RegularSupport.Constructions.supportOver V.toOver D.val
  let i : Y ⟶ V.toOver := Thom.Scheme.RegularSupport.Constructions.supportToAmbient V.toOver D.val
  let Z : IrreducibleCloseds Y.left := irreducibleSetEquivPoints.symm y
  have he : Thom.Scheme.ProperSupport.Constructions.imageSupport i Z = parentPrimeSupport V D y := by
    apply irreducibleSetEquivPoints.injective
    exact (Thom.Scheme.ProperSupport.Constructions.imageSupport_genericPoint i Z).trans
      ((congrArg i.left (irreducibleSetEquivPoints.apply_symm_apply y)).trans
        (irreducibleSetEquivPoints.apply_symm_apply (D.inclusion y)).symm)
  have hd := Integral.MapDimension.Constructions.finite_support_dimension i Z
  rw [he] at hd
  have hs := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one D.structureMap y hy
  have hD := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V D.val
  have hW := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V (parentPrimeSupport V D y)
  rw [D.property] at hD
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (parentPrimeSupport V D y) V.structureMap =
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z D.structureMap at hd
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z D.structureMap + 1 = Foundations.Scheme.SupportDimension.supportTranscendenceDimension D.val V.structureMap at hs
  omega

theorem quotientSupport_codimension (x : V.carrier) (hxD : x ∈ (D.val : Set V.carrier))
    (q : Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD))) (hq : Order.coheight q = 1) :
    Geometric.DimensionCycles.dimensionCodimension V (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport V.carrier D.val x hxD q) = p + 1 :=
  parentPrimeSupport_codimension V D (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupportMap V.carrier D.val x hxD q)
    ((quotientSupportMap_coheight V.carrier D.val x hxD q).trans hq)

def quotientCycleSupport (x : V.carrier) (hxD : x ∈ (D.val : Set V.carrier))
    (q : Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD))) (hq : Order.coheight q = 1) : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1) :=
  ⟨StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport V.carrier D.val x hxD q, quotientSupport_codimension V D x hxD q hq⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientCodimension.Constructions
