import OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

/-! # Support Quotient Points -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientPoints.Constructions

noncomputable section

/-! Points of the actual ambient prime quotient correspond exactly to
the original irreducible supports inside the parent and through the
chosen scheme point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme) (D : IrreducibleCloseds X) (x : X) (hxD : x ∈ (D : Set X))

theorem quotientSupportMap_injective : Function.Injective (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupportMap X D x hxD) :=
  ((Geometric.GenericPoint.reducedSupportScheme D).fromSpecStalk (IntersectionGeometry.supportPreimage D x hxD)).isEmbedding.injective.comp
    (Spec.map (StalkPrimeQuotient.Constructions.SupportScheme.quotientStalkEquiv X D x hxD).symm.toCommRingCatIso.hom).isOpenEmbedding.injective

theorem quotientSupport_injective : Function.Injective (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport X D x hxD) := by
  intro q t h
  apply quotientSupportMap_injective X D x hxD
  apply (Geometric.GenericPoint.reducedSupportι D).isClosedEmbedding.injective
  exact (StalkPrimeQuotient.Constructions.SupportScheme.supportPoint_quotientSupport X D x hxD q).symm.trans
    ((congrArg IntersectionGeometry.supportPoint h).trans (StalkPrimeQuotient.Constructions.SupportScheme.supportPoint_quotientSupport X D x hxD t))

theorem quotientSupport_subset_parent (q : Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD))) :
    (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport X D x hxD q : Set X) ⊆ D :=
  (Intersection.Supports.supportPoint_mem_iff_subset ⟨D, D.isClosed⟩ (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport X D x hxD q)).mp
    (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport_mem_parent X D x hxD q)

theorem point_mem_quotientSupport (q : Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD))) :
    x ∈ (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport X D x hxD q : Set X) := by
  let z := Geometric.GenericPoint.reducedSupportι D (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupportMap X D x hxD q)
  have hr : z ∈ Set.range (X.fromSpecStalk x) :=
    ⟨(Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD)))) q,
      (congrArg (fun f => f q) (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupportMap_ambient X D x hxD)).symm⟩
  have hs : z ⤳ x := by rwa [Scheme.range_fromSpecStalk] at hr
  change x ∈ closure {z}
  exact specializes_iff_mem_closure.mp hs

theorem exists_quotientSupport (W : IrreducibleCloseds X) (hWD : (W : Set X) ⊆ D) (hxW : x ∈ (W : Set X)) :
    ∃ q : Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD)), StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport X D x hxD q = W := by
  have hW : IntersectionGeometry.supportPoint W ∈ (D : Set X) := hWD (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem
  let y := IntersectionGeometry.supportPreimage D (IntersectionGeometry.supportPoint W) hW
  let z := IntersectionGeometry.supportPreimage D x hxD
  have hs : IntersectionGeometry.supportPoint W ⤳ x := (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).specializes hxW
  have hyz : y ⤳ z := by
    apply (Geometric.GenericPoint.reducedSupportι D).isClosedEmbedding.isEmbedding.isInducing.specializes_iff.mp
    exact (specializes_of_eq (IntersectionGeometry.supportPreimage_spec D (IntersectionGeometry.supportPoint W) hW)).trans
      (hs.trans (specializes_of_eq (IntersectionGeometry.supportPreimage_spec D x hxD).symm))
  have hy : y ∈ Set.range ((Geometric.GenericPoint.reducedSupportScheme D).fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]
    exact hyz
  obtain ⟨t, ht⟩ := hy
  let i := Spec.map (StalkPrimeQuotient.Constructions.SupportScheme.quotientStalkEquiv X D x hxD).symm.toCommRingCatIso.hom
  obtain ⟨q, hq⟩ := i.homeomorph.surjective t
  refine ⟨q, ?_⟩
  apply irreducibleSetEquivPoints.injective
  exact (StalkPrimeQuotient.Constructions.SupportScheme.supportPoint_quotientSupport X D x hxD q).trans
    ((congrArg (Geometric.GenericPoint.reducedSupportι D) ((congrArg ((Geometric.GenericPoint.reducedSupportScheme D).fromSpecStalk z) hq).trans ht)).trans
      (IntersectionGeometry.supportPreimage_spec D (IntersectionGeometry.supportPoint W) hW))

def quotientSupportEquiv : Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD)) ≃
    {W : IrreducibleCloseds X // x ∈ (W : Set X) ∧ (W : Set X) ⊆ D} :=
  Equiv.ofBijective (fun q => ⟨StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport X D x hxD q,
    point_mem_quotientSupport X D x hxD q, quotientSupport_subset_parent X D x hxD q⟩) (by
    constructor
    · intro q t h
      exact quotientSupport_injective X D x hxD (congrArg Subtype.val h)
    · intro W
      obtain ⟨q, hq⟩ := exists_quotientSupport X D x hxD W.val W.property.2 W.property.1
      exact ⟨q, Subtype.ext hq⟩)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientPoints.Constructions
