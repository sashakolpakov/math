import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedIteratedTorEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.TorLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDimension

/-! # Triple Support Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TripleSupportEuler

noncomputable section

/-! At an expected-codimension component of a proper triple intersection,
the actual local support modules satisfy the iterated Tor Euler identity. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m d : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  (A B D : IrreducibleCloseds X.carrier)
  (hproper : ∀ E : IrreducibleCloseds X.carrier,
    (E : Set X.carrier) ⊆ ((A : Set X.carrier) ∩ B) ∩ D → d ≤ X.supportCodimension E)
  (C : X.DimensionCycleSupport d)
  (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A : Set X.carrier))
  (hxB : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (B : Set X.carrier))
  (hxD : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (D : Set X.carrier))

include m hproper in
theorem isolated :
    (Module.support (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA) ∩
      Module.support (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxB)) ∩
      Module.support (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier D (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxD) ⊆
      {IsLocalRing.closedPoint (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))} := by
  intro p hp
  let x := CycleClass.Thom.IntersectionGeometry.supportPoint C.val
  let z := X.carrier.fromSpecStalk x p
  let E : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm z
  have hzA : z ∈ (A : Set X.carrier) :=
    Local.SupportSpectrum.image_mem_support X.carrier A x hxA p hp.1.1
  have hzB : z ∈ (B : Set X.carrier) :=
    Local.SupportSpectrum.image_mem_support X.carrier B x hxB p hp.1.2
  have hzD : z ∈ (D : Set X.carrier) :=
    Local.SupportSpectrum.image_mem_support X.carrier D x hxD p hp.2
  have hE : (E : Set X.carrier) ⊆ ((A : Set X.carrier) ∩ B) ∩ D := by
    change closure {z} ⊆ _
    exact ((A.isClosed.inter B.isClosed).inter D.isClosed).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr ⟨⟨hzA, hzB⟩, hzD⟩)
  have hz : z ⤳ x := by
    have hr : z ∈ Set.range (X.carrier.fromSpecStalk x) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hr
  have hCE : C.val ≤ E := by
    apply (Supports.supportPoint_mem_iff_subset ⟨E, E.isClosed⟩ C.val).mp
    change x ∈ closure {z}
    exact hz.mem_closed isClosed_closure (subset_closure (Set.mem_singleton z))
  have he : C.val = E := by
    by_contra hne
    have ht := Supports.codimension_strictAnti X m (lt_of_le_of_ne hCE hne)
    have hd := hproper E hE
    rw [C.property] at ht
    omega
  have hzx : z = x :=
    (irreducibleSetEquivPoints.apply_symm_apply z).symm.trans (congrArg CycleClass.Thom.IntersectionGeometry.supportPoint he.symm)
  apply Set.mem_singleton_iff.mpr
  apply (X.carrier.fromSpecStalk x).isEmbedding.injective
  exact hzx.trans Scheme.fromSpecStalk_closedPoint.symm

include hproper in
theorem commute :
    IteratedTorEuler.euler (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier D (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxD)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxB)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA) m m =
    IteratedTorEuler.euler (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxB)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier D (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxD)
      (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA) m m := by
  let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
  let L := CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier D (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxD
  let M := CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxB
  let N := CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxA
  let : Module.Finite R L := Local.TorFinite.localSupportModule_finite _ _ _ _
  let : Module.Finite R M := Local.TorFinite.localSupportModule_finite _ _ _ _
  let : Module.Finite R N := Local.TorFinite.localSupportModule_finite _ _ _ _
  let : HasProjectiveDimensionLE L m := Smooth.StalkDimension.stalk_bound X.structureMap m _ L
  let : HasProjectiveDimensionLE M m := Smooth.StalkDimension.stalk_bound X.structureMap m _ M
  exact IsolatedIteratedTorEuler.commute R L M N m m (IsLocalRing.closedPoint R)
    (isolated X m d A B D hproper C hxA hxB hxD)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TripleSupportEuler
