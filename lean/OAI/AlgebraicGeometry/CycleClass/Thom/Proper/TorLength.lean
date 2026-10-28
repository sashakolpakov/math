import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.LocalSupportSpectrum
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.FiniteLength
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

/-! # Tor Length -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Proper.TorLength

noncomputable section

/-! At a component of a proper intersection, the two local supports meet
only at the closed point of the ambient local spectrum. Consequently all
of ThomClass's actual local Tor lengths are finite. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem local_support_intersection_subset (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (d : ℕ) (A B : IrreducibleCloseds X.carrier)
    (hproper : ∀ D : IrreducibleCloseds X.carrier,
      (D : Set X.carrier) ⊆ (A : Set X.carrier) ∩ B → d ≤ X.supportCodimension D)
    (C : X.DimensionCycleSupport d) (hxA : IntersectionGeometry.supportPoint C.val ∈ (A : Set X.carrier))
    (hxB : IntersectionGeometry.supportPoint C.val ∈ (B : Set X.carrier)) :
    Module.support (X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val))
      (IntersectionGeometry.localSupportModule X.carrier A (IntersectionGeometry.supportPoint C.val) hxA) ∩
    Module.support (X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val))
      (IntersectionGeometry.localSupportModule X.carrier B (IntersectionGeometry.supportPoint C.val) hxB) ⊆
        {IsLocalRing.closedPoint (X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val))} := by
  intro p hp
  let x := IntersectionGeometry.supportPoint C.val
  let z := X.carrier.fromSpecStalk x p
  let D : IrreducibleCloseds X.carrier := irreducibleSetEquivPoints.symm z
  have hzA : z ∈ (A : Set X.carrier) :=
    TorAlgebra.LocalSupportSpectrum.image_mem_support X.carrier A x hxA p hp.1
  have hzB : z ∈ (B : Set X.carrier) :=
    TorAlgebra.LocalSupportSpectrum.image_mem_support X.carrier B x hxB p hp.2
  have hD : (D : Set X.carrier) ⊆ (A : Set X.carrier) ∩ B := by
    change closure {z} ⊆ _
    exact (A.isClosed.inter B.isClosed).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr ⟨hzA, hzB⟩)
  have hz : z ⤳ x := by
    have hr : z ∈ Set.range (X.carrier.fromSpecStalk x) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hr
  have hCD : C.val ≤ D := by
    apply (Intersection.Supports.supportPoint_mem_iff_subset ⟨D, D.isClosed⟩ C.val).mp
    change x ∈ closure {z}
    exact hz.mem_closed isClosed_closure (subset_closure (Set.mem_singleton z))
  have he : C.val = D := by
    by_contra hne
    have ht := Intersection.Supports.codimension_strictAnti X (lt_of_le_of_ne hCD hne)
    have hd := hproper D hD
    rw [C.property] at ht
    omega
  have hzx : z = x := by
    exact (irreducibleSetEquivPoints.apply_symm_apply z).symm.trans
      (congrArg IntersectionGeometry.supportPoint he.symm)
  apply Set.mem_singleton_iff.mpr
  apply (X.carrier.fromSpecStalk x).isEmbedding.injective
  exact hzx.trans Scheme.fromSpecStalk_closedPoint.symm

theorem localTorLength_ne_top (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (d : ℕ) (A B : IrreducibleCloseds X.carrier)
    (hproper : ∀ D : IrreducibleCloseds X.carrier,
      (D : Set X.carrier) ⊆ (A : Set X.carrier) ∩ B → d ≤ X.supportCodimension D)
    (C : X.DimensionCycleSupport d) (hxA : IntersectionGeometry.supportPoint C.val ∈ (A : Set X.carrier))
    (hxB : IntersectionGeometry.supportPoint C.val ∈ (B : Set X.carrier)) (n : ℕ) :
    IntersectionGeometry.localTorLength X.carrier A B (IntersectionGeometry.supportPoint C.val) hxA hxB n ≠ ⊤ := by
  let := TorAlgebra.LocalFinite.Tor.localSupportModule_finite X.carrier A (IntersectionGeometry.supportPoint C.val) hxA
  let := TorAlgebra.LocalFinite.Tor.localSupportModule_finite X.carrier B (IntersectionGeometry.supportPoint C.val) hxB
  exact TorAlgebra.FiniteLength.Tor.tor_length_ne_top _ _ _ _
    (local_support_intersection_subset X d A B hproper C hxA hxB) n

theorem localTorLength_ne_top_of_meetProperly (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (h : IntersectionGeometry.MeetProperly X p q a b) (A : X.DimensionCycleSupport p) (hA : A ∈ a.support)
    (B : X.DimensionCycleSupport q) (hB : B ∈ b.support) (C : X.DimensionCycleSupport (p + q))
    (hxA : IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (hxB : IntersectionGeometry.supportPoint C.val ∈ (B.val : Set X.carrier)) (n : ℕ) :
    IntersectionGeometry.localTorLength X.carrier A.val B.val (IntersectionGeometry.supportPoint C.val) hxA hxB n ≠ ⊤ :=
  localTorLength_ne_top X (p + q) A.val B.val (h A hA B hB) C hxA hxB n

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Proper.TorLength
