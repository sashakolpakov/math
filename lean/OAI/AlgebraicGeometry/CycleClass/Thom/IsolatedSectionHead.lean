import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportElementarySectionHead
import OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSupportAvoidance

/-! # Isolated Section Head -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSectionHead.Constructions

noncomputable section

/-! Isolated proper local equations admit a simultaneous actual
elementary section head for every nonzero component of the finite
cycle through the target generic point. Prime avoidance is derived. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportElementarySectionHead.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationNeighborhood.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p d : ℕ) (Z : Geometric.DimensionCycles.DimensionCycleSupport V d) (hp : p < d)
  (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 → IntersectionGeometry.supportPoint Z.val ∈ (D.val : Set V.carrier))
  (B : V.carrier.Opens) (hxB : IntersectionGeometry.supportPoint Z.val ∈ B) (r : Γ(V.carrier, B)) (rs : List Γ(V.carrier, B))

local notation "x" => OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry.supportPoint Z.val
local notation "R" => V.carrier.presheaf.stalk (OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry.supportPoint Z.val)
local notation "gB" => V.carrier.presheaf.germ B (OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry.supportPoint Z.val) hxB

include hp in
theorem exists_elementary_head
    (hr : IsWeaklyRegular R (gB r :: rs.map gB))
    (hm : ∀ a ∈ gB r :: rs.map gB, a ∈ IsLocalRing.maximalIdeal R)
    (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0),
      PrimeSpectrum.zeroLocus (Ideal.ofList (gB r :: rs.map gB) : Set R) ∩
        Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x (hc D hD)) ⊆ {IsLocalRing.closedPoint R}) :
    ∃ C : V.carrier.Opens, ∃ hCB : C ≤ B, ∃ hxC : x ∈ C, ∃ s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤),
      C.topIso.hom s - V.carrier.presheaf.map (homOfLE hCB).op r ∈
        Ideal.ofList (rs.map (V.carrier.presheaf.map (homOfLE hCB).op)) ∧
      Ideal.ofList (C.topIso.hom s :: rs.map (V.carrier.presheaf.map (homOfLE hCB).op)) =
        Ideal.ofList ((r :: rs).map (V.carrier.presheaf.map (homOfLE hCB).op)) ∧
      IsWeaklyRegular R (V.carrier.presheaf.germ C x hxC (C.topIso.hom s) :: rs.map gB) ∧
      (∀ a ∈ V.carrier.presheaf.germ C x hxC (C.topIso.hom s) :: rs.map gB,
        a ∈ IsLocalRing.maximalIdeal R) ∧
      ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0),
        letI := Affine.NormalizationNeighborhood.Constructions.normalizationBase_nonempty D C x (hc D hD) hxC
        Affine.SectionFunction.Constructions.parentSectionFunction D C s ≠ 0 := by
  let D : c.support → Geometric.DimensionCycles.DimensionCycleSupport V p := Subtype.val
  let hD := fun i : c.support => hc i.val (Finsupp.mem_support_iff.mp i.property)
  have hI : ∀ i : c.support, ¬ Ideal.ofList (gB r :: rs.map gB) ≤
      (StalkPrimeQuotient.Constructions.kernelPrime V.carrier (D i).val x (hD i)).asIdeal := by
    intro i
    exact IsolatedSupportAvoidance.Constructions.ideal_not_le_supportKernel V p d (D i) Z hp (hD i)
      (gB r :: rs.map gB) (hi i.val (Finsupp.mem_support_iff.mp i.property))
  obtain ⟨C, hCB, hxC, s, he, hgen, hreg, hmax, hn⟩ :=
    Finite.SupportElementarySectionHead.Constructions.exists_elementary_section_head V p x D hD B hxB r rs hr hm hI
  refine ⟨C, hCB, hxC, s, he, hgen, hreg, hmax, ?_⟩
  intro W hW
  exact hn ⟨W, Finsupp.mem_support_iff.mpr hW⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSectionHead.Constructions
