import OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSectionHead
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction

/-! # Isolated Vector Section Head -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedVectorSectionHead.Constructions

noncomputable section

/-! Simultaneous head selection for the actual finite section vector,
with the precise global tail-ideal condition needed by its homotopy. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedSectionHead.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationNeighborhood.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p d : ℕ) (Z : Geometric.DimensionCycles.DimensionCycleSupport V d) (hp : p < d)
  (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 → IntersectionGeometry.supportPoint Z.val ∈ (D.val : Set V.carrier))
  (B : V.carrier.Opens) (hxB : IntersectionGeometry.supportPoint Z.val ∈ B)
  (n : ℕ) (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))

local notation "x" => OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry.supportPoint Z.val
local notation "R" => V.carrier.presheaf.stalk (OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry.supportPoint Z.val)
local notation "gB" => (fun a => V.carrier.presheaf.germ B (OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry.supportPoint Z.val) hxB (B.topIso.hom a))

include hp in
theorem exists_vector_head
    (hr : IsWeaklyRegular R (gB r :: (List.ofFn s).map gB))
    (hm : ∀ a ∈ gB r :: (List.ofFn s).map gB, a ∈ IsLocalRing.maximalIdeal R)
    (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0),
      PrimeSpectrum.zeroLocus (Ideal.ofList (gB r :: (List.ofFn s).map gB) : Set R) ∩
        Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x (hc D hD)) ⊆ {IsLocalRing.closedPoint R}) :
    ∃ C : V.carrier.Opens, ∃ hCB : C ≤ B, ∃ hxC : x ∈ C, ∃ a : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤),
      a - Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB r ∈ Ideal.span (Set.range (fun i => Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i))) ∧
      IsWeaklyRegular R (V.carrier.presheaf.germ C x hxC (C.topIso.hom a) :: (List.ofFn s).map gB) ∧
      (∀ b ∈ V.carrier.presheaf.germ C x hxC (C.topIso.hom a) :: (List.ofFn s).map gB,
        b ∈ IsLocalRing.maximalIdeal R) ∧
      ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0),
        letI := Affine.NormalizationNeighborhood.Constructions.normalizationBase_nonempty D C x (hc D hD) hxC
        Affine.SectionFunction.Constructions.parentSectionFunction D C a ≠ 0 := by
  have hr' : IsWeaklyRegular R (V.carrier.presheaf.germ B x hxB (B.topIso.hom r) ::
      ((List.ofFn s).map B.topIso.hom).map (V.carrier.presheaf.germ B x hxB)) := by
    simpa only [List.map_map, Function.comp_def] using hr
  have hm' : ∀ a ∈ V.carrier.presheaf.germ B x hxB (B.topIso.hom r) ::
      ((List.ofFn s).map B.topIso.hom).map (V.carrier.presheaf.germ B x hxB), a ∈ IsLocalRing.maximalIdeal R := by
    simpa only [List.map_map, Function.comp_def] using hm
  have hi' : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0),
      PrimeSpectrum.zeroLocus (Ideal.ofList (V.carrier.presheaf.germ B x hxB (B.topIso.hom r) ::
        ((List.ofFn s).map B.topIso.hom).map (V.carrier.presheaf.germ B x hxB)) : Set R) ∩
        Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x (hc D hD)) ⊆ {IsLocalRing.closedPoint R} := by
    simpa only [List.map_map, Function.comp_def] using hi
  obtain ⟨C, hCB, hxC, a, hdiff, _, hreg, hmax, hn⟩ :=
    IsolatedSectionHead.Constructions.exists_elementary_head V p d Z hp c hc B hxB (B.topIso.hom r) ((List.ofFn s).map B.topIso.hom) hr' hm' hi'
  refine ⟨C, hCB, hxC, a, ?_, ?_, ?_, hn⟩
  · have h := Section.BaseRestriction.Constructions.HeadDifference.head_difference_mem V B C hCB r (List.ofFn s) a hdiff
    rw [List.map_ofFn] at h
    have he : Ideal.ofList (List.ofFn (fun i => Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i))) =
        Ideal.span (Set.range (fun i => Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i))) := by
      apply congrArg Ideal.span
      ext b
      exact List.mem_ofFn' _ b
    exact (congrArg (fun I : Ideal Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤) => a - Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB r ∈ I) he).mp h
  · simpa only [List.map_map, Function.comp_def] using hreg
  · simpa only [List.map_map, Function.comp_def] using hmax

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedVectorSectionHead.Constructions
