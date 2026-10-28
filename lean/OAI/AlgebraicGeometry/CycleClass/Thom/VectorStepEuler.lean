import OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepIsolation
import OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerIdeal
import OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerFilter

/-! # Vector Step Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.VectorStepEuler.Constructions

noncomputable section

/-! The exact native Tor recursion for an elementary section-head
change followed by the original principal cycle and point filtering. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepIsolation.Constructions.ReferencePrincipalSum OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerIdeal.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerFilter.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.ResidualTailAmbientEuler.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p n : ℕ) (B C : V.carrier.Opens) (hCB : C ≤ B)
  (x : V.carrier) (hxC : x ∈ C) (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
  (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (a : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤))
  (ha : a - Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB r ∈ Ideal.span (Set.range (fun i => Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i))))
  (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hne : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 → Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ C))
  (hs : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0), letI := hne D hD
    Affine.SectionFunction.Constructions.parentSectionFunction D C a ≠ 0)

local notation "R" => V.carrier.presheaf.stalk x
local notation "sC" => (fun i => OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i))
local notation "old" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms.vectorGerms V B x (hCB hxC) (n + 1) (Fin.cons r s)
local notation "new" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms.vectorGerms V C x hxC (n + 1) (Fin.cons a sC)
local notation "tail" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms.vectorGerms V C x hxC n sC
local notation "c₁" => OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler.Constructions.originalPrincipalStepSum V p C a c hne hs
local notation "c₂" => OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions.cycleAtPoint V (p + 1) x c₁

include ha in
theorem changed_isolated
    (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → ∀ hxD : x ∈ (D.val : Set V.carrier),
      PrimeSpectrum.zeroLocus (Ideal.ofList old : Set R) ∩
        Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) ⊆ {IsLocalRing.closedPoint R})
    (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0) (hxD : x ∈ (D.val : Set V.carrier)) :
    PrimeSpectrum.zeroLocus (Ideal.ofList new : Set R) ∩
      Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) ⊆ {IsLocalRing.closedPoint R} := by
  rw [Section.StalkMap.Constructions.VectorGerms.vectorGerms_head_ideal V B C hCB x hxC n r s a ha]
  exact hi D hD hxD

theorem tail_regular (hr : IsWeaklyRegular R new)
    (hm : ∀ b ∈ new, b ∈ IsLocalRing.maximalIdeal R) : IsWeaklyRegular R tail := by
  rw [Section.StalkMap.Constructions.VectorGerms.vectorGerms_cons] at hr hm
  exact ResidualTailAmbientEuler.Constructions.regular_tail_ambient R (Section.StalkMap.Constructions.sectionStalkMap V C x hxC a) tail hr hm

theorem tail_maximal (hm : ∀ b ∈ new, b ∈ IsLocalRing.maximalIdeal R) :
    ∀ b ∈ tail, b ∈ IsLocalRing.maximalIdeal R := by
  rw [Section.StalkMap.Constructions.VectorGerms.vectorGerms_cons] at hm
  exact fun b hb => hm b (List.mem_cons_of_mem _ hb)

include ha in
theorem filtered_step_isolated
    (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → ∀ hxD : x ∈ (D.val : Set V.carrier),
      PrimeSpectrum.zeroLocus (Ideal.ofList old : Set R) ∩
        Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) ⊆ {IsLocalRing.closedPoint R})
    (D : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1)) (hD : c₂ D ≠ 0) (hxD : x ∈ (D.val : Set V.carrier)) :
    PrimeSpectrum.zeroLocus (Ideal.ofList tail : Set R) ∩
      Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) ⊆ {IsLocalRing.closedPoint R} := by
  have hnew := changed_isolated V p n B C hCB x hxC r s a ha c hi
  simp only [Section.StalkMap.Constructions.VectorGerms.vectorGerms_cons] at hnew
  exact Finite.SectionStepIsolation.Constructions.ReferencePrincipalSum.isolated_tail V p C a c hne hs x hxC tail hnew D
    (Cycle.AtPoint.Constructions.cycleAtPoint_ne_zero V (p + 1) x c₁ D hD).1 hxD

include ha in
theorem filtered_step_euler (hr : IsWeaklyRegular R new)
    (hm : ∀ b ∈ new, b ∈ IsLocalRing.maximalIdeal R)
    (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → ∀ hxD : x ∈ (D.val : Set V.carrier),
      PrimeSpectrum.zeroLocus (Ideal.ofList old : Set R) ∩
        Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) ⊆ {IsLocalRing.closedPoint R})
    (l : ℕ) (hl : n ≤ l) :
    Local.Euler.Constructions.localCycleEuler V p x old l c = Local.Euler.Constructions.localCycleEuler V (p + 1) x tail l c₂ := by
  have he := Section.StalkMap.Constructions.VectorGerms.vectorGerms_head_ideal V B C hCB x hxC n r s a ha
  have hideal := LinearMap.congr_fun (Local.EulerIdeal.Constructions.localCycleEuler_ideal_eq V p x old new he.symm l) c
  have hnew := changed_isolated V p n B C hCB x hxC r s a ha c hi
  rw [Section.StalkMap.Constructions.VectorGerms.vectorGerms_cons] at hr hm hnew
  have hstep := Finite.SectionStepIsolation.Constructions.ReferencePrincipalSum.localCycleEuler_step V p C a c hne hs x hxC tail hr hm hnew l
    ((Section.StalkMap.Constructions.VectorGerms.vectorGerms_length V C x hxC n sC).le.trans hl)
  have hstep' : Local.Euler.Constructions.localCycleEuler V p x new l c = Local.Euler.Constructions.localCycleEuler V (p + 1) x tail l c₁ := by
    rw [Section.StalkMap.Constructions.VectorGerms.vectorGerms_cons]
    change Local.Euler.Constructions.localCycleEuler V p x
      (V.carrier.presheaf.germ C x hxC (C.topIso.hom a) :: tail) l c = _
    exact hstep
  exact hideal.trans (hstep'.trans (Local.EulerFilter.Constructions.localCycleEuler_cycleAtPoint V (p + 1) x tail l c₁).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.VectorStepEuler.Constructions
