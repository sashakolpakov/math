import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalStepIsolation

/-! # Section Step Isolation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepIsolation.Constructions

/-! The native isolated-intersection condition passes to every
nonzero component of the actual finite section-step cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.CycleSectionClass.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepCoefficients.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalStepIsolation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.Principal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (B : V.carrier.Opens)
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (x : V.carrier) (hxB : x ∈ B)
  (U : Opens V.analyticSpace) {L : Type} (u : L → U) (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u)
  (hne : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B))
  (hs : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0), letI := hne D hD
    Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)

local notation "R" => V.carrier.presheaf.stalk x
local notation "r" => V.carrier.presheaf.germ B x hxB (B.topIso.hom s)

theorem cycleSectionStep_isolated_tail (rs : List R)
    (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → ∀ hxD : x ∈ (D.val : Set V.carrier),
      PrimeSpectrum.zeroLocus (Ideal.ofList (r :: rs) : Set R) ∩
        Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) ⊆ {IsLocalRing.closedPoint R})
    (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1))
    (hC : CycleSectionClass.Constructions.cycleSectionStep V p B s U u c hc hne hs C ≠ 0) (hxC : x ∈ (C.val : Set V.carrier)) :
    PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) ∩
      Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier C.val x hxC) ⊆ {IsLocalRing.closedPoint R} := by
  rw [SectionStepCoefficients.Constructions.cycleSectionStep_coefficient] at hC
  obtain ⟨D, _, hD⟩ := Finset.exists_ne_zero_of_sum_ne_zero hC
  let hcoef := Finsupp.mem_support_iff.mp D.property
  let := hne D.val hcoef
  have horder : IntersectionGeometry.principalDivisorCoefficient V.presentation D.val.val (Affine.SectionFunction.Constructions.parentSectionFunction D.val B s) C.val ≠ 0 :=
    (mul_ne_zero_iff.mp hD).2
  have hCD := (Section.ClosedSupport.Constructions.Principal.principalCoefficient_support D.val B s C.val horder).1
  have hstep : Section.CupPrincipalGeneral.Constructions.Step.principalStep D.val B s (hs D.val hcoef) C ≠ 0 := by
    rw [Section.CupPrincipalGeneral.Constructions.Step.principalStep_coefficient]
    exact horder
  exact PrincipalStepIsolation.Constructions.principalStep_isolated_tail V D.val B s (hs D.val hcoef) x (hCD hxC) hxB C hxC hstep rs
    (hi D.val hcoef (hCD hxC))

end AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepIsolation.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepIsolation.Constructions.ReferencePrincipalSum

/-! Original principal-step sums without auxiliary analytic-support
parameters, retaining their exact coefficients and local Tor recursion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.CycleSectionClass.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepIsolation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.Principal OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (B : V.carrier.Opens) (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
  (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hne : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B))
  (hs : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0), letI := hne D hD
    Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)

theorem exists_parent_of_step_coefficient (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1))
    (hC : SectionEuler.Constructions.originalPrincipalStepSum V p B s c hne hs C ≠ 0) :
    ∃ D : c.support, letI := hne D.val (Finsupp.mem_support_iff.mp D.property)
      Section.CupPrincipalGeneral.Constructions.Step.principalStep D.val B s (hs D.val (Finsupp.mem_support_iff.mp D.property)) C ≠ 0 := by
  rw [SectionEuler.Constructions.originalPrincipalStepSum, Finsupp.finsetSum_apply] at hC
  obtain ⟨D, _, hD⟩ := Finset.exists_ne_zero_of_sum_ne_zero hC
  let := hne D.val (Finsupp.mem_support_iff.mp D.property)
  refine ⟨D, ?_⟩
  change c D.val * Section.CupPrincipalGeneral.Constructions.Step.principalStep D.val B s (hs D.val (Finsupp.mem_support_iff.mp D.property)) C ≠ 0 at hD
  exact (mul_ne_zero_iff.mp hD).2

theorem step_support (F : Closeds V.carrier)
    (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 → (D.val : Set V.carrier) ⊆ F)
    (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1)) (hC : SectionEuler.Constructions.originalPrincipalStepSum V p B s c hne hs C ≠ 0) :
    (C.val : Set V.carrier) ⊆ F ∧
      ∀ x : V.carrier, x ∈ (C.val : Set V.carrier) → x ∉ V.carrier.basicOpen (B.topIso.hom s) := by
  obtain ⟨D, hD⟩ := exists_parent_of_step_coefficient V p B s c hne hs C hC
  let := hne D.val (Finsupp.mem_support_iff.mp D.property)
  rw [Section.CupPrincipalGeneral.Constructions.Step.principalStep_coefficient] at hD
  obtain ⟨hCD, hz⟩ := Section.ClosedSupport.Constructions.Principal.principalCoefficient_support D.val B s C.val hD
  exact ⟨hCD.trans (hc D.val (Finsupp.mem_support_iff.mp D.property)), hz⟩

variable (x : V.carrier) (hxB : x ∈ B) (rs : List (V.carrier.presheaf.stalk x))

local notation "R" => V.carrier.presheaf.stalk x
local notation "r" => V.carrier.presheaf.germ B x hxB (B.topIso.hom s)

theorem localCycleEuler_step (hr : IsWeaklyRegular R (r :: rs))
    (hm : ∀ a ∈ r :: rs, a ∈ IsLocalRing.maximalIdeal R)
    (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → ∀ hxD : x ∈ (D.val : Set V.carrier),
      PrimeSpectrum.zeroLocus (Ideal.ofList (r :: rs) : Set R) ∩
        Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) ⊆ {IsLocalRing.closedPoint R})
    (d : ℕ) (hd : rs.length ≤ d) :
    Local.Euler.Constructions.localCycleEuler V p x (r :: rs) d c =
      Local.Euler.Constructions.localCycleEuler V (p + 1) x rs d (SectionEuler.Constructions.originalPrincipalStepSum V p B s c hne hs) := by
  let U : Opens V.analyticSpace := ⊤
  let u : U → U := id
  have hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u :=
    fun _ _ z _ => ⟨z, rfl⟩
  have h := SectionEuler.Constructions.localCycleEuler_sectionStep V p B s x hxB U u c hc hne hs rs hr hm hi d hd
  rwa [SectionEuler.Constructions.cycleSectionStep_eq_sum] at h

theorem isolated_tail
    (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → ∀ hxD : x ∈ (D.val : Set V.carrier),
      PrimeSpectrum.zeroLocus (Ideal.ofList (r :: rs) : Set R) ∩
        Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) ⊆ {IsLocalRing.closedPoint R})
    (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1)) (hC : SectionEuler.Constructions.originalPrincipalStepSum V p B s c hne hs C ≠ 0)
    (hxC : x ∈ (C.val : Set V.carrier)) :
    PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) ∩
      Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier C.val x hxC) ⊆ {IsLocalRing.closedPoint R} := by
  obtain ⟨D, hD⟩ := exists_parent_of_step_coefficient V p B s c hne hs C hC
  let hcoef := Finsupp.mem_support_iff.mp D.property
  let := hne D.val hcoef
  have horder := hD
  rw [Section.CupPrincipalGeneral.Constructions.Step.principalStep_coefficient] at horder
  have hCD := (Section.ClosedSupport.Constructions.Principal.principalCoefficient_support D.val B s C.val horder).1
  exact PrincipalStepIsolation.Constructions.principalStep_isolated_tail V D.val B s (hs D.val hcoef) x (hCD hxC) hxB
    C hxC hD rs (hi D.val hcoef (hCD hxC))

end AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepIsolation.Constructions.ReferencePrincipalSum

end

end OAI
