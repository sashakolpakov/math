import OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalStepEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepCoefficients

/-! # Section Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler.Constructions

noncomputable section

/-! The native local Euler recursion holds for an arbitrary finite
original cycle and its actual section step. Components away from the
point contribute zero on both sides. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalStepEuler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.CycleSectionClass.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepCoefficients.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.Step.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.AdmissibleLift.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (B : V.carrier.Opens)
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (x : V.carrier) (hxB : x ∈ B)

theorem principalStep_euler_of_not_mem (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
    [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)] (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)
    (hxD : x ∉ (D.val : Set V.carrier)) (rs : List (V.carrier.presheaf.stalk x)) (d : ℕ) :
    Local.Euler.Constructions.localCycleEuler V (p + 1) x rs d (Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs) = 0 := by
  rw [Local.Euler.Constructions.localCycleEuler_eq_sum]
  apply Finset.sum_eq_zero
  intro C hC
  have hc := Finsupp.mem_support_iff.mp hC
  rw [Section.CupPrincipalGeneral.Constructions.Step.principalStep_coefficient] at hc
  have hCD := (Section.ClosedSupport.Constructions.Principal.principalCoefficient_support D B s C.val hc).1
  rw [Local.Euler.Constructions.supportEuler_of_not_mem V (p + 1) x rs d C (fun h => hxD (hCD h)), mul_zero]

theorem supportEuler_eq_principalStep (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
    [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)] (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)
    (rs : List (V.carrier.presheaf.stalk x))
    (hr : IsWeaklyRegular (V.carrier.presheaf.stalk x)
      (V.carrier.presheaf.germ B x hxB (B.topIso.hom s) :: rs))
    (hm : ∀ a ∈ V.carrier.presheaf.germ B x hxB (B.topIso.hom s) :: rs,
      a ∈ IsLocalRing.maximalIdeal (V.carrier.presheaf.stalk x))
    (hi : ∀ hxD : x ∈ (D.val : Set V.carrier),
      PrimeSpectrum.zeroLocus (Ideal.ofList (V.carrier.presheaf.germ B x hxB (B.topIso.hom s) :: rs) :
        Set (V.carrier.presheaf.stalk x)) ∩
        Module.support (V.carrier.presheaf.stalk x) (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) ⊆
          {IsLocalRing.closedPoint (V.carrier.presheaf.stalk x)})
    (d : ℕ) (hd : rs.length ≤ d) :
    Local.Euler.Constructions.supportEuler V p x (V.carrier.presheaf.germ B x hxB (B.topIso.hom s) :: rs) d D =
      Local.Euler.Constructions.localCycleEuler V (p + 1) x rs d (Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs) := by
  by_cases hxD : x ∈ (D.val : Set V.carrier)
  · exact (Local.Euler.Constructions.supportEuler_of_mem V p x _ d D hxD).trans
      (PrincipalStepEuler.Constructions.euler_eq_principalStep V D B s hs x hxD hxB rs hr hm (hi hxD) d hd)
  · exact (Local.Euler.Constructions.supportEuler_of_not_mem V p x _ d D hxD).trans
      (principalStep_euler_of_not_mem V p B s x D hs hxD rs d).symm

variable (U : Opens V.analyticSpace) {L : Type} (u : L → U) (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u)
  (hne : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B))
  (hs : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0), letI := hne D hD
    Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)

def originalPrincipalStepSum : Geometric.DimensionCycles.RationalDimensionCycle V (p + 1) :=
  ∑ D : c.support, letI := hne D.val (Finsupp.mem_support_iff.mp D.property)
    c D.val • Section.CupPrincipalGeneral.Constructions.Step.principalStep D.val B s (hs D.val (Finsupp.mem_support_iff.mp D.property))

theorem cycleSectionStep_eq_sum :
    CycleSectionClass.Constructions.cycleSectionStep V p B s U u c hc hne hs = originalPrincipalStepSum V p B s c hne hs := by
  rw [CycleSectionClass.Constructions.cycleSectionStep, Section.Step.Constructions.stepCycleMap, Section.AdmissibleLift.Constructions.admissibleCycle, Finsupp.linearCombination_mapDomain,
    SectionStepCoefficients.Constructions.linearCombination_nonzeroSubtype_eq_sum]
  rfl

theorem localCycleEuler_sectionStep (rs : List (V.carrier.presheaf.stalk x))
    (hr : IsWeaklyRegular (V.carrier.presheaf.stalk x)
      (V.carrier.presheaf.germ B x hxB (B.topIso.hom s) :: rs))
    (hm : ∀ a ∈ V.carrier.presheaf.germ B x hxB (B.topIso.hom s) :: rs,
      a ∈ IsLocalRing.maximalIdeal (V.carrier.presheaf.stalk x))
    (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → ∀ hxD : x ∈ (D.val : Set V.carrier),
      PrimeSpectrum.zeroLocus (Ideal.ofList (V.carrier.presheaf.germ B x hxB (B.topIso.hom s) :: rs) :
        Set (V.carrier.presheaf.stalk x)) ∩
        Module.support (V.carrier.presheaf.stalk x) (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) ⊆
          {IsLocalRing.closedPoint (V.carrier.presheaf.stalk x)})
    (d : ℕ) (hd : rs.length ≤ d) :
    Local.Euler.Constructions.localCycleEuler V p x (V.carrier.presheaf.germ B x hxB (B.topIso.hom s) :: rs) d c =
      Local.Euler.Constructions.localCycleEuler V (p + 1) x rs d (CycleSectionClass.Constructions.cycleSectionStep V p B s U u c hc hne hs) := by
  rw [cycleSectionStep_eq_sum, originalPrincipalStepSum, map_sum]
  refine (Local.Euler.Constructions.localCycleEuler_eq_sum V p x _ d c).trans ?_
  refine (Finset.sum_coe_sort c.support (fun D => c D * Local.Euler.Constructions.supportEuler V p x _ d D)).symm.trans ?_
  apply Finset.sum_congr rfl
  intro D _
  let := hne D.val (Finsupp.mem_support_iff.mp D.property)
  rw [map_smul]
  exact congrArg (fun a : ℚ => c D.val • a)
    (supportEuler_eq_principalStep V p B s x hxB D.val (hs D.val (Finsupp.mem_support_iff.mp D.property))
      rs hr hm (hi D.val (Finsupp.mem_support_iff.mp D.property)) d hd)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler.Constructions
