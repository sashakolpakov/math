import OAI.AlgebraicGeometry.CycleClass.Thom.VectorLocalFormula
import OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedOneSection

/-! # One Vector Local Formula -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.OneVectorLocalFormula.Constructions

noncomputable section

/-! The uniform local one-equation formula in an arbitrary specified
target grading, with its actual native Tor Euler coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.VectorLocalFormula.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedOneSection.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_one_local_formula (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p d : ℕ) (hd : p + 1 = d)
    (Z : Geometric.DimensionCycles.DimensionCycleSupport V d) (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
    (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 → IntersectionGeometry.supportPoint Z.val ∈ (D.val : Set V.carrier))
    (B : V.carrier.Opens) (hxB : IntersectionGeometry.supportPoint Z.val ∈ B) [Nonempty B]
    (s : Fin 1 → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
    (hr : IsWeaklyRegular (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val)) (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B (IntersectionGeometry.supportPoint Z.val) hxB 1 s))
    (hm : ∀ a ∈ Section.StalkMap.Constructions.VectorGerms.vectorGerms V B (IntersectionGeometry.supportPoint Z.val) hxB 1 s,
      a ∈ IsLocalRing.maximalIdeal (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val)))
    (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → ∀ hxD : IntersectionGeometry.supportPoint Z.val ∈ (D.val : Set V.carrier),
      PrimeSpectrum.zeroLocus
        (Ideal.ofList (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B (IntersectionGeometry.supportPoint Z.val) hxB 1 s) : Set (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))) ∩
        Module.support (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))
          (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val (IntersectionGeometry.supportPoint Z.val) hxD) ⊆
            {IsLocalRing.closedPoint (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))})
    (l : ℕ) :
    ∃ C : V.carrier.Opens, C ≤ B ∧ IntersectionGeometry.supportPoint Z.val ∈ C ∧
      VectorLocalFormula.Constructions.HasLocalVectorFormula V B p 1 d hd s c
        (Finsupp.single Z (Local.Euler.Constructions.localCycleEuler V p (IntersectionGeometry.supportPoint Z.val) (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B (IntersectionGeometry.supportPoint Z.val) hxB 1 s) l c)) C := by
  cases hd
  let x := IntersectionGeometry.supportPoint Z.val
  let R := V.carrier.presheaf.stalk x
  let r := s 0
  have hs : s = (fun _ => r) := funext (fun i => congrArg s (Subsingleton.elim i 0))
  have hr' : IsWeaklyRegular R [Section.StalkMap.Constructions.sectionStalkMap V B x hxB r] := by
    simpa only [hs, Section.StalkMap.Constructions.VectorGerms.vectorGerms_one] using hr
  have hm' : ∀ a ∈ [Section.StalkMap.Constructions.sectionStalkMap V B x hxB r], a ∈ IsLocalRing.maximalIdeal R := by
    simpa only [hs, Section.StalkMap.Constructions.VectorGerms.vectorGerms_one] using hm
  have hi' : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0),
      PrimeSpectrum.zeroLocus (Ideal.ofList [Section.StalkMap.Constructions.sectionStalkMap V B x hxB r] : Set R) ∩
        Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x (hc D hD)) ⊆ {IsLocalRing.closedPoint R} := by
    intro D hD
    simpa only [hs, Section.StalkMap.Constructions.VectorGerms.vectorGerms_one] using hi D hD (hc D hD)
  let c₁ := IsolatedOneSection.Constructions.Class.oneSectionStep V p Z c hc B hxB r hi'
  refine ⟨Cycle.AtPoint.Constructions.pointNeighborhood V (p + 1) x c₁ B, Cycle.AtPoint.Constructions.pointNeighborhood_le V (p + 1) x c₁ B,
    Cycle.AtPoint.Constructions.mem_pointNeighborhood V (p + 1) x c₁ B hxB, ?_⟩
  intro U hUC hUB L u hu hcu
  have h := IsolatedOneSection.Constructions.Class.cycleVectorClass_singleEuler V p Z c hc B hxB r hi' U hUB u hu hcu hr' hm' l hUC
  rw [hs, Section.StalkMap.Constructions.VectorGerms.vectorGerms_one]
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.OneVectorLocalFormula.Constructions
