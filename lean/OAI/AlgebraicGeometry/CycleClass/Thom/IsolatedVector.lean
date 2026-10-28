import OAI.AlgebraicGeometry.CycleClass.Thom.OneVectorLocalFormula
import OAI.AlgebraicGeometry.CycleClass.Thom.VectorStepEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedVectorSectionHead

/-! # Isolated Vector -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.IsolatedVector.Constructions.Class

/-! The actual cycle-vector class at an isolated target component is
the original target cycle with its native Serre--Tor Euler coefficient.
The proof is induction through genuine principal-divisor cycles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.VectorLocalFormula.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.OneVectorLocalFormula.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedVectorSectionHead.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.VectorStepEuler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationNeighborhood.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference
open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_local_vector_formula (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (d : ℕ) (Z : Geometric.DimensionCycles.DimensionCycleSupport V d)
    (n p : ℕ) (hd : p + (n + 1) = d) (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
    (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 → IntersectionGeometry.supportPoint Z.val ∈ (D.val : Set V.carrier))
    (B : V.carrier.Opens) (hxB : IntersectionGeometry.supportPoint Z.val ∈ B) [Nonempty B]
    (s : Fin (n + 1) → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
    (hr : IsWeaklyRegular (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))
      (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B (IntersectionGeometry.supportPoint Z.val) hxB (n + 1) s))
    (hm : ∀ a ∈ Section.StalkMap.Constructions.VectorGerms.vectorGerms V B (IntersectionGeometry.supportPoint Z.val) hxB (n + 1) s,
      a ∈ IsLocalRing.maximalIdeal (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val)))
    (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → ∀ hxD : IntersectionGeometry.supportPoint Z.val ∈ (D.val : Set V.carrier),
      PrimeSpectrum.zeroLocus
        (Ideal.ofList (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B (IntersectionGeometry.supportPoint Z.val) hxB (n + 1) s) : Set (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))) ∩
        Module.support (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))
          (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val (IntersectionGeometry.supportPoint Z.val) hxD) ⊆
            {IsLocalRing.closedPoint (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))})
    (l : ℕ) (hl : n ≤ l) :
    ∃ C : V.carrier.Opens, C ≤ B ∧ IntersectionGeometry.supportPoint Z.val ∈ C ∧
      VectorLocalFormula.Constructions.HasLocalVectorFormula V B p (n + 1) d hd s c
        (Finsupp.single Z (Local.Euler.Constructions.localCycleEuler V p (IntersectionGeometry.supportPoint Z.val)
          (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B (IntersectionGeometry.supportPoint Z.val) hxB (n + 1) s) l c)) C := by
  induction n generalizing p B with
  | zero =>
      exact OneVectorLocalFormula.Constructions.exists_one_local_formula V p d hd Z c hc B hxB s hr hm hi l
  | succ n ih =>
      let x := IntersectionGeometry.supportPoint Z.val
      let R := V.carrier.presheaf.stalk x
      let r := s 0
      let t := Fin.tail s
      have heta : Fin.cons r t = s := Fin.cons_self_tail s
      have hr₀ : IsWeaklyRegular R (Section.StalkMap.Constructions.sectionStalkMap V B x hxB r :: Section.StalkMap.Constructions.VectorGerms.vectorGerms V B x hxB (n + 1) t) := by
        rw [← heta, Section.StalkMap.Constructions.VectorGerms.vectorGerms_cons] at hr
        exact hr
      have hm₀ : ∀ a ∈ Section.StalkMap.Constructions.sectionStalkMap V B x hxB r :: Section.StalkMap.Constructions.VectorGerms.vectorGerms V B x hxB (n + 1) t,
          a ∈ IsLocalRing.maximalIdeal R := by
        rw [← heta, Section.StalkMap.Constructions.VectorGerms.vectorGerms_cons] at hm
        exact hm
      have hi₀ : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0),
          PrimeSpectrum.zeroLocus
            (Ideal.ofList (Section.StalkMap.Constructions.sectionStalkMap V B x hxB r :: Section.StalkMap.Constructions.VectorGerms.vectorGerms V B x hxB (n + 1) t) : Set R) ∩
            Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x (hc D hD)) ⊆ {IsLocalRing.closedPoint R} := by
        intro D hD
        have h := hi D hD (hc D hD)
        rw [← heta, Section.StalkMap.Constructions.VectorGerms.vectorGerms_cons] at h
        exact h
      obtain ⟨C, hCB, hxC, a, ha, hreg, hmax, hs⟩ :=
        IsolatedVectorSectionHead.Constructions.exists_vector_head V p d Z (by omega) c hc B hxB (n + 1) r t hr₀ hm₀ hi₀
      let : Nonempty C := ⟨⟨x, hxC⟩⟩
      let tC := fun i => Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (t i)
      let hne := fun D hD => Affine.NormalizationNeighborhood.Constructions.normalizationBase_nonempty D C x (hc D hD) hxC
      let c₁ := Finite.SectionEuler.Constructions.originalPrincipalStepSum V p C a c hne hs
      let c₂ := Cycle.AtPoint.Constructions.cycleAtPoint V (p + 1) x c₁
      have hc₂ : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1), c₂ D ≠ 0 → x ∈ (D.val : Set V.carrier) :=
        fun D hD => (Cycle.AtPoint.Constructions.cycleAtPoint_ne_zero V (p + 1) x c₁ D hD).2
      have hrC : IsWeaklyRegular R (Section.StalkMap.Constructions.VectorGerms.vectorGerms V C x hxC ((n + 1) + 1) (Fin.cons a tC)) := by
        rw [Section.StalkMap.Constructions.VectorGerms.vectorGerms_cons, Section.StalkMap.Constructions.VectorGerms.vectorGerms_restrict]
        exact hreg
      have hmC : ∀ b ∈ Section.StalkMap.Constructions.VectorGerms.vectorGerms V C x hxC ((n + 1) + 1) (Fin.cons a tC),
          b ∈ IsLocalRing.maximalIdeal R := by
        rw [Section.StalkMap.Constructions.VectorGerms.vectorGerms_cons, Section.StalkMap.Constructions.VectorGerms.vectorGerms_restrict]
        exact hmax
      have hiOld : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → ∀ hxD : x ∈ (D.val : Set V.carrier),
          PrimeSpectrum.zeroLocus (Ideal.ofList (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B x (hCB hxC) ((n + 1) + 1) (Fin.cons r t)) : Set R) ∩
            Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) ⊆ {IsLocalRing.closedPoint R} := by
        rw [heta]
        exact hi
      have hrT : IsWeaklyRegular R (Section.StalkMap.Constructions.VectorGerms.vectorGerms V C x hxC (n + 1) tC) :=
        VectorStepEuler.Constructions.tail_regular V (n + 1) B C hCB x hxC t a hrC hmC
      have hmT : ∀ b ∈ Section.StalkMap.Constructions.VectorGerms.vectorGerms V C x hxC (n + 1) tC, b ∈ IsLocalRing.maximalIdeal R :=
        VectorStepEuler.Constructions.tail_maximal V (n + 1) B C hCB x hxC t a hmC
      have hiT : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1)), c₂ D ≠ 0 → ∀ hxD : x ∈ (D.val : Set V.carrier),
          PrimeSpectrum.zeroLocus (Ideal.ofList (Section.StalkMap.Constructions.VectorGerms.vectorGerms V C x hxC (n + 1) tC) : Set R) ∩
            Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) ⊆ {IsLocalRing.closedPoint R} :=
        VectorStepEuler.Constructions.filtered_step_isolated V p (n + 1) B C hCB x hxC r t a ha c hne hs hiOld
      have hE : Local.Euler.Constructions.localCycleEuler V p x (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B x hxB ((n + 1) + 1) s) l c =
          Local.Euler.Constructions.localCycleEuler V (p + 1) x (Section.StalkMap.Constructions.VectorGerms.vectorGerms V C x hxC (n + 1) tC) l c₂ := by
        have h := VectorStepEuler.Constructions.filtered_step_euler V p (n + 1) B C hCB x hxC r t a ha c hne hs hrC hmC hiOld l hl
        rw [heta] at h
        exact h
      obtain ⟨D, hDC, hxD, hformula⟩ := ih (p := p + 1) (hd := by omega) (c := c₂) (hc := hc₂)
        (B := C) (hxB := hxC) (s := tC) (hr := hrT) (hm := hmT) (hi := hiT) (hl := by omega)
      let N := Cycle.AtPoint.Constructions.pointNeighborhood V (p + 1) x c₁ C
      refine ⟨D ⊓ N, inf_le_left.trans (hDC.trans hCB),
        ⟨hxD, Cycle.AtPoint.Constructions.mem_pointNeighborhood V (p + 1) x c₁ C hxC⟩, ?_⟩
      have hstep := VectorLocalFormula.Constructions.localFormula_of_filtered_step V p (n + 1) d hd B C hCB x r t a ha c hne hs
        (Finsupp.single Z (Local.Euler.Constructions.localCycleEuler V p x (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B x hxB ((n + 1) + 1) s) l c)) D hDC
      rw [hE] at hstep
      have hresult := hstep hformula
      rw [heta, ← hE] at hresult
      exact hresult

end AlgebraicGeometry.CycleClass.Thom.IsolatedVector.Constructions.Class

namespace AlgebraicGeometry.CycleClass.Thom.IsolatedVector.Constructions.ClassGeneral

/-! The isolated section-vector formula for an arbitrary finite cycle.
Components away from the target generic point are removed on an actual
algebraic neighborhood, and their native local Euler terms are zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.VectorLocalFormula.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedVector.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerFilter.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorFilter.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_local_vector_formula (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (d : ℕ) (Z : Geometric.DimensionCycles.DimensionCycleSupport V d)
    (n p : ℕ) (hd : p + (n + 1) = d) (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
    (B : V.carrier.Opens) (hxB : IntersectionGeometry.supportPoint Z.val ∈ B) [Nonempty B]
    (s : Fin (n + 1) → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
    (hr : IsWeaklyRegular (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))
      (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B (IntersectionGeometry.supportPoint Z.val) hxB (n + 1) s))
    (hm : ∀ a ∈ Section.StalkMap.Constructions.VectorGerms.vectorGerms V B (IntersectionGeometry.supportPoint Z.val) hxB (n + 1) s,
      a ∈ IsLocalRing.maximalIdeal (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val)))
    (hi : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → ∀ hxD : IntersectionGeometry.supportPoint Z.val ∈ (D.val : Set V.carrier),
      PrimeSpectrum.zeroLocus
        (Ideal.ofList (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B (IntersectionGeometry.supportPoint Z.val) hxB (n + 1) s) : Set (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))) ∩
        Module.support (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))
          (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val (IntersectionGeometry.supportPoint Z.val) hxD) ⊆
            {IsLocalRing.closedPoint (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint Z.val))})
    (l : ℕ) (hl : n ≤ l) :
    ∃ C : V.carrier.Opens, C ≤ B ∧ IntersectionGeometry.supportPoint Z.val ∈ C ∧
      VectorLocalFormula.Constructions.HasLocalVectorFormula V B p (n + 1) d hd s c
        (Finsupp.single Z (Local.Euler.Constructions.localCycleEuler V p (IntersectionGeometry.supportPoint Z.val)
          (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B (IntersectionGeometry.supportPoint Z.val) hxB (n + 1) s) l c)) C := by
  let x := IntersectionGeometry.supportPoint Z.val
  let c₀ := Cycle.AtPoint.Constructions.cycleAtPoint V p x c
  have hc₀ : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c₀ D ≠ 0 → x ∈ (D.val : Set V.carrier) :=
    fun D hD => (Cycle.AtPoint.Constructions.cycleAtPoint_ne_zero V p x c D hD).2
  have hi₀ := fun (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c₀ D ≠ 0) =>
    hi D (Cycle.AtPoint.Constructions.cycleAtPoint_ne_zero V p x c D hD).1
  obtain ⟨C, hCB, hxC, hformula⟩ :=
    Class.exists_local_vector_formula V d Z n p hd c₀ hc₀ B hxB s hr hm hi₀ l hl
  let N := Cycle.AtPoint.Constructions.pointNeighborhood V p x c B
  refine ⟨C ⊓ N, inf_le_left.trans hCB, ⟨hxC, Cycle.AtPoint.Constructions.mem_pointNeighborhood V p x c B hxB⟩, ?_⟩
  intro U hUN hUB L u hu hcu
  have hUC : (U : Set V.analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver C := fun _ hy => (hUN hy).1
  have hUP : (U : Set V.analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver N := fun _ hy => (hUN hy).2
  have h := hformula U hUC hUB u hu (fun D hD => hcu D (Cycle.AtPoint.Constructions.cycleAtPoint_ne_zero V p x c D hD).1)
  have hE := Local.EulerFilter.Constructions.localCycleEuler_cycleAtPoint V p x (Section.StalkMap.Constructions.VectorGerms.vectorGerms V B x hxB (n + 1) s) l c
  rw [hE] at h
  exact (Cycle.VectorFilter.Constructions.cycleVectorClassAt_cycleAtPoint V B U hUB u p (n + 1) d hd s hu c x B hUP hcu).trans h

end AlgebraicGeometry.CycleClass.Thom.IsolatedVector.Constructions.ClassGeneral

end

end OAI
