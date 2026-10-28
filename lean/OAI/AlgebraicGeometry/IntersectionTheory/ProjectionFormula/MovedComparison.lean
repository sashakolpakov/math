import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoveredPrincipalDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

/-! # Moved Comparison -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedComparison

noncomputable section

section

/-! Every native rational-equivalence relation has finite positioning
strata. All cycles meeting those strata properly have rationally zero
intersection with the relation, in every codimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace RelationDescentStrata

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem restrict (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (S T : Finset (IrreducibleCloseds X.carrier)) (hST : S ⊆ T) (a : X.RationalDimensionCycle p)
    (ha : a ∈ Proper.SupportCycles.submodule X p (fun B : T => B.val)) :
    a ∈ Proper.SupportCycles.submodule X p (fun B : S => B.val) :=
  fun B => ha ⟨B.val, hST B.property⟩

theorem principal (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0) :
    ∃ S : Finset (IrreducibleCloseds X.carrier), ∀ (p : ℕ) (a : X.RationalDimensionCycle p),
      a ∈ Proper.SupportCycles.submodule X p (fun B : S => B.val) →
      CycleClass.Thom.IntersectionGeometry.MeetProperly X p (k + 1) a (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) ∧
      Supports.ProperCycle.intersectionBilinear X m p (k + 1) a (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) ∈
        CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + (k + 1)) :=
  CoveredPrincipalDescent.exists_strata X m k W g hg

theorem exists_data (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (b : X.RationalDimensionCycle q) (hb : b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X q) :
    ∃ S : Finset (IrreducibleCloseds X.carrier), ∀ (p : ℕ) (a : X.RationalDimensionCycle p),
      a ∈ Proper.SupportCycles.submodule X p (fun B : S => B.val) →
      CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b ∧ Supports.ProperCycle.intersectionBilinear X m p q a b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + q) := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨W, hW, g, hg, rfl⟩ := (Principal.ClosedSectionCycle.isPrincipalDivisor_iff X q b).mp hb
    subst q
    exact principal X m (X.supportCodimension W) ⟨W, rfl⟩ g hg
  | zero =>
    refine ⟨∅, ?_⟩
    intro p a _
    refine ⟨?_, ?_⟩
    · intro A hA B hB
      simp at hB
    · rw [map_zero]
      exact Submodule.zero_mem _
  | add b c _ _ ihb ihc =>
    obtain ⟨S, hS⟩ := ihb
    obtain ⟨T, hT⟩ := ihc
    refine ⟨S ∪ T, ?_⟩
    intro p a ha
    have hb := hS p a (restrict X p S (S ∪ T) Finset.subset_union_left a ha)
    have hc := hT p a (restrict X p T (S ∪ T) Finset.subset_union_right a ha)
    refine ⟨ProperCycleLinearity.add_right X p q a b c hb.1 hc.1, ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ hb.2 hc.2
  | smul r b _ ih =>
    obtain ⟨S, hS⟩ := ih
    refine ⟨S, ?_⟩
    intro p a ha
    have hb := hS p a ha
    refine ⟨ProperCycleLinearity.smul_right X p q a b r hb.1, ?_⟩
    rw [map_smul]
    exact Submodule.smul_mem _ _ hb.2

end RelationDescentStrata

end

/-! Rationally equivalent second inputs have equal Chow intersection
classes against a common, explicitly constructed moved first input. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem exists_moved (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle p) (b b' : X.RationalDimensionCycle q)
    (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X q b b')
    {ι : Type} [Finite ι] (Z₀ : ι → IrreducibleCloseds X.carrier) :
    ∃ a' : X.RationalDimensionCycle p,
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a' ∧ a' ∈ Proper.SupportCycles.submodule X p Z₀ ∧
      CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a' b ∧ CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a' b' ∧
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (p + q) (Supports.ProperCycle.intersectionBilinear X m p q a' b) (Supports.ProperCycle.intersectionBilinear X m p q a' b') := by
  classical
  obtain ⟨S, hS⟩ := RelationDescentStrata.exists_data X m q (b - b') hb
  let J := ι ⊕ (S ⊕ (b.support ⊕ b'.support))
  let family : J → IrreducibleCloseds X.carrier :=
    Sum.elim Z₀ (Sum.elim Subtype.val (Sum.elim (fun B => B.val.val) (fun B => B.val.val)))
  obtain ⟨a', ha', hp⟩ := General.ChowMoving.cycle X m family p a
  refine ⟨a', ha', ?_, ?_, ?_, ?_⟩
  · intro i A hA
    exact hp (.inl i) A hA
  · intro A hA B hB C hC
    have h := hp (.inr (.inr (.inl ⟨B, hB⟩))) A hA C hC
    change p + X.supportCodimension B.val ≤ X.supportCodimension C at h
    rwa [B.property] at h
  · intro A hA B hB C hC
    have h := hp (.inr (.inr (.inr ⟨B, hB⟩))) A hA C hC
    change p + X.supportCodimension B.val ≤ X.supportCodimension C at h
    rwa [B.property] at h
  · have hpos : a' ∈ Proper.SupportCycles.submodule X p (fun B : S => B.val) := by
      intro B A hA
      exact hp (.inr (.inl B)) A hA
    have hz := (hS p a' hpos).2
    rw [map_sub] at hz
    exact hz

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedComparison
