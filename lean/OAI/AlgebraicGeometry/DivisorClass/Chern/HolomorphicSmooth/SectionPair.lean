import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.HermitianPair

/-! # Section Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.SectionPair

noncomputable section

/-! The actual Hermitian metric induces a frame-independent pointwise pairing on smooth line-bundle sections. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [FiniteDimensional ℝ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [CompactSpace M] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) {U : Opens M}

def holomorphicLineSmoothSectionPair (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) (x : U) : ℂ :=
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x.val
  HolomorphicLine.HermitianPair.holomorphicLineHermitianPair u x.val ⟨x.val, hx⟩
    (s.val x.val ⟨x.val, x.property, hx⟩ 0) (t.val x.val ⟨x.val, x.property, hx⟩ 0)

theorem holomorphicLineSmoothSectionPair_inFrame (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0)
    (i : M) (x : U) (hi : x.val ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    holomorphicLineSmoothSectionPair u s t x =
      HolomorphicLine.HermitianPair.holomorphicLineHermitianPair u i ⟨x.val, hi⟩
        (s.val i ⟨x.val, x.property, hi⟩ 0) (t.val i ⟨x.val, x.property, hi⟩ 0) := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x.val
  have hs := congrArg (fun a : TangentSpace 𝓘(ℝ, E) x.val [⋀^Fin 0]→L[ℝ] ℂ => a 0)
    (s.property i x.val x.val x.property hi hx)
  have ht := congrArg (fun a : TangentSpace 𝓘(ℝ, E) x.val [⋀^Fin 0]→L[ℝ] ℂ => a 0)
    (t.property i x.val x.val x.property hi hx)
  change s.val x.val ⟨x.val, x.property, hx⟩ 0 =
    (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i x.val).val ⟨x.val, hi, hx⟩ *
      s.val i ⟨x.val, x.property, hi⟩ 0 at hs
  change t.val x.val ⟨x.val, x.property, hx⟩ 0 =
    (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i x.val).val ⟨x.val, hi, hx⟩ *
      t.val i ⟨x.val, x.property, hi⟩ 0 at ht
  have h := HolomorphicLine.HermitianPair.holomorphicLineHermitianPair_transition u i x.val x.val hi hx
    (s.val i ⟨x.val, x.property, hi⟩ 0) (t.val i ⟨x.val, x.property, hi⟩ 0)
  rw [HolomorphicLine.Bundle.holomorphicCohomologyCoordChange_apply E M u i x.val x.val hi hx,
    HolomorphicLine.Bundle.holomorphicCohomologyCoordChange_apply E M u i x.val x.val hi hx, ← hs, ← ht] at h
  exact h

theorem holomorphicLineSmoothSectionPair_conj (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) (x : U) :
    conj (holomorphicLineSmoothSectionPair u s t x) = holomorphicLineSmoothSectionPair u t s x := by
  unfold holomorphicLineSmoothSectionPair HolomorphicLine.HermitianPair.holomorphicLineHermitianPair
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem holomorphicLineSmoothSectionPair_add_right (s t r : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) (x : U) :
    holomorphicLineSmoothSectionPair u s (t + r) x =
      holomorphicLineSmoothSectionPair u s t x + holomorphicLineSmoothSectionPair u s r x := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x.val
  let A : ℂ := (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u x.val ⟨x.val, hx⟩ : ℂ) *
    conj (s.val x.val ⟨x.val, x.property, hx⟩ 0)
  let b : ℂ := t.val x.val ⟨x.val, x.property, hx⟩ 0
  let c : ℂ := r.val x.val ⟨x.val, x.property, hx⟩ 0
  change A * (b + c) = A * b + A * c
  ring

theorem holomorphicLineSmoothSectionPair_smul_right (s t : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0)
    (z : ℂ) (x : U) :
    holomorphicLineSmoothSectionPair u s (z • t) x = z * holomorphicLineSmoothSectionPair u s t x := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x.val
  let A : ℂ := (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u x.val ⟨x.val, hx⟩ : ℂ) *
    conj (s.val x.val ⟨x.val, x.property, hx⟩ 0)
  let b : ℂ := t.val x.val ⟨x.val, x.property, hx⟩ 0
  change A * (z * b) = z * (A * b)
  ring

theorem holomorphicLineSmoothSectionPair_self_inFrame (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0)
    (i : M) (x : U) (hi : x.val ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    holomorphicLineSmoothSectionPair u s s x =
      (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight u i ⟨x.val, hi⟩ *
        Complex.normSq (s.val i ⟨x.val, x.property, hi⟩ 0) : ℝ) := by
  rw [holomorphicLineSmoothSectionPair_inFrame u s s i x hi, HolomorphicLine.HermitianPair.holomorphicLineHermitianPair_self]

theorem holomorphicLineSmoothSectionPair_nonneg (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) (x : U) :
    0 ≤ (holomorphicLineSmoothSectionPair u s s x).re := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x.val
  rw [holomorphicLineSmoothSectionPair_self_inFrame u s x.val x hx, Complex.ofReal_re]
  exact mul_nonneg (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight_pos u x.val ⟨x.val, hx⟩).le (Complex.normSq_nonneg _)

theorem holomorphicLineSmoothSectionPair_definite (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0)
    (hs : ∀ x : U, (holomorphicLineSmoothSectionPair u s s x).re = 0) : s = 0 := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro i x
  have h := hs ⟨x.val, x.property.1⟩
  rw [holomorphicLineSmoothSectionPair_self_inFrame u s i ⟨x.val, x.property.1⟩ x.property.2,
    Complex.ofReal_re] at h
  have hz : s.val i x 0 = 0 := by
    by_contra hn
    have hp := mul_pos (HolomorphicLine.MetricWeight.holomorphicLineMetricWeight_pos u i ⟨x.val, x.property.2⟩)
      (Complex.normSq_pos.mpr hn)
    rw [h] at hp
    exact (lt_irrefl 0) hp
  ext v
  change s.val i x v = 0
  have hv : v = 0 := Subsingleton.elim _ _
  rwa [hv]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.SectionPair
