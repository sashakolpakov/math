import OAI.AlgebraicGeometry.HilbertScheme.Presentations.InitialIdeal

/-! # Groebner Generators -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroebnerGenerators.GradedHilbert

noncomputable section

/-!
Lifting generators of an initial ideal to homogeneous generators of the
original ideal. The leading-term cover is proved to generate the ideal
using division and the vanishing of a standard remainder in the ideal.
-/

open _root_.MvPolynomial
open scoped MonomialOrder

universe u

variable {K : Type u} [Field K] {n : ℕ}

theorem leadingDegree_homogeneousComponent (m : MonomialOrder (Fin (n + 1)))
    {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} (hf : f ≠ 0) :
    let d := (m.degree f).degree
    homogeneousComponent d f ≠ 0 ∧ m.degree (homogeneousComponent d f) = m.degree f := by
  classical
  dsimp only
  have hs : m.degree f ∈ (homogeneousComponent (m.degree f).degree f).support := by
    rw [support_homogeneousComponent]
    exact Finset.mem_filter.mpr ⟨m.degree_mem_support hf, rfl⟩
  refine ⟨?_, m.toSyn.injective ?_⟩
  · intro hzero
    simp only [hzero, support_zero, Finset.notMem_empty] at hs
  · apply le_antisymm
    · apply m.degree_le_iff.mpr
      intro a ha
      rw [support_homogeneousComponent] at ha
      exact m.le_degree (Finset.mem_filter.mp ha).1
    · exact m.le_degree hs

theorem lift_initial_monomial (m : MonomialOrder (Fin (n + 1)))
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (a : Fin (n + 1) →₀ ℕ)
    (ha : monomial a (1 : K) ∈ InitialIdeal.GradedHilbert.initialIdeal m I.toIdeal) :
    ∃ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n, f ∈ I.toIdeal ∧ f ≠ 0 ∧
      f.IsHomogeneous (m.degree f).degree ∧ m.degree f ≤ a := by
  obtain ⟨f, hf, hf0, hfa⟩ := (InitialIdeal.GradedHilbert.monomial_mem_initialIdeal_iff m I.toIdeal a).mp ha
  obtain ⟨hc0, hdeg⟩ := leadingDegree_homogeneousComponent m hf0
  refine ⟨homogeneousComponent (m.degree f).degree f,
    homogeneousComponent_mem_of_mem I.isHomogeneous hf _, hc0, ?_, ?_⟩
  · rw [hdeg]
    exact homogeneousComponent_isHomogeneous _ _
  · rw [hdeg]
    exact hfa

theorem ideal_eq_span_of_leading_cover (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))
    (hB : ∀ b ∈ B, b ∈ I ∧ b ≠ 0)
    (hcover : ∀ f ∈ I, f ≠ 0 → ∃ b ∈ B, m.degree b ≤ m.degree f) :
    I = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) := by
  classical
  have hspan : Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) ≤ I :=
    Ideal.span_le.mpr fun b hb => (hB b hb).1
  apply le_antisymm _ hspan
  intro f hf
  obtain ⟨g, r, hfr, _, hr⟩ := m.div_set (B := (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))
    (fun b hb => m.isUnit_leadingCoeff.mpr (hB b hb).2) f
  have hg : Finsupp.linearCombination (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)
      (fun b : (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) => b.val) g ∈
      Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ (g b) (Ideal.subset_span b.property)
  have hrI : r ∈ I := by
    have h := I.sub_mem hf (hspan hg)
    rwa [hfr, add_sub_cancel_left] at h
  have hr0 : r = 0 := by
    by_contra hr0
    obtain ⟨b, hb, hbr⟩ := hcover r hrI hr0
    exact hr (m.degree r) (m.degree_mem_support hr0) b hb hbr
  rw [hfr, hr0, add_zero]
  exact hg

/-- A bound on the degrees of monomial generators of the initial ideal
lifts to a bound on homogeneous generators of the original ideal. -/
theorem homogeneous_generators_of_initial_generators
    (m : MonomialOrder (Fin (n + 1))) (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
    (G : Finset (Fin (n + 1) →₀ ℕ)) (N : ℕ)
    (hG : InitialIdeal.GradedHilbert.initialIdeal m I.toIdeal =
      Ideal.span ((fun a => monomial a (1 : K)) '' (G : Set (Fin (n + 1) →₀ ℕ))))
    (hN : ∀ a ∈ G, a.degree ≤ N) :
    ∃ B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n), I.toIdeal = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) ∧
      ∀ b ∈ B, b ≠ 0 ∧ ∃ d ≤ N, b.IsHomogeneous d := by
  classical
  have hlift (a : G) : ∃ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n, f ∈ I.toIdeal ∧ f ≠ 0 ∧
      f.IsHomogeneous (m.degree f).degree ∧ m.degree f ≤ a.val := by
    apply lift_initial_monomial m I a.val
    rw [hG]
    exact Ideal.subset_span ⟨a.val, a.property, rfl⟩
  choose f hf using hlift
  let B := Finset.univ.image f
  have hB (b : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hb : b ∈ B) : b ∈ I.toIdeal ∧ b ≠ 0 := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨(hf a).1, (hf a).2.1⟩
  refine ⟨B, ideal_eq_span_of_leading_cover m I.toIdeal B hB ?_, ?_⟩
  · intro p hp hp0
    have hlead := InitialIdeal.GradedHilbert.leading_monomial_mem_initialIdeal m hp hp0
    rw [hG, mem_ideal_span_monomial_image] at hlead
    have hmem : m.degree p ∈ (monomial (m.degree p) (1 : K)).support := by simp
    obtain ⟨a, ha, hpa⟩ := hlead (m.degree p) hmem
    exact ⟨f ⟨a, ha⟩, Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩,
      (hf ⟨a, ha⟩).2.2.2.trans hpa⟩
  · intro b hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨(hf a).2.1, (m.degree (f a)).degree,
      (Finsupp.degree_mono (hf a).2.2.2).trans (hN a.val a.property), (hf a).2.2.1⟩

theorem exists_finite_homogeneous_generators (m : MonomialOrder (Fin (n + 1)))
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) :
    ∃ (N : ℕ) (B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)),
      I.toIdeal = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) ∧
      ∀ b ∈ B, b ≠ 0 ∧ ∃ d ≤ N, b.IsHomogeneous d := by
  classical
  obtain ⟨G, hG⟩ := (InitialIdeal.GradedHilbert.initialIdeal_isMonomial m I.toIdeal).finite_generators
  obtain ⟨B, hB⟩ := homogeneous_generators_of_initial_generators m I G (G.sup Finsupp.degree)
    hG (fun a ha => Finset.le_sup (f := Finsupp.degree) ha)
  exact ⟨G.sup Finsupp.degree, B, hB⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroebnerGenerators.GradedHilbert
