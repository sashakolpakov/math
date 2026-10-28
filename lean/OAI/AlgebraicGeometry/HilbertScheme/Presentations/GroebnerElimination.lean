import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EliminationOrder
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedGroebnerCompletion

/-! # Groebner Elimination -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroebnerElimination.GradedHilbert

noncomputable section

/-! The elimination theorem with a uniform positive-weight degree bound. -/

open _root_.MvPolynomial

universe u v

variable {K : Type u} [Field K] {n : ℕ}

theorem elimination_mem_span_of_leading_cover
    (s : Finset (Fin (n + 1))) (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))
    {ι : Type v} (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)
    (hb : ∀ i, b i ∈ I ∧ b i ≠ 0)
    (hcover : ∀ f ∈ I, f ≠ 0 →
      ∃ i, (EliminationOrder.GradedHilbert.eliminationOrder s).degree (b i) ≤ (EliminationOrder.GradedHilbert.eliminationOrder s).degree f)
    (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : f ∈ I)
    (hfs : f ∈ supported K ((s : Set (Fin (n + 1)))ᶜ)) :
    f ∈ Ideal.span {g | ∃ i, b i = g ∧
      EliminationOrder.GradedHilbert.eliminatedWeight s ((EliminationOrder.GradedHilbert.eliminationOrder s).degree (b i)) = 0} := by
  classical
  let m := EliminationOrder.GradedHilbert.eliminationOrder s
  let J : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) := Ideal.span {g | ∃ i, b i = g ∧
    EliminationOrder.GradedHilbert.eliminatedWeight s (m.degree (b i)) = 0}
  let T := {i // EliminationOrder.GradedHilbert.eliminatedWeight s (m.degree (b i)) = 0}
  let c : T → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n := fun i => b i.val
  have hJI : J ≤ I := Ideal.span_le.mpr (by rintro g ⟨i, rfl, _⟩; exact (hb i).1)
  obtain ⟨q, r, hfr, hq, hr⟩ := m.div (b := c)
    (fun i => m.isUnit_leadingCoeff.mpr (hb i.val).2) f
  let g := Finsupp.linearCombination (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) c q
  have hgJ : g ∈ J := by
    dsimp only [g]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ (q i)
      (Ideal.subset_span ⟨i.val, rfl, i.property⟩)
  have hgs : g ∈ supported K ((s : Set (Fin (n + 1)))ᶜ) := by
    dsimp only [g]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Subalgebra.sum_mem
    intro i _
    apply EliminationOrder.GradedHilbert.supported_complement_of_degree_le s _ hfs
    simpa only [smul_eq_mul, mul_comm] using hq i
  have hre : r = f - g := (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hfr.symm))
  have hrI : r ∈ I := hre ▸ I.sub_mem hf (hJI hgJ)
  have hrs : r ∈ supported K ((s : Set (Fin (n + 1)))ᶜ) :=
    hre ▸ (supported K _).sub_mem hfs hgs
  have hr0 : r = 0 := by
    by_contra hr0
    obtain ⟨i, hi⟩ := hcover r hrI hr0
    have hwi : EliminationOrder.GradedHilbert.eliminatedWeight s (m.degree (b i)) = 0 := by
      apply Nat.eq_zero_of_le_zero
      have hw := WeightedOrder.GradedHilbert.exponent_weight_monotone (EliminationOrder.GradedHilbert.eliminatedWeight s) hi
      rwa [(EliminationOrder.GradedHilbert.supported_complement_iff_leadingWeight s r).mp hrs] at hw
    exact hr (m.degree r) (m.degree_mem_support hr0) (⟨i, hwi⟩ : T) hi
  rw [hfr, hr0, add_zero]
  exact hgJ

theorem exists_uniform_weighted_elimination_generators
    (w : Fin (n + 1) → ℕ) (hw : ∀ i, w i ≠ 0)
    (s : Finset (Fin (n + 1))) {ι : Type v} [Fintype ι]
    (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (e : ι → ℕ)
    (hb : ∀ i, (b i).IsWeightedHomogeneous w (e i)) (hb0 : ∀ i, b i ≠ 0)
    (D : ℕ) (hD : ∀ i, e i ≤ D) :
    ∃ B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n),
      (∀ g ∈ B, g ∈ Ideal.span (Set.range b) ∧ g ≠ 0 ∧
        g ∈ supported K ((s : Set (Fin (n + 1)))ᶜ) ∧
        ∃ d ≤ Uniform.GroebnerCompletion.GradedHilbert.homogeneousGroebnerDegreeBound n D, g.IsWeightedHomogeneous w d) ∧
      ∀ f ∈ supported K ((s : Set (Fin (n + 1)))ᶜ),
        f ∈ Ideal.span (Set.range b) ↔ f ∈ Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) := by
  classical
  let m := EliminationOrder.GradedHilbert.eliminationOrder s
  obtain ⟨k, c, hspan, hc, hcover⟩ :=
    WeightedGroebnerCompletion.GradedHilbert.exists_uniform_weighted_homogeneous_groebner_completion w hw m b e hb hb0 D hD
  let B := (Finset.univ.filter (fun j => EliminationOrder.GradedHilbert.eliminatedWeight s (m.degree (c j)) = 0)).image c
  have hB (g : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) : g ∈ B ↔
      ∃ j, c j = g ∧ EliminationOrder.GradedHilbert.eliminatedWeight s (m.degree (c j)) = 0 := by
    simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact exists_congr (fun _ => and_comm)
  have hcI (j : ι ⊕ Fin k) : c j ∈ Ideal.span (Set.range b) := by
    rw [← hspan]
    exact Ideal.subset_span (Set.mem_range_self j)
  refine ⟨B, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, rfl, hj⟩ := (hB g).mp hg
    exact ⟨hcI j, (hc j).1, (EliminationOrder.GradedHilbert.supported_complement_iff_leadingWeight s (c j)).mpr hj, (hc j).2⟩
  · intro f hfs
    constructor
    · intro hf
      have h := elimination_mem_span_of_leading_cover s (Ideal.span (Set.range b)) c
        (fun j => ⟨hcI j, (hc j).1⟩) hcover f hf hfs
      have he : {g | ∃ j, c j = g ∧ EliminationOrder.GradedHilbert.eliminatedWeight s (m.degree (c j)) = 0} =
          (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) := Set.ext (fun g => (hB g).symm)
      rwa [he] at h
    · apply Ideal.span_le.mpr
      intro g hg
      obtain ⟨j, rfl, _⟩ := (hB g).mp hg
      exact hcI j

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroebnerElimination.GradedHilbert
