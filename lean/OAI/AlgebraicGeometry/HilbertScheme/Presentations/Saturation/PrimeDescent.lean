import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.IdealPrimeDescent
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SaturationOrder

/-! # Prime Descent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.PrimeDescent.GradedHilbert

noncomputable section

/-! Finitely many homogeneous saturation memberships spread from a
prime localization to a principal neighborhood, without Noetherianity. -/

open _root_.MvPolynomial

universe u v
variable {A : Type u} [CommRing A] {n : ℕ}

theorem finite_saturation_membership_prime_descent
    (p : Ideal A) [p.IsPrime] {κ : Type v} [Fintype κ]
    (I : κ → HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n)) (g : κ → Hilbert.Polynomial.GradedHilbert.CoordinateRing A n)
    (d : κ → ℕ) (hg : ∀ i, (g i).IsHomogeneous (d i))
    (hmem : ∀ i, MvPolynomial.map (algebraMap A (Localization.AtPrime p)) (g i) ∈
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.AtPrime p) (I i))).toIdeal) :
    ∃ s : A, s ∉ p ∧ ∀ i, MvPolynomial.map (algebraMap A (Localization.Away s)) (g i) ∈
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.Away s) (I i))).toIdeal := by
  classical
  have hpowers (q : κ × Fin (n + 1)) : ∃ k : ℕ,
      X q.2 ^ k * MvPolynomial.map (algebraMap A (Localization.AtPrime p)) (g q.1) ∈
        (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.AtPrime p) (I q.1)).toIdeal :=
    (Projective.Saturation.GradedHilbert.mem_projectiveSaturation_iff _ ((hg q.1).map _)).mp (hmem q.1) q.2
  choose k hk using hpowers
  have hm (q : κ × Fin (n + 1)) :
      MvPolynomial.map (algebraMap A (Localization.AtPrime p)) (X q.2 ^ k q * g q.1) ∈
        (I q.1).toIdeal.map (MvPolynomial.map (algebraMap A (Localization.AtPrime p))) := by
    simpa only [map_mul, map_pow, MvPolynomial.map_X] using! hk q
  obtain ⟨s, hs, hsm⟩ := Polynomial.IdealPrimeDescent.finite_polynomialIdeal_membership_descent p
    (fun q : κ × Fin (n + 1) => (I q.1).toIdeal) (fun q => X q.2 ^ k q * g q.1) hm
  refine ⟨s, hs, fun i => ?_⟩
  apply (Projective.Saturation.GradedHilbert.mem_projectiveSaturation_iff _ ((hg i).map _)).mpr
  intro j
  refine ⟨k (i, j), ?_⟩
  simpa only [map_mul, map_pow, MvPolynomial.map_X] using! hsm (i, j)

theorem generatedIdeal_le_saturation_of_mapped_generators
    (T : Type v) [CommRing T] [Algebra A T]
    {κ : Type*} (g : κ → Hilbert.Polynomial.GradedHilbert.CoordinateRing A n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n))
    (hmem : ∀ i, MvPolynomial.map (algebraMap A T) (g i) ∈
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := T) I)).toIdeal) :
    Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := T) (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)) ≤
      Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := T) I) := by
  apply (Projective.SaturationOrder.GradedHilbert.projectiveSaturation_le_iff _ _ (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated _)).mpr
  change (Ideal.span (Set.range g)).map (MvPolynomial.map (algebraMap A T)) ≤ _
  rw [Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact hmem i

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.PrimeDescent.GradedHilbert
