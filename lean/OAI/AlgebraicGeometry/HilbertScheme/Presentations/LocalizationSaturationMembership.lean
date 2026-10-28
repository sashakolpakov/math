import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationPolynomialMembership
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.PrimeDescent

/-! # Localization Saturation Membership -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationSaturationMembership.GradedHilbert

noncomputable section

/-! Finite homogeneous saturation memberships spread from an arbitrary
coefficient localization to one of its principal neighborhoods. -/

open _root_.MvPolynomial

universe u v
variable {A : Type u} [CommRing A] {n : ℕ}

theorem finite_saturation_membership_localization_descent
    (U : Submonoid A) (T : Type u) [CommRing T] [Algebra A T] [IsLocalization U T]
    {κ : Type v} [Fintype κ]
    (I : κ → HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n)) (g : κ → Hilbert.Polynomial.GradedHilbert.CoordinateRing A n)
    (d : κ → ℕ) (hg : ∀ i, (g i).IsHomogeneous (d i))
    (hmem : ∀ i, MvPolynomial.map (algebraMap A T) (g i) ∈
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := T) (I i))).toIdeal) :
    ∃ s : U, ∀ i, MvPolynomial.map (algebraMap A (Localization.Away s.val)) (g i) ∈
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.Away s.val) (I i))).toIdeal := by
  classical
  have hpowers (q : κ × Fin (n + 1)) : ∃ k : ℕ,
      X q.2 ^ k * MvPolynomial.map (algebraMap A T) (g q.1) ∈
        (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := T) (I q.1)).toIdeal :=
    (Projective.Saturation.GradedHilbert.mem_projectiveSaturation_iff _ ((hg q.1).map _)).mp (hmem q.1) q.2
  choose k hk using hpowers
  have hm (q : κ × Fin (n + 1)) :
      MvPolynomial.map (algebraMap A T) (X q.2 ^ k q * g q.1) ∈
        (I q.1).toIdeal.map (MvPolynomial.map (algebraMap A T)) := by
    simpa only [map_mul, map_pow, MvPolynomial.map_X] using! hk q
  obtain ⟨s, hsm⟩ := LocalizationPolynomialMembership.finite_polynomialIdeal_membership_localization_descent U T
    (fun q : κ × Fin (n + 1) => (I q.1).toIdeal) (fun q => X q.2 ^ k q * g q.1) hm
  refine ⟨s, fun i => ?_⟩
  apply (Projective.Saturation.GradedHilbert.mem_projectiveSaturation_iff _ ((hg i).map _)).mpr
  intro j
  refine ⟨k (i, j), ?_⟩
  simpa only [map_mul, map_pow, MvPolynomial.map_X] using! hsm (i, j)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationSaturationMembership.GradedHilbert
