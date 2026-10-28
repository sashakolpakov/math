import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Quotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Localization
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Ideal Recovery -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealRecovery.GradedHilbert

noncomputable section

/-!
Recovering a saturated homogeneous ideal from its projective closed
subscheme. Homogeneous fractions on the standard affine charts detect
variable-power membership in the original ideal.
-/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

def coordinateFraction (i : Fin (n + 1)) (d : ℕ) (f : Hilbert.Polynomial.GradedHilbert.grading R n d) :
    HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading R n) (X i) :=
  HomogeneousLocalization.Away.mk (Hilbert.Polynomial.GradedHilbert.grading R n) (isHomogeneous_X R i) d f.val
    (by simpa only [smul_eq_mul, mul_one] using f.property)

theorem quotient_coordinateFraction_eq_zero_iff (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) (d : ℕ) (f : Hilbert.Polynomial.GradedHilbert.grading R n d) :
    HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i) (coordinateFraction i d f) = 0 ↔
      ∃ k : ℕ, X i ^ k * f.val ∈ I.toIdeal := by
  erw [coordinateFraction, HomogeneousLocalization.Away.map_mk,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_zero,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := s.property
    refine ⟨k, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    change Ideal.Quotient.mk I.toIdeal (X i ^ k * f.val) = 0
    rw [map_mul, map_pow]
    rw [← hk] at hs
    exact hs
  · rintro ⟨k, hk⟩
    refine ⟨⟨(Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) ^ k, ⟨k, rfl⟩⟩, ?_⟩
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hk
    rw [map_mul, map_pow] at hz
    exact hz

theorem saturated_eq_of_projective_chart_kernels
    (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (hJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal)
    (hker : ∀ i : Fin (n + 1),
      RingHom.ker (HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i)) =
        RingHom.ker (HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap J) (X i))) : I = J := by
  apply Saturation.Localization.GradedHilbert.saturated_eq_of_variable_power_membership I J hI hJ
  · intro f d hf hfI i
    have hz : coordinateFraction i d (⟨f, hf⟩ : Hilbert.Polynomial.GradedHilbert.grading R n d) ∈
        RingHom.ker (HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (X i)) := by
      apply (quotient_coordinateFraction_eq_zero_iff I i d ⟨f, hf⟩).mpr
      exact ⟨0, by simpa only [pow_zero, one_mul] using hfI⟩
    rw [hker i] at hz
    exact (quotient_coordinateFraction_eq_zero_iff J i d ⟨f, hf⟩).mp hz
  · intro f d hf hfJ i
    have hz : coordinateFraction i d (⟨f, hf⟩ : Hilbert.Polynomial.GradedHilbert.grading R n d) ∈
        RingHom.ker (HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap J) (X i)) := by
      apply (quotient_coordinateFraction_eq_zero_iff J i d ⟨f, hf⟩).mpr
      exact ⟨0, by simpa only [pow_zero, one_mul] using hfJ⟩
    rw [← hker i] at hz
    exact (quotient_coordinateFraction_eq_zero_iff I i d ⟨f, hf⟩).mp hz

theorem projective_chart_kernel_eq (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    {d : ℕ} (hd : 0 < d) (s : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hs : s ∈ Hilbert.Polynomial.GradedHilbert.grading R n d) :
    RingHom.ker (HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) s) =
      ((Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).ker.ideal
        ⟨Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) s, Proj.isAffineOpen_basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) s hs hd⟩).comap
          (Proj.awayToSection (Hilbert.Polynomial.GradedHilbert.grading R n) s).hom := by
  let q := Graded.Quotient.GradedHilbert.gradedQuotientMap I
  let e := Proj.basicOpenIsoAway (Graded.Quotient.GradedHilbert.quotientGrading I) (q s) (q.map_mem hs) hd
  have hdiag := Proj.awayToSection_comp_appLE q (Graded.Quotient.GradedHilbert.irrelevant_quotient_le_map I) hs
  apply Ideal.ext
  intro z
  rw [Ideal.mem_comap, Scheme.Hom.ker_apply]
  change HomogeneousLocalization.Away.map q s z = 0 ↔
    ((Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).app (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) s)).hom
      ((Proj.awayToSection (Hilbert.Polynomial.GradedHilbert.grading R n) s).hom z) = 0
  have h := congrArg (fun h => h.hom z) hdiag
  change ((Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).app (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) s)).hom
      ((Proj.awayToSection (Hilbert.Polynomial.GradedHilbert.grading R n) s).hom z) =
    (Proj.awayToSection (Graded.Quotient.GradedHilbert.quotientGrading I) (q s)).hom
      (HomogeneousLocalization.Away.map q s z) at h
  rw [h]
  exact ((e.commRingCatIsoToRingEquiv).map_eq_zero_iff).symm

/-- Equal projective ideal sheaves have equal saturated homogeneous
coordinate ideals. -/
theorem saturated_eq_of_projective_idealSheaf
    (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (hJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal)
    (hker : (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).ker = (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J).ker) : I = J := by
  apply saturated_eq_of_projective_chart_kernels I J hI hJ
  intro i
  rw [projective_chart_kernel_eq I Nat.zero_lt_one (X i) (isHomogeneous_X R i),
    projective_chart_kernel_eq J Nat.zero_lt_one (X i) (isHomogeneous_X R i), hker]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealRecovery.GradedHilbert
