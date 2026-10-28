import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.LocalizationFlat
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Flatness.GradedHilbert

noncomputable section

/-!
Flatness of projective spectra from flatness in high homogeneous degrees.
This checks actual scheme morphisms through their standard affine cover.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

def projectiveStructureMap : Proj 𝒜 ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))

theorem projectiveStructureMap_away {s : A} (hs : s ∈ 𝒜 1) :
    Proj.awayι 𝒜 s hs Nat.zero_lt_one ≫ projectiveStructureMap 𝒜 =
      Spec.map (CommRingCat.ofHom (algebraMap R (HomogeneousLocalization.Away 𝒜 s))) := by
  rw [projectiveStructureMap, ← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp, Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap]
  rfl

theorem projectiveStructureMap_flat {ι : Type*} (s : ι → A)
    (hs : ∀ i, s i ∈ 𝒜 1)
    (hcover : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range s))
    (N : ℕ) (hflat : ∀ d ≥ N, Module.Flat R (𝒜 d)) : Flat (projectiveStructureMap 𝒜) := by
  have : IsZariskiLocalAtSource @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{u}) (Q := RingHom.Flat)
  let U := Proj.affineOpenCoverOfIrrelevantLESpan 𝒜 s hs (fun _ => Nat.zero_lt_one) hcover
  apply (IsZariskiLocalAtSource.iff_of_openCover U.openCover).mpr
  intro i
  change Flat (Proj.awayι 𝒜 (s i) (hs i) Nat.zero_lt_one ≫ projectiveStructureMap 𝒜)
  rw [projectiveStructureMap_away, Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr (Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_flat_of_eventually_flat (hs i) N hflat)

variable {n : ℕ}

theorem quotient_irrelevant_le_span_variables (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    (HomogeneousIdeal.irrelevant (Graded.Quotient.GradedHilbert.quotientGrading I)).toIdeal ≤
      Ideal.span (Set.range (fun i : Fin (n + 1) => Graded.Quotient.GradedHilbert.gradedQuotientMap I (MvPolynomial.X i))) := by
  have h := Graded.Quotient.GradedHilbert.irrelevant_quotient_le_map I
  change (HomogeneousIdeal.irrelevant (Graded.Quotient.GradedHilbert.quotientGrading I)).toIdeal ≤
    Ideal.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (HomogeneousIdeal.irrelevant (Hilbert.Polynomial.GradedHilbert.grading R n)).toIdeal at h
  apply h.trans
  have hr : (Set.range fun i : Fin (n + 1) => Graded.Quotient.GradedHilbert.gradedQuotientMap I (MvPolynomial.X i)) =
      Graded.Quotient.GradedHilbert.gradedQuotientMap I '' Set.range MvPolynomial.X := Set.range_comp' _ _
  rw [hr]
  erw [← Ideal.map_span]
  apply Ideal.map_mono
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (Hilbert.Polynomial.GradedHilbert.grading R n)).mpr
  intro d hd f hf
  change f ∈ Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n))
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro a ha
  have had : a.degree = d := (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support f d).mp hf a ha
  have hex : ∃ i, a i ≠ 0 := by
    by_contra! hzero
    have haz : a = 0 := Finsupp.ext hzero
    rw [haz] at had
    simp only [map_zero] at had
    omega
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, Set.mem_univ i, hi⟩

/-- The projective quotient is flat as an actual scheme over the base
whenever its high homogeneous degree quotients are flat modules. -/
theorem projectiveQuotient_flat_of_eventually_flat
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (N : ℕ)
    (hflat : ∀ d ≥ N, Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)) :
    Flat (projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := by
  apply projectiveStructureMap_flat (Graded.Quotient.GradedHilbert.quotientGrading I)
    (fun i : Fin (n + 1) => Graded.Quotient.GradedHilbert.gradedQuotientMap I (MvPolynomial.X i))
    (fun i => (Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (MvPolynomial.isHomogeneous_X R i))
    (quotient_irrelevant_le_span_variables I) N
  intro d hd
  exact (Module.Flat.equiv_iff (Graded.Quotient.GradedHilbert.degreeQuotientEquivQuotientGrading I d)).mp (hflat d hd)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Flatness.GradedHilbert
