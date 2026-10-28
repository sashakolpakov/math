import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Quotient
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Quotient -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Quotient.GradedHilbert

noncomputable section

/-!
The projective spectrum of a homogeneous quotient is a closed subscheme
of projective space. On every projective basic open, its inclusion comes
from a surjective map of homogeneous localizations.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

def projectiveQuotient (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) : Scheme :=
  Proj (Graded.Quotient.GradedHilbert.quotientGrading I)

def projectiveQuotientInclusion (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    projectiveQuotient I ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  Proj.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (Graded.Quotient.GradedHilbert.irrelevant_quotient_le_map I)

theorem quotient_away_map_surjective (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    {d : ℕ} (s : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hs : s ∈ Hilbert.Polynomial.GradedHilbert.grading R n d) :
    Function.Surjective (HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) s) := by
  intro z
  obtain ⟨m, q, hq, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (Graded.Quotient.GradedHilbert.quotientGrading I)
    ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem hs) z
  obtain ⟨f, hf, rfl⟩ := hq
  refine ⟨HomogeneousLocalization.Away.mk (Hilbert.Polynomial.GradedHilbert.grading R n) hs m f hf, ?_⟩
  rw [HomogeneousLocalization.Away.map_mk]
  rfl

theorem projectiveQuotientInclusion_restrict_closed (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    {d : ℕ} (hd : 0 < d) (s : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hs : s ∈ Hilbert.Polynomial.GradedHilbert.grading R n d) :
    IsClosedImmersion (projectiveQuotientInclusion I ∣_ Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) s) := by
  let f := Graded.Quotient.GradedHilbert.gradedQuotientMap I
  let src := Proj.basicOpenIsoSpec (Graded.Quotient.GradedHilbert.quotientGrading I) (f s) (f.map_mem hs) hd
  let tgt := Proj.basicOpenIsoSpec (Hilbert.Polynomial.GradedHilbert.grading R n) s hs hd
  let a := Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f s))
  have ha : IsClosedImmersion a := IsClosedImmersion.spec_of_surjective _
    (quotient_away_map_surjective I s hs)
  have hdiag : src.inv ≫ (projectiveQuotientInclusion I ∣_ Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) s) =
      a ≫ tgt.inv := by
    apply (cancel_mono (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) s).ι).mp
    erw [Category.assoc, morphismRestrict_ι]
    exact Proj.awayι_comp_map f (Graded.Quotient.GradedHilbert.irrelevant_quotient_le_map I) hd s hs
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    src.inv (projectiveQuotientInclusion I ∣_ Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) s)).mp
  rw [hdiag]
  exact IsClosedImmersion.comp a tgt.inv

instance projectiveQuotientInclusion_isClosedImmersion (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    IsClosedImmersion (projectiveQuotientInclusion I) := by
  let A := Hilbert.Polynomial.GradedHilbert.grading R n
  let Index := Σ d : PNat, A d
  let U (s : Index) := Proj.basicOpen A s.2.val
  have hcover : iSup U = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top
    apply (HomogeneousIdeal.toIdeal_irrelevant_le A).mpr
    intro d hd f hf
    exact Ideal.subset_span ⟨(⟨⟨d, hd⟩, ⟨f, hf⟩⟩ : Index), rfl⟩
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) U hcover).mpr
  intro s
  exact projectiveQuotientInclusion_restrict_closed I s.1.property s.2.val s.2.property

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Quotient.GradedHilbert
