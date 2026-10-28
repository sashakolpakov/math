import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.CoefficientMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartPullback

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert

noncomputable section

/-!
Projective homogeneous quotients commute with arbitrary base change.
The actual square of scheme morphisms is Cartesian: its standard affine
charts are the polynomial-quotient tensor-product squares.
-/

open _root_.MvPolynomial _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomogeneousLocalization

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

theorem projectiveCoefficientMap_chart_isPullback (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) :
    IsPullback (Spec.map (CommRingCat.ofHom (ChartCoefficientMap.GradedHilbert.chartCoefficientMap (S := S) I i)))
      (Proj.awayι (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I))
        (Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (X i))
        ((Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).map_mem (isHomogeneous_X S i))
        Nat.zero_lt_one)
      (Proj.awayι (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
        ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i)) Nat.zero_lt_one)
      (CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := S) I) := by
  apply IsOpenImmersion.isPullback
  · exact CoefficientMap.GradedHilbert.projectiveCoefficientMap_away I i
  · rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
    exact CoefficientMap.GradedHilbert.projectiveCoefficientMap_preimage I i

/-- The projective quotient over the extended coefficient ring is the
scheme-theoretic base change of the original projective quotient. -/
theorem projectiveQuotient_isPullback (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    IsPullback (CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := S) I)
      (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)))
      (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let U := Proj.affineOpenCoverOfIrrelevantLESpan (Graded.Quotient.GradedHilbert.quotientGrading I)
    (fun i : Fin (n + 1) => Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
    (fun i => (Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i))
    (fun _ => Nat.zero_lt_one) (Flatness.GradedHilbert.quotient_irrelevant_le_span_variables I)
  apply Scheme.isPullback_of_openCover _ _ _ _ U.openCover
  intro i
  change Fin (n + 1) at i
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I
  let a := Proj.awayι (Graded.Quotient.GradedHilbert.quotientGrading J) (Graded.Quotient.GradedHilbert.gradedQuotientMap J (X i))
    ((Graded.Quotient.GradedHilbert.gradedQuotientMap J).map_mem (isHomogeneous_X S i)) Nat.zero_lt_one
  let b := Proj.awayι (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
    ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i)) Nat.zero_lt_one
  let g := Spec.map (CommRingCat.ofHom (ChartCoefficientMap.GradedHilbert.chartCoefficientMap (S := S) I i))
  let p := Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)
  let p' := Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J)
  have H₁ : IsPullback g a b (CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := S) I) :=
    projectiveCoefficientMap_chart_isPullback I i
  have H₂ : IsPullback g (a ≫ p') (b ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    dsimp only [a, b, p, p']
    rw [Flatness.GradedHilbert.projectiveStructureMap_away, Flatness.GradedHilbert.projectiveStructureMap_away]
    exact (Affine.ChartPullback.GradedHilbert.affineChart_coefficient_isPullback I i).flip
  apply H₂.of_iso H₁.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change g ≫ 𝟙 _ = H₁.flip.isoPullback.hom ≫ pullback.snd (CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := S) I) b
    rw [Category.comp_id]
    exact H₁.flip.isoPullback_hom_snd.symm
  · change (a ≫ p') ≫ 𝟙 _ =
      H₁.flip.isoPullback.hom ≫ pullback.fst (CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := S) I) b ≫ p'
    rw [Category.comp_id]
    exact (congrArg (fun h => h ≫ p') H₁.flip.isoPullback_hom_fst.symm).trans
      (Category.assoc _ _ _)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp

def projectiveQuotientBaseChangeIso (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Quotient.GradedHilbert.projectiveQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) ≅
      pullback (Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (projectiveQuotient_isPullback I).isoPullback

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert
