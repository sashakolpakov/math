import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveCoefficientMap

/-! # Quotient Bot -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientBot.GradedHilbert

noncomputable section

/-! The projective quotient by the zero homogeneous ideal is canonically
the original polynomial projective space, over its coefficient ring. -/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (R : Type u) [CommRing R] (n : ℕ)

def gradedQuotientBotInverse : Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) →+*ᵍ Hilbert.Polynomial.GradedHilbert.grading R n where
  __ := (RingEquiv.quotientBot (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)).toRingHom
  map_mem h := by
    obtain ⟨f, hf, rfl⟩ := h
    exact hf

theorem gradedQuotientBotInverse_mk (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    gradedQuotientBotInverse R n (Graded.Quotient.GradedHilbert.gradedQuotientMap (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) f) = f :=
  RingEquiv.quotientBot_mk f

theorem gradedQuotientBotInverse_comp :
    (gradedQuotientBotInverse R n).comp (Graded.Quotient.GradedHilbert.gradedQuotientMap (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))) =
      GradedRingHom.id (Hilbert.Polynomial.GradedHilbert.grading R n) := by
  ext1 f
  exact gradedQuotientBotInverse_mk R n f

theorem gradedQuotientBot_comp_inverse :
    (Graded.Quotient.GradedHilbert.gradedQuotientMap (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))).comp (gradedQuotientBotInverse R n) =
      GradedRingHom.id (Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))) := by
  ext q
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  change Graded.Quotient.GradedHilbert.gradedQuotientMap (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (gradedQuotientBotInverse R n (Graded.Quotient.GradedHilbert.gradedQuotientMap (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) f)) = _
  rw [gradedQuotientBotInverse_mk]
  rfl

theorem irrelevant_gradedQuotientBotInverse_le_map :
    HomogeneousIdeal.irrelevant (Hilbert.Polynomial.GradedHilbert.grading R n) ≤
      (HomogeneousIdeal.irrelevant (Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)))).map
        (gradedQuotientBotInverse R n) := by
  change (HomogeneousIdeal.irrelevant (Hilbert.Polynomial.GradedHilbert.grading R n)).toIdeal ≤ _
  apply Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomial_irrelevant_le_span_variables.trans
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [← gradedQuotientBotInverse_mk R n (X i)]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem
    (Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))) Nat.zero_lt_one
      ((Graded.Quotient.GradedHilbert.gradedQuotientMap (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))).map_mem (isHomogeneous_X R i)))

def projectiveQuotientBotSection : Proj (Hilbert.Polynomial.GradedHilbert.grading R n) ⟶
    Projective.Quotient.GradedHilbert.projectiveQuotient (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :=
  Proj.map (gradedQuotientBotInverse R n) (irrelevant_gradedQuotientBotInverse_le_map R n)

theorem projectiveQuotientBotSection_inclusion :
    projectiveQuotientBotSection R n ≫ Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) =
      𝟙 _ := by
  change Proj.map (gradedQuotientBotInverse R n) _ ≫
    Proj.map (Graded.Quotient.GradedHilbert.gradedQuotientMap (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))) _ = 𝟙 _
  rw [← Proj.map_comp]
  simpa only [gradedQuotientBotInverse_comp] using (Proj.map_id (𝒜 := Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveQuotientBotInclusion_section :
    Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) ≫ projectiveQuotientBotSection R n =
      𝟙 _ := by
  change Proj.map (Graded.Quotient.GradedHilbert.gradedQuotientMap (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))) _ ≫
    Proj.map (gradedQuotientBotInverse R n) _ = 𝟙 _
  rw [← Proj.map_comp]
  simpa only [gradedQuotientBot_comp_inverse] using
    (Proj.map_id (𝒜 := Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))))

instance projectiveQuotientBotInclusion_isIso :
    IsIso (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))) :=
  ⟨⟨projectiveQuotientBotSection R n, projectiveQuotientBotInclusion_section R n,
    projectiveQuotientBotSection_inclusion R n⟩⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientBot.GradedHilbert
