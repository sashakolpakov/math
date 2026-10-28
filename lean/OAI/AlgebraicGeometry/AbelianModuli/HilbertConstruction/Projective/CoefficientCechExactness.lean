import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCechBounded

/-! # Coefficient Cech Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCechExactness

noncomputable section

/-! Exactness of the projective coefficient Cech functor on quasicoherent short exact sequences. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

/-- The short complex obtained by applying the projective coefficient Cech functor. -/
abbrev projectiveCoefficientCechMappedShortComplex
    (T : ShortComplex (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) := by
  change ShortComplex (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules at T
  exact T.map (CoefficientCechFunctor.projectiveCoefficientCechFunctor I)

theorem projectiveCoefficientCech_shortExact {T : ShortComplex (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I).Modules}
    (hT : T.ShortExact) [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent] :
    (projectiveCoefficientCechMappedShortComplex I T).ShortExact := by
  rename_i h₁ h₂ h₃
  dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient] at *
  let p := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
  let : IsProper p := HilbertScheme.Presentations.Projective.Properness.GradedHilbert.projectiveQuotient_proper I
  let : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).IsSeparated := ⟨by
    rw [← terminal.comp_from p]
    infer_instance⟩
  exact @Ordered.CoefficientCechExactness.orderedCoefficientCech_shortExact
    (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) R inferInstance _ inferInstance
    (ULift.{u} (Fin (n + 1))) inferInstance
    (CechCover.projectiveCechOpens I) (CechCover.projectiveCechOpens_affine I) T hT h₁ h₂ h₃

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCechExactness
