import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.EmbeddingBaseChange
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Ideal Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual defining ideals of the generated projective families commute with coefficient changes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Projective.IdealBaseChange.closedImmersion_kernel_isPullback {X Y X' Y' : Scheme.{u}}
    (i : X ⟶ Y) (i' : X' ⟶ Y') (a : X' ⟶ X) (b : Y' ⟶ Y)
    [IsClosedImmersion i] (h : IsPullback a i' i b) :
    i'.ker = i.ker.comap b :=
  (congrArg Scheme.Hom.ker h.flip.isoPullback_hom_fst).symm.trans
    ((Scheme.Hom.ker_comp_of_isIso h.flip.isoPullback.hom _).trans
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i b))

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

theorem Projective.IdealBaseChange.projectiveQuotientIdeal_baseChange (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).ker =
      (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).ker.comap
        (Polynomial.ProjectiveCoefficients.polynomialProjectiveCoefficientMap (R := R) (A := A)) :=
  Projective.IdealBaseChange.closedImmersion_kernel_isPullback _ _ _ _ (Projective.CoefficientPullback.projectiveQuotientEmbedding_isPullback I)

variable {B : ℕ} {r : ℕ → ℕ}
variable (D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r)

def Truncated.GradedClassification.TruncatedGradedQuotientData.projectiveIdeal : (Projective.ProjectivePresentations.affineProjectiveSpace R n).left.IdealSheafData :=
  D.projectiveEmbedding.left.ker

theorem Truncated.GradedClassification.TruncatedGradedQuotientData.projectiveIdeal_baseChange :
    (D.baseChange A).projectiveIdeal = D.projectiveIdeal.comap
      (Polynomial.ProjectiveCoefficients.polynomialProjectiveCoefficientMap (R := R) (A := A)) := by
  change (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (D.baseChange A).generatedIdeal).ker = _
  rw [D.baseChange_generatedIdeal]
  exact Projective.IdealBaseChange.projectiveQuotientIdeal_baseChange D.generatedIdeal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
