import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialProjectiveBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.ReesPresentation
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace

/-! # Blowup Projective Product -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupProjectiveProduct.Construction

noncomputable section

/-! Closed embeddings of affine blowups into relative complex projective space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] [Algebra ℂ R] {m : ℕ}

/-- Polynomial projective space over a complex algebra is the actual
fiber product with complex projective space. -/
def complexPolynomialProjectiveIso :
    Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R m) ≅ pullback (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :=
  PolynomialProjectiveBaseChange.Construction.polynomialProjectiveBaseChangeIso (R := ℂ) (S := R) (n := m)

theorem complexPolynomialProjectiveIso_hom_snd :
    (complexPolynomialProjectiveIso (R := R) (m := m)).hom ≫ pullback.snd _ _ =
      ReesPresentation.Construction.polynomialProjToSpec :=
  (PolynomialProjectiveBaseChange.Construction.polynomialProjective_isPullback (R := ℂ) (S := R) (n := m)).isoPullback_hom_snd

variable (I : Ideal R) (a : Fin (m + 1) → I)
variable (hgen : Submodule.span R (Set.range a) = ⊤)

/-- The Rees presentation gives a closed embedding into `ℙᵐ_ℂ × Spec R`. -/
def affineBlowupProjectiveProductEmbedding :
    ReesGrading.Construction.affineBlowup I ⟶ pullback (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :=
  ReesPresentation.Construction.affineBlowupProjectiveEmbedding I a hgen ≫ complexPolynomialProjectiveIso.hom

instance affineBlowupProjectiveProductEmbedding_isClosedImmersion :
    IsClosedImmersion (affineBlowupProjectiveProductEmbedding I a hgen) := by
  unfold affineBlowupProjectiveProductEmbedding
  infer_instance

/-- The product embedding retains the original blowup projection. -/
theorem affineBlowupProjectiveProductEmbedding_over :
    affineBlowupProjectiveProductEmbedding I a hgen ≫ pullback.snd _ _ =
      ReesGrading.Construction.affineBlowupToSpec I := by
  rw [affineBlowupProjectiveProductEmbedding, Category.assoc,
    complexPolynomialProjectiveIso_hom_snd, ReesPresentation.Construction.affineBlowupProjectiveEmbedding_over]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupProjectiveProduct.Construction
