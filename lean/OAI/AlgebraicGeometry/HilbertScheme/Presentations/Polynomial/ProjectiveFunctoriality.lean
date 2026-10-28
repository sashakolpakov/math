import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.ProjectiveBaseChange

/-! # Projective Functoriality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveFunctoriality.GradedHilbert

noncomputable section

/-! Polynomial projective coefficient maps and relative projective spaces
respect identities and composition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] {n : ℕ}

theorem gradedCoefficientMap_id :
    Graded.BaseChange.GradedHilbert.gradedCoefficientMap (n := n) (RingHom.id R) = GradedRingHom.id (Hilbert.Polynomial.GradedHilbert.grading R n) := by
  ext1 f
  exact MvPolynomial.map_id f

theorem gradedCoefficientMap_comp (φ : R →+* A) (ψ : A →+* B) :
    Graded.BaseChange.GradedHilbert.gradedCoefficientMap (n := n) (ψ.comp φ) = (Graded.BaseChange.GradedHilbert.gradedCoefficientMap ψ).comp (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ) := by
  ext1 f
  exact MvPolynomial.map_map φ ψ f |>.symm

theorem polynomialProjectiveCoefficientMap_id :
    ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) (RingHom.id R) = 𝟙 (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)) := by
  change Proj.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (RingHom.id R)) _ = _
  simpa only [gradedCoefficientMap_id] using (Proj.map_id (𝒜 := Hilbert.Polynomial.GradedHilbert.grading R n))

theorem polynomialProjectiveCoefficientMap_comp (φ : R →+* A) (ψ : A →+* B) :
    ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) (ψ.comp φ) =
      ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap ψ ≫ ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap φ := by
  change Proj.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (ψ.comp φ)) _ = Proj.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap ψ) _ ≫
    Proj.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ) _
  rw [← Proj.map_comp]
  congr 1
  exact gradedCoefficientMap_comp φ ψ

theorem relativeProjectiveBaseMap_id (X : Scheme.{u}) (n : ℕ) :
    Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap (𝟙 X) n = 𝟙 (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver X n).left := by
  apply pullback.hom_ext
  · rw [Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_coefficient, Category.id_comp]
    change _ ≫ ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (RingHom.id _) = _
    rw [polynomialProjectiveCoefficientMap_id, Category.comp_id]
  · exact (Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_projection (𝟙 X) n).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

theorem relativeProjectiveBaseMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap (f ≫ g) n = Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap f n ≫ Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap g n := by
  apply pullback.hom_ext
  · rw [Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_coefficient, Category.assoc, Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_coefficient,
      ← Category.assoc, Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_coefficient, Category.assoc]
    congr 1
    rw [Scheme.Hom.comp_appTop]
    exact polynomialProjectiveCoefficientMap_comp g.appTop.hom f.appTop.hom
  · change _ ≫ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver Z n).hom = (_ ≫ _) ≫ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver Z n).hom
    rw [Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_projection, Category.assoc, Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_projection]
    exact (congrArg (fun l => l ≫ g) (Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_projection f n)).symm.trans
      (Category.assoc _ _ _)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveFunctoriality.GradedHilbert
