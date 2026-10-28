import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange

/-! # Coefficient Functoriality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality

noncomputable section

/-! Standard projective coefficient maps with explicit ring homomorphisms and composition laws. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def polynomialProjectiveMap {R A : CommRingCat.{u}} (φ : R ⟶ A) (n : ℕ) :
    (ProjectivePresentations.affineProjectiveSpace A n).left ⟶ (ProjectivePresentations.affineProjectiveSpace R n).left := by
  let : Algebra R A := φ.hom.toAlgebra
  exact Polynomial.ProjectiveCoefficients.polynomialProjectiveCoefficientMap

theorem polynomialProjectiveMap_isPullback {R A : CommRingCat.{u}} (φ : R ⟶ A) (n : ℕ) :
    IsPullback (polynomialProjectiveMap φ n) (ProjectivePresentations.affineProjectiveSpace A n).hom
      (ProjectivePresentations.affineProjectiveSpace R n).hom (Spec.map φ) := by
  let : Algebra R A := φ.hom.toAlgebra
  exact CoefficientPullback.polynomialProjectiveCoefficient_isPullback

theorem polynomialProjectiveMap_over {R A : CommRingCat.{u}} (φ : R ⟶ A) (n : ℕ) :
    polynomialProjectiveMap φ n ≫ (ProjectivePresentations.affineProjectiveSpace R n).hom =
      (ProjectivePresentations.affineProjectiveSpace A n).hom ≫ Spec.map φ :=
  (polynomialProjectiveMap_isPullback φ n).w

theorem polynomialProjectiveMap_comp {R A C : CommRingCat.{u}}
    (φ : R ⟶ A) (ψ : A ⟶ C) (n : ℕ) :
    polynomialProjectiveMap (φ ≫ ψ) n =
      polynomialProjectiveMap ψ n ≫ polynomialProjectiveMap φ n := by
  change Proj.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (ψ.hom.comp φ.hom)) _ =
    Proj.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap ψ.hom) _ ≫ Proj.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ.hom) _
  rw [← Proj.map_comp]
  have he : (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (n := n) ψ.hom).comp (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ.hom) =
      HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (ψ.hom.comp φ.hom) := by
    apply GradedRingHom.ext
    intro p
    exact MvPolynomial.map_map φ.hom ψ.hom p
  simp only [he]

theorem polynomialProjectiveMap_id (R : CommRingCat.{u}) (n : ℕ) :
    polynomialProjectiveMap (𝟙 R) n = 𝟙 (ProjectivePresentations.affineProjectiveSpace R n).left := by
  change Proj.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (RingHom.id R)) _ = _
  have he : HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (n := n) (RingHom.id R) = GradedRingHom.id (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) := by
    apply GradedRingHom.ext
    intro p
    exact MvPolynomial.map_id p
  simp only [he, Proj.map_id]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality
