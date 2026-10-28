import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.ProjectiveBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PointCoefficients

/-! # Point -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Point

noncomputable section

/-! Polynomial projective space over a ring-valued point is the actual
fiber of relative projective space over that point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {M : Scheme.{u}} {R : Type u} [CommRing R]

theorem schemePointCoefficientMap_spec (a : Spec (CommRingCat.of R) ⟶ M) :
    Spec.map (CommRingCat.ofHom (PointCoefficients.schemePointCoefficientMap a)) = a ≫ M.toSpecΓ := by
  change Spec.map (a.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) = _
  rw [Spec.map_comp, SpecMap_ΓSpecIso_hom]
  exact (Scheme.toSpecΓ_naturality a).symm

namespace GradedHilbert

variable (n : ℕ) (a : Spec (CommRingCat.of R) ⟶ M)

def projectiveSchemePointMap : Proj (Hilbert.Polynomial.GradedHilbert.grading R n) ⟶ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M n).left := by
  let : Algebra Γ(M, ⊤) R := (PointCoefficients.schemePointCoefficientMap a).toAlgebra
  refine pullback.lift (Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (PointCoefficients.schemePointCoefficientMap a))
    (Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) ≫ a) ?_
  have hc : Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) (PointCoefficients.schemePointCoefficientMap a) ≫
      Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(M, ⊤) n) =
    Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) ≫ Spec.map (CommRingCat.ofHom (PointCoefficients.schemePointCoefficientMap a)) :=
      Polynomial.ProjectiveBaseChange.GradedHilbert.polynomialProjectiveCoefficientMap_over
  rw [hc, schemePointCoefficientMap_spec, ← Category.assoc]

theorem projectiveSchemePointMap_coefficient :
    projectiveSchemePointMap n a ≫ pullback.fst _ _ =
      Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) (PointCoefficients.schemePointCoefficientMap a) := pullback.lift_fst _ _ _

theorem projectiveSchemePointMap_projection :
    projectiveSchemePointMap n a ≫ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M n).hom =
      Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) ≫ a := pullback.lift_snd _ _ _

theorem projectiveSchemePointMap_isPullback :
    IsPullback (projectiveSchemePointMap n a) (Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n))
      (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M n).hom a := by
  let : Algebra Γ(M, ⊤) R := (PointCoefficients.schemePointCoefficientMap a).toAlgebra
  have hc : IsPullback (Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) (PointCoefficients.schemePointCoefficientMap a))
      (Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n)) (Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(M, ⊤) n))
      (Spec.map (CommRingCat.ofHom (PointCoefficients.schemePointCoefficientMap a))) := Polynomial.ProjectiveBaseChange.GradedHilbert.polynomialProjective_isPullback
  rw [schemePointCoefficientMap_spec, ← projectiveSchemePointMap_coefficient n a] at hc
  exact hc.of_right (projectiveSchemePointMap_projection n a)
    (IsPullback.of_hasPullback (Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(M, ⊤) n)) M.toSpecΓ)

end GradedHilbert

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Point
