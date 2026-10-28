import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialAmbient

/-! # Projective Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert

noncomputable section

/-! Relative polynomial projective spaces commute with arbitrary changes
of base scheme, through their actual coefficient morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)

def relativeProjectiveBaseMap : (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver X n).left ⟶ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver Y n).left := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let pX := Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(X, ⊤) n)
  let pY := Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(Y, ⊤) n)
  let c : Proj (Hilbert.Polynomial.GradedHilbert.grading Γ(X, ⊤) n) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading Γ(Y, ⊤) n) :=
    Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap f.appTop.hom
  have hc : c ≫ pY = pX ≫ Spec.map f.appTop := Polynomial.ProjectiveBaseChange.GradedHilbert.polynomialProjectiveCoefficientMap_over
  change pullback pX X.toSpecΓ ⟶ pullback pY Y.toSpecΓ
  refine pullback.lift (pullback.fst _ _ ≫ c) (pullback.snd _ _ ≫ f) ?_
  rw [Category.assoc, hc, ← Category.assoc, pullback.condition, Category.assoc,
    ← Scheme.toSpecΓ_naturality f, ← Category.assoc]

theorem relativeProjectiveBaseMap_coefficient :
    relativeProjectiveBaseMap f n ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) f.appTop.hom := pullback.lift_fst _ _ _

theorem relativeProjectiveBaseMap_projection :
    relativeProjectiveBaseMap f n ≫ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver Y n).hom =
      (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver X n).hom ≫ f := pullback.lift_snd _ _ _

theorem relativeProjectiveBaseMap_isPullback :
    IsPullback (relativeProjectiveBaseMap f n) (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver X n).hom
      (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver Y n).hom f := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let pX := Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(X, ⊤) n)
  let pY := Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(Y, ⊤) n)
  let c : Proj (Hilbert.Polynomial.GradedHilbert.grading Γ(X, ⊤) n) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading Γ(Y, ⊤) n) :=
    Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap f.appTop.hom
  have hc : IsPullback c pX pY (Spec.map f.appTop) := Polynomial.ProjectiveBaseChange.GradedHilbert.polynomialProjective_isPullback
  have hout := (IsPullback.of_hasPullback pX X.toSpecΓ).paste_horiz hc
  rw [← Scheme.toSpecΓ_naturality f] at hout
  have hk : relativeProjectiveBaseMap f n ≫ pullback.fst pY Y.toSpecΓ =
      pullback.fst pX X.toSpecΓ ≫ c := relativeProjectiveBaseMap_coefficient f n
  rw [← hk] at hout
  exact hout.of_right (relativeProjectiveBaseMap_projection f n) (IsPullback.of_hasPullback pY Y.toSpecΓ)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert
