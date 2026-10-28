import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness

/-! # Polynomial Family -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialFamily.GradedHilbert

noncomputable section

/-! The actual projective polynomial family over an arbitrary parameter scheme
is obtained by base change from its global coefficient ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))

def relativePolynomialFamily {T : Over S} (x : T ⟶ M) : Scheme.{u} :=
  pullback (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) (x.left ≫ M.left.toSpecΓ)

def relativePolynomialProjection {T : Over S} (x : T ⟶ M) : relativePolynomialFamily M I x ⟶ T.left :=
  pullback.snd _ _

instance relativePolynomialProjection_isProper {T : Over S} (x : T ⟶ M) :
    IsProper (relativePolynomialProjection M I x) := by
  have : IsProper (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Projective.Properness.GradedHilbert.projectiveQuotient_proper I
  exact inferInstanceAs (IsProper (pullback.snd (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))
    (x.left ≫ M.left.toSpecΓ)))

theorem relativePolynomialProjection_flat_of_coefficients {T : Over S} (x : T ⟶ M)
    (hflat : letI : Algebra Γ(M.left, ⊤) Γ(T.left, ⊤) := x.left.appTop.hom.toAlgebra
      Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Γ(T.left, ⊤)) I)))) :
    Flat (relativePolynomialProjection M I x) := by
  let : Algebra Γ(M.left, ⊤) Γ(T.left, ⊤) := x.left.appTop.hom.toAlgebra
  let p := Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)
  let p' := Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Γ(T.left, ⊤)) I))
  have : Flat p' := hflat
  have h₁ := IsPullback.of_hasPullback p' T.left.toSpecΓ
  have h₂ := Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback (S := Γ(T.left, ⊤)) I
  have hcomp := h₁.paste_horiz h₂
  have hΓ : T.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(M.left, ⊤) Γ(T.left, ⊤))) =
      x.left ≫ M.left.toSpecΓ := (Scheme.toSpecΓ_naturality x.left).symm
  rw [hΓ] at hcomp
  have he := hcomp.isoPullback_inv_snd
  have hc : Flat (hcomp.isoPullback.inv ≫ pullback.snd p' T.left.toSpecΓ) := inferInstance
  rw [he] at hc
  exact hc

theorem relativePolynomialProjection_flat_of_affine_tests {T : Over S} (x : T ⟶ M)
    (h : ∀ (U : Over S) [IsAffine U.left] (a : U ⟶ T),
      Flat (relativePolynomialProjection M I (a ≫ x))) :
    Flat (relativePolynomialProjection M I x) := by
  let C := T.left.affineCover
  have : IsZariskiLocalAtTarget @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{u}) (Q := RingHom.Flat)
  apply (IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) C).mpr
  intro i
  let U : Over S := Over.mk (C.f i ≫ T.hom)
  let a : U ⟶ T := Over.homMk (C.f i) rfl
  have : IsAffine U.left := inferInstanceAs (IsAffine (C.X i))
  have hp := h U a
  let p := Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)
  let b := x.left ≫ M.left.toSpecΓ
  have heq : (a ≫ x).left ≫ M.left.toSpecΓ = C.f i ≫ b := Category.assoc _ _ _
  change Flat (pullback.snd p ((a ≫ x).left ≫ M.left.toSpecΓ)) at hp
  rw [heq] at hp
  let := hp
  let e := pullbackLeftPullbackSndIso p b (C.f i)
  have hc : Flat (e.hom ≫ pullback.snd p (C.f i ≫ b)) := inferInstance
  dsimp only [e] at hc
  rw [pullbackLeftPullbackSndIso_hom_snd] at hc
  exact hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialFamily.GradedHilbert
