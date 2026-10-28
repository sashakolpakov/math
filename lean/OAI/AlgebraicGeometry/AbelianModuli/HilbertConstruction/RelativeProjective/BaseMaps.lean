import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.Charts

/-! # Base Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseMaps

noncomputable section

/-! Explicit base morphisms of relative projective spaces, compatible with the affine coefficient charts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} (f : T ⟶ S) (n : ℕ)

def relativeProjectiveCoefficientProjection (S : Scheme.{u}) (n : ℕ) :
    (Projective.ProjectivePresentations.projectiveSpaceOver S n).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left :=
  pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ

theorem relativeProjectiveCoefficientProjection_over (S : Scheme.{u}) (n : ℕ) :
    relativeProjectiveCoefficientProjection S n ≫ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom =
      (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom ≫ S.toSpecΓ := pullback.condition

theorem relativeProjectiveCoefficientProjection_isPullback (S : Scheme.{u}) (n : ℕ) :
    IsPullback (relativeProjectiveCoefficientProjection S n) (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom
      (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ := IsPullback.of_hasPullback _ _

theorem relativeProjectiveCoefficientProjection_affine {S : Scheme.{u}} {R : CommRingCat.{u}}
    (x : Spec R ⟶ S) (n : ℕ) :
    AffineProjective.Charts.affineProjectiveChartMap x n ≫ relativeProjectiveCoefficientProjection S n =
      Projective.CoefficientFunctoriality.polynomialProjectiveMap (AffineProjective.Charts.affinePointCoefficients x) n := AffineProjective.Charts.affineProjectiveChartMap_fst x n

def relativeProjectiveBaseMap : (Projective.ProjectivePresentations.projectiveSpaceOver T n).left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver S n).left :=
  pullback.lift
    (relativeProjectiveCoefficientProjection T n ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap f.appTop n)
    ((Projective.ProjectivePresentations.projectiveSpaceOver T n).hom ≫ f) (by
      rw [Category.assoc, Projective.CoefficientFunctoriality.polynomialProjectiveMap_over, ← Category.assoc,
        relativeProjectiveCoefficientProjection_over, Category.assoc, ← Scheme.toSpecΓ_naturality,
        ← Category.assoc])

theorem relativeProjectiveBaseMap_fst :
    relativeProjectiveBaseMap f n ≫ relativeProjectiveCoefficientProjection S n =
      relativeProjectiveCoefficientProjection T n ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap f.appTop n :=
  pullback.lift_fst _ _ _

theorem relativeProjectiveBaseMap_over :
    relativeProjectiveBaseMap f n ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom = (Projective.ProjectivePresentations.projectiveSpaceOver T n).hom ≫ f :=
  pullback.lift_snd _ _ _

theorem relativeProjectiveBaseMap_isPullback :
    IsPullback (relativeProjectiveBaseMap f n) (Projective.ProjectivePresentations.projectiveSpaceOver T n).hom
      (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom f := by
  have h := (relativeProjectiveCoefficientProjection_isPullback T n).paste_horiz
    (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback f.appTop n)
  rw [← Scheme.toSpecΓ_naturality f] at h
  have houter : IsPullback (relativeProjectiveBaseMap f n ≫
      relativeProjectiveCoefficientProjection S n)
      (Projective.ProjectivePresentations.projectiveSpaceOver T n).hom (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom (f ≫ S.toSpecΓ) := by
    rw [relativeProjectiveBaseMap_fst]
    exact h
  exact houter.of_right (relativeProjectiveBaseMap_over f n)
    (relativeProjectiveCoefficientProjection_isPullback S n)

theorem affinePointCoefficients_postcomp {R : CommRingCat.{u}} (x : Spec R ⟶ T) :
    AffineProjective.Charts.affinePointCoefficients (x ≫ f) = f.appTop ≫ AffineProjective.Charts.affinePointCoefficients x := by
  change (f.appTop ≫ x.appTop) ≫ (Scheme.ΓSpecIso R).hom = _
  exact Category.assoc _ _ _

theorem relativeProjectiveBaseMap_affine {R : CommRingCat.{u}} (x : Spec R ⟶ T) :
    AffineProjective.Charts.affineProjectiveChartMap x n ≫ relativeProjectiveBaseMap f n = AffineProjective.Charts.affineProjectiveChartMap (x ≫ f) n := by
  apply (relativeProjectiveCoefficientProjection_isPullback S n).hom_ext
  · rw [Category.assoc, relativeProjectiveBaseMap_fst, ← Category.assoc, relativeProjectiveCoefficientProjection_affine,
      ← Projective.CoefficientFunctoriality.polynomialProjectiveMap_comp, relativeProjectiveCoefficientProjection_affine, affinePointCoefficients_postcomp]
  ·
    rw [Category.assoc, relativeProjectiveBaseMap_over, ← Category.assoc, AffineProjective.Charts.affineProjectiveChartMap_over,
      Category.assoc, AffineProjective.Charts.affineProjectiveChartMap_over]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseMaps
