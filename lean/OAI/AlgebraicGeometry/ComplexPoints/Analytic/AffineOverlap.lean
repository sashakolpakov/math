import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenLifts
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalizationPointTopology

/-! # Affine Overlap -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic

noncomputable section

/-!
# Actual point transitions on affine open overlaps

A local factorization of one affine chart through another determines a
transition by an algebra map into a principal localization. This file proves
that the transition gives exactly the same native complex point, and exposes
its coordinate evaluations as fractions of regular evaluations.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The continuous character transition induced by a map into a principal
localization. Its domain is the ordinary principal open set. -/
def SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition (A B : CommAlgCat ℂ) (a : A)
    (h : B →ₐ[ℂ] Localization.Away a) :
    C(Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a, Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) where
  toFun y := (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y.val a y.property).comp h
  continuous_toFun := (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h).continuous.comp
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_localizePoint a)

@[simp]
theorem SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition_apply (A B : CommAlgCat ℂ) (a : A)
    (h : B →ₐ[ℂ] Localization.Away a)
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a) :
    SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h y =
      (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y.val a y.property).comp h := rfl

/-- Each transition coordinate is a quotient of two ordinary evaluations,
with denominator a power of the defining nonvanishing regular function. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition_eval (A B : CommAlgCat ℂ) (a : A)
    (h : B →ₐ[ℂ] Localization.Away a)
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a) (b : B) :
    SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h y b =
      y.val (IsLocalization.Away.sec a (h b)).1 /
        (y.val a) ^ (IsLocalization.Away.sec a (h b)).2 := by
  exact Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_eq_div_sec y.val a y.property (h b)

/-- A genuine local affine factorization gives the same native scheme point
on every character where its denominator is nonzero. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_localize_comp (A B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X)
    (a : A) (h : B →ₐ[ℂ] Localization.Away a)
    (hfac : Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B (Localization.Away a) h ≫ j =
      Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
        (Algebra.algHom ℂ A (Localization.Away a)) ≫ i)
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hy : y a ≠ 0) :
    SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j ((Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y a hy).comp h) =
      SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i y := by
  calc
    SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j ((Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y a hy).comp h) =
        SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (Localization.Away a))
          (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B (Localization.Away a) h ≫ j)
          (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y a hy) :=
      (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap B (CommAlgCat.of ℂ (Localization.Away a)) h j _).symm
    _ = SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ (Localization.Away a))
          (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
            (Algebra.algHom ℂ A (Localization.Away a)) ≫ i)
          (Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y a hy) := by rw [hfac]
    _ = SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i y := by
      rw [SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comap]
      change SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i
        ((Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint y a hy).comp
          (Algebra.algHom ℂ A (Localization.Away a))) = _
      rw [Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp]

/-- The bundled continuous overlap transition commutes with the actual chart
maps to native complex points. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition_point (A B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X)
    (a : A) (h : B →ₐ[ℂ] Localization.Away a)
    (hfac : Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B (Localization.Away a) h ≫ j =
      Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
        (Algebra.algHom ℂ A (Localization.Away a)) ≫ i)
    (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a) :
    SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j (SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h y) =
      SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i y.val :=
  SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_localize_comp A B i j a h hfac y.val y.property

/-- At every point shared with an affine open chart, there is a principal
neighborhood with a genuine localization algebra map describing its transition.
Coverage and the point identity follow from the native open immersion. -/
theorem SchemePointHomeomorphs.schemeComplexPoints.exists_affineLocalizationTransition (A B : CommAlgCat ℂ)
    (i : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) (j : Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ X)
    [IsOpenImmersion j.left] (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
    (hx : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j)) :
    ∃ a : A, x a ≠ 0 ∧ ∃ h : B →ₐ[ℂ] Localization.Away a,
      (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B (Localization.Away a) h ≫ j =
        Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
          (Algebra.algHom ℂ A (Localization.Away a)) ≫ i) ∧
      ∀ y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.principalOpen a,
        SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j (SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition A B a h y) =
          SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i y.val := by
  have hx' : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i x ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.map j) := by
    obtain ⟨z, hz⟩ := hx
    exact ⟨SchemePointHomeomorphs.affineSchemePointEquiv B z, hz⟩
  obtain ⟨a, ha, l, hl⟩ := SchemePointHomeomorphs.schemeComplexPoints.exists_localizationLift j A i x hx'
  let h := (Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B (Localization.Away a)).symm l
  have hfac : Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ B (Localization.Away a) h ≫ j =
      Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A (Localization.Away a)
        (Algebra.algHom ℂ A (Localization.Away a)) ≫ i := by
    simpa only [h, Equiv.apply_symm_apply] using hl
  exact ⟨a, ha, h, hfac, SchemePointHomeomorphs.schemeComplexPoints.affineLocalizationTransition_point A B i j a h hfac⟩

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic
