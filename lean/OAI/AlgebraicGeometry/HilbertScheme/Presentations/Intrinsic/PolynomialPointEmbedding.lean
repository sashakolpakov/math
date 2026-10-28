import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialPointComparison
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial

/-! # Polynomial Point Embedding -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialPointEmbedding.GradedHilbert

noncomputable section

/-! The native ideal-sheaf subscheme over a field-valued point has an actual
closed embedding in polynomial projective space, with the computed Hilbert polynomial. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))
variable {R : Type u} [CommRing R] (a : Spec (CommRingCat.of R) ⟶ M.left)

def nativePolynomialPointSubschemeIso : Projective.Quotient.GradedHilbert.projectiveQuotient (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a) ≅
    (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).ker.subscheme :=
  Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso M I a ≪≫ asIso (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).toImage

def nativePolynomialPointEmbedding :
    (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).ker.subscheme ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  (nativePolynomialPointSubschemeIso M I a).inv ≫ Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a)

instance nativePolynomialPointEmbedding_isClosedImmersion :
    IsClosedImmersion (nativePolynomialPointEmbedding M I a) :=
  inferInstanceAs (IsClosedImmersion ((nativePolynomialPointSubschemeIso M I a).inv ≫
    Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a)))

theorem nativePolynomialPointSubschemeIso_projection :
    (nativePolynomialPointSubschemeIso M I a).hom ≫
        Hilbert.Functor.familyProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n)
          (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).ker =
      Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a)) := by
  have h : (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).toImage ≫
      Hilbert.Functor.familyProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n)
        (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).ker =
      Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a) :=
    (Closed.ImmersionFamily.Hilbert.closedImmersion_image_projection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n)
      (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a))).trans
        (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion_projection M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a))
  change ((Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso M I a).hom ≫
    (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).toImage) ≫ _ = _
  exact (Category.assoc _ _ _).trans ((congrArg (fun f => (Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso M I a).hom ≫ f) h).trans
    (Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso_projection M I a))

theorem nativePolynomialPointEmbedding_projection :
    nativePolynomialPointEmbedding M I a ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) =
      Hilbert.Functor.familyProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n)
        (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).ker := by
  have he := (Iso.eq_inv_comp (nativePolynomialPointSubschemeIso M I a)).mpr
    (nativePolynomialPointSubschemeIso_projection M I a)
  change ((nativePolynomialPointSubschemeIso M I a).inv ≫
    Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a)) ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (nativePolynomialPointSubschemeIso M I a).inv ≫ f)
      (Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a))).trans he.symm)

theorem nativePolynomialPointEmbedding_ambient :
    nativePolynomialPointEmbedding M I a ≫ Projective.Point.GradedHilbert.projectiveSchemePointMap n a =
      (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).ker.subschemeι ≫
        (prod.snd : Over.mk a ⨯ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left := by
  apply (cancel_epi (nativePolynomialPointSubschemeIso M I a).hom).mp
  have hleft : (nativePolynomialPointSubschemeIso M I a).hom ≫ nativePolynomialPointEmbedding M I a =
      Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a) := by
    change (nativePolynomialPointSubschemeIso M I a).hom ≫
      ((nativePolynomialPointSubschemeIso M I a).inv ≫ _) = _
    exact Iso.hom_inv_id_assoc _ _
  have hright : (nativePolynomialPointSubschemeIso M I a).hom ≫
      (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).ker.subschemeι =
        (Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso M I a).hom ≫ PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a) := by
    change ((Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso M I a).hom ≫
      (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).toImage) ≫
      (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).imageι = _
    rw [Category.assoc, Scheme.Hom.toImage_imageι]
  let s : Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk a) ⟶
      (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left :=
    (prod.snd : Over.mk a ⨯ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left
  let e : Projective.Quotient.GradedHilbert.projectiveQuotient (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a) ⟶
      Relative.PolynomialFamily.GradedHilbert.relativePolynomialFamily M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a) := (Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso M I a).hom
  let k : Relative.PolynomialFamily.GradedHilbert.relativePolynomialFamily M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a) ⟶
      Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk a) :=
    PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)
  have hc : Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a) ≫ Projective.Point.GradedHilbert.projectiveSchemePointMap n a =
      e ≫ k ≫ s := (PolynomialPointComparison.GradedHilbert.projectiveQuotientPointIso_native_inclusion M I a).symm
  have hr : (nativePolynomialPointSubschemeIso M I a).hom ≫
      (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).ker.subschemeι = e ≫ k := hright
  calc
    _ = ((nativePolynomialPointSubschemeIso M I a).hom ≫ nativePolynomialPointEmbedding M I a) ≫
        Projective.Point.GradedHilbert.projectiveSchemePointMap n a := (Category.assoc _ _ _).symm
    _ = Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a) ≫ Projective.Point.GradedHilbert.projectiveSchemePointMap n a :=
      congrArg (fun f => f ≫ Projective.Point.GradedHilbert.projectiveSchemePointMap n a) hleft
    _ = e ≫ k ≫ s := hc
    _ = ((nativePolynomialPointSubschemeIso M I a).hom ≫
        (PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)).ker.subschemeι) ≫ s :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ s) hr).symm
    _ = _ := Category.assoc _ _ _

theorem nativePolynomialPointEmbedding_hilbertPolynomial [IsNoetherianRing R] (P : Polynomial ℚ)
    (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a).toIdeal P) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (nativePolynomialPointEmbedding M I a).ker).toIdeal P := by
  rw [nativePolynomialPointEmbedding, Scheme.Hom.ker_comp_of_isIso]
  exact (Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a) P).mpr hP

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialPointEmbedding.GradedHilbert
