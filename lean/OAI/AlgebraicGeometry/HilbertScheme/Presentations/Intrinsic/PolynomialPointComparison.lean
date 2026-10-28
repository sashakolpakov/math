import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientPoint

/-! # Polynomial Point Comparison -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialPointComparison.GradedHilbert

noncomputable section

/-! The actual point-fiber isomorphism respects the native Hilbert closed
embedding into relative projective space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}

theorem nativePolynomialAmbient_second_projection {T : Over S} (x : T ⟶ M) :
    (prod.snd : Over.mk x.left ⨯ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left ≫
        (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).hom =
      Hilbert.Functor.ambientProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk x.left) ≫ x.left :=
  (prod.snd : Over.mk x.left ⨯ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).w.trans
    (prod.fst : Over.mk x.left ⨯ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ Over.mk x.left).w.symm

variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))
variable {R : Type u} [CommRing R] (a : Spec (CommRingCat.of R) ⟶ M.left)

theorem projectiveQuotientPointIso_native_inclusion :
    (Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso M I a).hom ≫ PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a) ≫
        (prod.snd : Over.mk a ⨯ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left =
      Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a) ≫ Projective.Point.GradedHilbert.projectiveSchemePointMap n a := by
  let F := Relative.PolynomialFamily.GradedHilbert.relativePolynomialFamily M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)
  let A := Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk a)
  let J := Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a
  let e : Proj (Graded.Quotient.GradedHilbert.quotientGrading J) ≅ F := Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso M I a
  let k : F ⟶ A := PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)
  let s : A ⟶ (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left :=
    (prod.snd : Over.mk a ⨯ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left
  let j : Proj (Graded.Quotient.GradedHilbert.quotientGrading J) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading R n) := Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J
  let jI : Proj (Graded.Quotient.GradedHilbert.quotientGrading I) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n) := Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I
  let r : F ⟶ Proj (Graded.Quotient.GradedHilbert.quotientGrading I) := pullback.fst _ _
  let c : Proj (Graded.Quotient.GradedHilbert.quotientGrading J) ⟶ Proj (Graded.Quotient.GradedHilbert.quotientGrading I) := Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointCoefficient M I a
  let q := Projective.Point.GradedHilbert.projectiveSchemePointMap n a
  let t : A ⟶ Spec (CommRingCat.of R) := Hilbert.Functor.ambientProjection (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n) (Over.mk a)
  let pF : F ⟶ Spec (CommRingCat.of R) := Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)
  let pJ := Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J)
  let pR := Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n)
  change e.hom ≫ k ≫ s = j ≫ q
  apply pullback.hom_ext
  · have hk : k ≫ s ≫ pullback.fst _ _ = r ≫ jI := PolynomialCoordinates.GradedHilbert.nativePolynomialInclusion_coefficient M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)
    have he : e.hom ≫ r = c := Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso_coefficient M I a
    have hc : c ≫ jI = j ≫ Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) (PointCoefficients.schemePointCoefficientMap a) :=
      Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointCoefficient_inclusion M I a
    have hq : q ≫ pullback.fst _ _ = Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) (PointCoefficients.schemePointCoefficientMap a) :=
      Projective.Point.GradedHilbert.projectiveSchemePointMap_coefficient n a
    calc
      _ = e.hom ≫ (k ≫ s ≫ pullback.fst _ _) := by simp only [Category.assoc]
      _ = e.hom ≫ (r ≫ jI) := congrArg (fun l => e.hom ≫ l) hk
      _ = (e.hom ≫ r) ≫ jI := (Category.assoc _ _ _).symm
      _ = c ≫ jI := congrArg (fun l => l ≫ jI) he
      _ = j ≫ Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) (PointCoefficients.schemePointCoefficientMap a) := hc
      _ = _ := by rw [Category.assoc, hq]
  · change (e.hom ≫ k ≫ s) ≫ (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).hom =
      (j ≫ q) ≫ (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).hom
    have hs : s ≫ (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).hom = t ≫ a :=
      nativePolynomialAmbient_second_projection M (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)
    have hk : k ≫ t = pF := PolynomialAmbient.GradedHilbert.nativePolynomialInclusion_projection M I (Projective.QuotientPoint.GradedHilbert.polynomialPointMorphism M a)
    have he : e.hom ≫ pF = pJ := Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso_projection M I a
    have hq : q ≫ (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).hom = pR ≫ a := Projective.Point.GradedHilbert.projectiveSchemePointMap_projection n a
    have hj : j ≫ pR = pJ := Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure J
    calc
      _ = e.hom ≫ k ≫ (s ≫ (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).hom) := by simp only [Category.assoc]
      _ = e.hom ≫ k ≫ (t ≫ a) := by rw [hs]
      _ = (e.hom ≫ (k ≫ t)) ≫ a := by simp only [Category.assoc]
      _ = (e.hom ≫ pF) ≫ a := by rw [hk]
      _ = pJ ≫ a := congrArg (fun l => l ≫ a) he
      _ = _ := by rw [Category.assoc, hq, ← Category.assoc, hj]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialPointComparison.GradedHilbert
