import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ParameterSpecialization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.PolynomialInclusion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveFunctoriality

/-! # Specialization Embedding -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.SpecializationEmbedding.GradedHilbert

noncomputable section

/-! Coefficient specialization respects the actual polynomial closed
embedding, including its map to the original relative projective space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n)) {T : Over S} (x : T ⟶ M)

theorem relativePolynomialParameterIso_native_projective :
    (ParameterSpecialization.GradedHilbert.relativePolynomialParameterIso M I x).hom ≫ Intrinsic.PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x ≫
        (prod.snd : Over.mk x.left ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left =
      Intrinsic.PolynomialAmbient.GradedHilbert.nativePolynomialInclusion T (ParameterSpecialization.GradedHilbert.parameterHomogeneousIdeal M I x) (𝟙 T) ≫
        (prod.snd : Over.mk (𝟙 T.left) ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T.left n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T.left n).left ≫
          Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap x.left n := by
  let J := ParameterSpecialization.GradedHilbert.parameterHomogeneousIdeal M I x
  let F := Relative.PolynomialFamily.GradedHilbert.relativePolynomialFamily M I x
  let G := Relative.PolynomialFamily.GradedHilbert.relativePolynomialFamily T J (𝟙 T)
  let e : G ≅ F := ParameterSpecialization.GradedHilbert.relativePolynomialParameterIso M I x
  let lM : F ⟶ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left := Intrinsic.PolynomialAmbient.GradedHilbert.nativePolynomialInclusion M I x ≫
    (prod.snd : Over.mk x.left ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).left
  let lT : G ⟶ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T.left n).left := Intrinsic.PolynomialAmbient.GradedHilbert.nativePolynomialInclusion T J (𝟙 T) ≫
    (prod.snd : Over.mk (𝟙 T.left) ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T.left n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T.left n).left
  let rM : F ⟶ Proj (Graded.Quotient.GradedHilbert.quotientGrading I) := pullback.fst _ _
  let rT : G ⟶ Proj (Graded.Quotient.GradedHilbert.quotientGrading J) := pullback.fst _ _
  let jI : Proj (Graded.Quotient.GradedHilbert.quotientGrading I) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n) := Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I
  let jJ : Proj (Graded.Quotient.GradedHilbert.quotientGrading J) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading Γ(T.left, ⊤) n) := Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J
  let c := ParameterSpecialization.GradedHilbert.parameterProjectiveCoefficient M I x
  let b := Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap x.left n
  let pF : F ⟶ T.left := Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection M I x
  let pG : G ⟶ T.left := Relative.PolynomialFamily.GradedHilbert.relativePolynomialProjection T J (𝟙 T)
  have hm₁ : lM ≫ pullback.fst _ _ = rM ≫ jI := Intrinsic.PolynomialCoordinates.GradedHilbert.nativePolynomialInclusion_coefficient M I x
  have ht₁ : lT ≫ pullback.fst _ _ = rT ≫ jJ := Intrinsic.PolynomialCoordinates.GradedHilbert.nativePolynomialInclusion_coefficient T J (𝟙 T)
  have he₁ : e.hom ≫ rM = rT ≫ c := ParameterSpecialization.GradedHilbert.relativePolynomialParameterIso_coefficient M I x
  have he₂ : e.hom ≫ pF = pG := ParameterSpecialization.GradedHilbert.relativePolynomialParameterIso_projection M I x
  have hc : c ≫ jI = jJ ≫ ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap x.left.appTop.hom :=
    ParameterSpecialization.GradedHilbert.parameterProjectiveCoefficient_inclusion M I x
  have hm₂ : lM ≫ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).hom = pF ≫ x.left := by
    dsimp only [lM]
    rw [Category.assoc, Intrinsic.PolynomialPointComparison.GradedHilbert.nativePolynomialAmbient_second_projection, ← Category.assoc,
      Intrinsic.PolynomialAmbient.GradedHilbert.nativePolynomialInclusion_projection]
  have ht₂ : lT ≫ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T.left n).hom = pG := by
    dsimp only [lT]
    rw [Category.assoc, Intrinsic.PolynomialPointComparison.GradedHilbert.nativePolynomialAmbient_second_projection T (𝟙 T), ← Category.assoc,
      Intrinsic.PolynomialAmbient.GradedHilbert.nativePolynomialInclusion_projection]
    exact Category.comp_id _
  change e.hom ≫ lM = lT ≫ b
  apply pullback.hom_ext
  · calc
      _ = (e.hom ≫ rM) ≫ jI := by rw [Category.assoc, hm₁, Category.assoc]
      _ = (rT ≫ c) ≫ jI := congrArg (fun l => l ≫ jI) he₁
      _ = rT ≫ jJ ≫ ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap x.left.appTop.hom := by rw [Category.assoc, hc]
      _ = _ := by
        rw [Category.assoc, Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_coefficient]
        simpa only [Category.assoc] using
          congrArg (fun l => l ≫ ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap x.left.appTop.hom) ht₁.symm
  · change (e.hom ≫ lM) ≫ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).hom =
      (lT ≫ b) ≫ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver M.left n).hom
    calc
      _ = (e.hom ≫ pF) ≫ x.left := by rw [Category.assoc, hm₂, Category.assoc]
      _ = pG ≫ x.left := congrArg (fun l => l ≫ x.left) he₂
      _ = _ := by
        rw [Category.assoc, Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_projection, ← Category.assoc, ht₂]

theorem relativePolynomialParameterIso_global_inclusion :
    (ParameterSpecialization.GradedHilbert.relativePolynomialParameterIso M I x).hom ≫ Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion M I x =
      Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion T (ParameterSpecialization.GradedHilbert.parameterHomogeneousIdeal M I x) (𝟙 T) := by
  apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd T (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n))).hom_ext
  · change (_ ≫ _) ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T =
      _ ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T
    rw [Category.assoc, Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion_projection, Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion_projection,
      ParameterSpecialization.GradedHilbert.relativePolynomialParameterIso_projection]
  · change (_ ≫ _) ≫ (prod.snd : T ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left =
      _ ≫ (prod.snd : T ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left
    rw [Category.assoc, Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion_projective, Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion_projective]
    have h := congrArg (fun l => l ≫ Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap M.hom n)
      (relativePolynomialParameterIso_native_projective M I x)
    simp only [Category.assoc] at h
    rw [← ProjectiveFunctoriality.GradedHilbert.relativeProjectiveBaseMap_comp, x.w] at h
    exact h

theorem globalPolynomialInclusion_parameter_ker :
    (Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion M I x).ker =
      (Global.PolynomialInclusion.GradedHilbert.globalPolynomialInclusion T (ParameterSpecialization.GradedHilbert.parameterHomogeneousIdeal M I x) (𝟙 T)).ker := by
  rw [← relativePolynomialParameterIso_global_inclusion, Scheme.Hom.ker_comp_of_isIso]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.SpecializationEmbedding.GradedHilbert
