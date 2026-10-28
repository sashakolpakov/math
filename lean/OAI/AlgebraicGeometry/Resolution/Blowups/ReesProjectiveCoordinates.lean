import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.BlowupProjectiveProduct
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Functor

/-! # Rees Projective Coordinates -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ReesProjectiveCoordinates.Construction

noncomputable section

/-! Explicit complex projective coordinates on an affine Rees blowup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {m : ℕ}
variable (I : Ideal R) (κ : ℂ →+* R) (a : Fin (m + 1) → I)

/-- The complex polynomial map sending each coordinate to its Rees generator. -/
def reesProjectivePolynomialMap : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ ReesGrading.Construction.reesGrade I :=
  (ReesPresentation.Construction.reesPolynomialPresentation I a).comp (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap κ)

@[simp]
theorem reesProjectivePolynomialMap_X (j : Fin (m + 1)) :
    reesProjectivePolynomialMap I κ a (MvPolynomial.X j) = Blowup.Charts.Construction.reesGenerator I (a j) := by
  change MvPolynomial.aeval (fun i => Blowup.Charts.Construction.reesGenerator I (a i))
    (MvPolynomial.map κ (MvPolynomial.X j)) = _
  rw [MvPolynomial.map_X, MvPolynomial.aeval_X]

@[simp]
theorem reesProjectivePolynomialMap_C (c : ℂ) :
    reesProjectivePolynomialMap I κ a (MvPolynomial.C c) =
      algebraMap R (reesAlgebra I) (κ c) := by
  change MvPolynomial.aeval (fun i => Blowup.Charts.Construction.reesGenerator I (a i))
    (MvPolynomial.map κ (MvPolynomial.C c)) = _
  rw [MvPolynomial.map_C, MvPolynomial.aeval_C]

theorem reesProjectivePolynomialMap_eq_eval :
    (reesProjectivePolynomialMap I κ a).toRingHom =
      MvPolynomial.eval₂Hom ((algebraMap R (reesAlgebra I)).comp κ)
        (fun j => Blowup.Charts.Construction.reesGenerator I (a j)) := by
  ext <;> simp

variable (hgen : Submodule.span R (Set.range a) = ⊤)

include hgen in
theorem reesProjectivePolynomialMap_irrelevant :
    HomogeneousIdeal.irrelevant (ReesGrading.Construction.reesGrade I) ≤
      (HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading m)).map
        (reesProjectivePolynomialMap I κ a) := by
  let : Algebra ℂ R := κ.toAlgebra
  exact HomogeneousIdeal.irrelevant_le_map_comp
    PolynomialProjectiveBaseChange.Construction.polynomial_coefficient_irrelevant_le_map
    (ProjectiveClosedImmersion.Construction.gradedMap_irrelevant_le_of_surjective (ReesPresentation.Construction.reesPolynomialPresentation I a)
      (ReesPresentation.Construction.reesPolynomialPresentation_surjective I a hgen))

/-- The chosen generators define an actual map from the blowup to complex projective space. -/
def reesProjectiveCoordinateMap : ReesGrading.Construction.affineBlowup I ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m :=
  Proj.map (reesProjectivePolynomialMap I κ a)
    (reesProjectivePolynomialMap_irrelevant I κ a hgen)

theorem reesProjectiveCoordinateMap_over :
    reesProjectiveCoordinateMap I κ a hgen ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m =
      ReesGrading.Construction.affineBlowupToSpec I ≫ Spec.map (CommRingCat.ofHom κ) := by
  unfold reesProjectiveCoordinateMap Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase ReesGrading.Construction.affineBlowupToSpec
  rw [← Category.assoc, Blowup.BaseOpen.Construction.projMap_toSpecZero, Category.assoc, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  apply Subtype.ext
  exact reesProjectivePolynomialMap_C I κ a c

theorem reesProjectiveCoordinateMap_eq_product_fst [Algebra ℂ R]
    (hκ : κ = algebraMap ℂ R) :
    reesProjectiveCoordinateMap I κ a hgen =
      Affine.BlowupProjectiveProduct.Construction.affineBlowupProjectiveProductEmbedding I a hgen ≫ pullback.fst _ _ := by
  subst κ
  unfold Affine.BlowupProjectiveProduct.Construction.affineBlowupProjectiveProductEmbedding
  rw [Category.assoc]
  change _ = ReesPresentation.Construction.affineBlowupProjectiveEmbedding I a hgen ≫
    ((PolynomialProjectiveBaseChange.Construction.polynomialProjective_isPullback (R := ℂ) (S := R) (n := m)).isoPullback.hom ≫
      pullback.fst _ _)
  rw [IsPullback.isoPullback_hom_fst]
  exact Proj.map_comp _ _ _ _

/-- Pairing the coordinate map with the blowup projection is a closed immersion. -/
theorem reesProjectiveCoordinateMap_pair_isClosedImmersion :
    IsClosedImmersion (pullback.lift (reesProjectiveCoordinateMap I κ a hgen)
      (ReesGrading.Construction.affineBlowupToSpec I) (reesProjectiveCoordinateMap_over I κ a hgen)) := by
  let : Algebra ℂ R := κ.toAlgebra
  have he : pullback.lift (reesProjectiveCoordinateMap I κ a hgen)
      (ReesGrading.Construction.affineBlowupToSpec I) (reesProjectiveCoordinateMap_over I κ a hgen) =
        Affine.BlowupProjectiveProduct.Construction.affineBlowupProjectiveProductEmbedding I a hgen := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact reesProjectiveCoordinateMap_eq_product_fst I κ a hgen rfl
    · rw [pullback.lift_snd]
      exact (Affine.BlowupProjectiveProduct.Construction.affineBlowupProjectiveProductEmbedding_over I a hgen).symm
  rw [he]
  infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ReesProjectiveCoordinates.Construction
