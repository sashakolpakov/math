import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.PolarizedCoefficientChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.NormalizedCoefficientSquare
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.RingMapBaseChange

/-! # Torsion Coefficient Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.TorsionCoefficientCoordinates

noncomputable section

/-! Normalized coordinates of the actual auxiliary torsion sections
survive coefficient extension in the saturated homogeneous
presentation. Equality is checked in the actual projective pullback. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R C : Type u} [CommRing R] [IsNoetherianRing R] [CommRing C]
variable {g N n r : ℕ} {δ : Fin g → ℕ} {P : Polynomial ℚ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R r P)
variable (e : A.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
variable (level : A.abelian.FullLevel n) (φ : R →+* C)

omit [NeZero n] in
theorem embeddedTorsionCoefficientChange_coordinates
    (c : Multiplicative (Fin (2 * g) → ZMod n)) (v : Fin (r + 1) → R)
    (i : Fin (r + 1)) (hi : v i = 1)
    (hv : (A.abelian.fullLevelGlobalSection level c ≫ e.hom.left) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R v i hi) :
    ((A.pullback (Spec.map (CommRingCat.ofHom φ))).abelian.fullLevelGlobalSection
        (level.pullback (Spec.map (CommRingCat.ofHom φ))) c ≫
      (PolarizedCoefficientChange.embeddedCoefficientChangeIso A I e φ).hom.left) ≫
        HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (I.coefficientChange φ).ideal =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of C) C (fun j => φ (v j)) i
        ((congrArg φ hi).trans φ.map_one) := by
  let f := Spec.map (CommRingCat.ofHom φ)
  let B := A.pullback f
  let s := B.abelian.fullLevelGlobalSection (level.pullback f) c
  let a := (PolarizedCoefficientChange.embeddedCoefficientChangeIso A I e φ).hom.left
  let J := I.coefficientChange φ
  let π := pullback.fst A.abelian.scheme.hom f
  have hy : s ≫ π = f ≫ A.abelian.fullLevelGlobalSection level c :=
    A.abelian.fullLevelGlobalSection_pullback level f c
  apply (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback (CommRingCat.ofHom φ) r).hom_ext
  · change ((s ≫ a) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J.ideal) ≫
        Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) r = _
    calc
      _ = s ≫ (a ≫ I.coefficientChangeMorphism φ) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal := by
        dsimp only [J]
        simp only [Category.assoc, I.coefficientChangeMorphism_ambient φ]
      _ = s ≫ (π ≫ e.hom.left) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal := by
        rw [PolarizedCoefficientChange.embeddedCoefficientChangeIso_projection]
      _ = f ≫ ((A.abelian.fullLevelGlobalSection level c ≫ e.hom.left) ≫
          HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal) := by
        simp only [Category.assoc]
        rw [← Category.assoc s π, hy]
        simp only [Category.assoc]
      _ = f ≫ AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R v i hi := by rw [hv]
      _ = _ := Affine.NormalizedCoefficientSquare.affineProjectiveCoordinateMap_coefficientSquare φ v i hi
  · change ((s ≫ a) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J.ideal) ≫ (Projective.ProjectivePresentations.affineProjectiveSpace C r).hom = _
    have hs : s ≫ B.abelian.scheme.hom = 𝟙 _ := B.abelian.fullLevelGlobalSection_comp _ c
    have ha : a ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J.ideal) = B.abelian.scheme.hom :=
      (PolarizedCoefficientChange.embeddedCoefficientChangeIso A I e φ).hom.w
    rw [Category.assoc, Projective.CoefficientPullback.projectiveQuotientInclusion_standard_over,
      Category.assoc, ha, hs]
    simpa using (AffineProjective.CoordinatesOver.affineProjectiveCoordinateMap_over (.of C) C (fun j => φ (v j)) i
      ((congrArg φ hi).trans φ.map_one)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.TorsionCoefficientCoordinates
