import OAI.RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme

/-! # Section Evaluation -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.SectionEvaluation

noncomputable section

/-! Actual evaluation of the algebraic hyperplane-frame coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem projective_away_section_value (n : ℕ) (i : Fin (n + 1))
    (a : AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n i →+* ℂ) (r : AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n i)
    (hp : (Spec.map (CommRingCat.ofHom a) ≫ Proj.awayι (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
      (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by omega)) (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :
    Complex.SectionEvaluation.complexSectionValue (Spec.map (CommRingCat.ofHom a) ≫ Proj.awayι (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
      (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by omega)) (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) hp
      ((Proj.awayToSection (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)) r) = a r := by
  let U := AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i
  let e := Proj.basicOpenIsoSpec (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)
    (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by omega)
  change Complex.SectionEvaluation.complexSectionValue ((Spec.map (CommRingCat.ofHom a) ≫ e.inv) ≫ U.ι) U hp
    ((Proj.awayToSection (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)) r) = _
  rw [Complex.SectionEvaluation.complexSectionValue_open]
  have hsection : U.topIso.inv ((Proj.awayToSection (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)) r) =
      e.hom.appTop ((Scheme.ΓSpecIso (.of (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n i))).inv r) := by
    change _ = (Proj.basicOpenToSpec (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)).appTop _
    rw [show (Proj.basicOpenToSpec (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i)).appTop =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i) ≫ U.topIso.inv
      from Proj.basicOpenToSpec_app_top _ _]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rfl
  rw [hsection]
  exact Complex.SectionEvaluation.complexSectionValue_affineIso e a r

theorem projective_affine_localEquation_value (n : ℕ) (i j : Fin (n + 1))
    (z : {j : Fin (n + 1) // j ≠ i} → ℂ)
    (hp : AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint.projectiveAffinePoint n i z (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :
    Complex.SectionEvaluation.complexSectionValue (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint.projectiveAffinePoint n i z) (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) hp
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ) i j) =
      AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i z j := by
  let a : AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n i →+* ℂ := (MvPolynomial.eval z).comp (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i)
  have hpoint : AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint.projectiveAffinePoint n i z = Spec.map (CommRingCat.ofHom a) ≫
      Proj.awayι (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i) (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i) (by omega) := by
    rw [AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint.projectiveAffinePoint, AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap, AlgebraicGeometry.Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec_inv_ι,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  revert hp
  rw [hpoint]
  intro hp
  rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_eq_isLocalizationElem]
  change Complex.SectionEvaluation.complexSectionValue _ _ _ ((Proj.awayToSection (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i))
    (HomogeneousLocalization.Away.isLocalizationElem (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i)
      (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n j))) = _
  rw [projective_away_section_value]
  change MvPolynomial.eval z (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartToPolynomial n i
    (HomogeneousLocalization.Away.isLocalizationElem (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i)
      (AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n j))) = _
  rw [AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint.projectiveChartToPolynomial_isLocalizationElem,
    AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.eval_dehomogenize, MvPolynomial.eval_X]

theorem projective_localEquation_value (n : ℕ) (i j : Fin (n + 1))
    (p : Projectivization ℂ (Fin (n + 1) → ℂ))
    (hi : AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i p) :
    Complex.SectionEvaluation.complexSectionValue (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p).left (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i)
      ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen n i p).mpr hi)
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ) i j) =
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i p j := by
  have hpoint := congrArg (fun q : AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n => q.left)
    (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_on_patch n i ⟨p, hi⟩)
  change (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p).left =
    AlgebraicGeometry.Foundations.Scheme.ProjectiveChartPoint.projectiveAffinePoint n i (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveAffineChart i ⟨p, hi⟩) at hpoint
  have hp := (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen n i p).mpr hi
  change Complex.SectionEvaluation.complexSectionValue _ _ hp _ = _
  revert hp
  rw [hpoint]
  intro hp
  rw [projective_affine_localEquation_value]
  exact congrFun (AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne_affineChart i p hi) j

theorem projective_transitionUnit_value (n : ℕ) (i k : Fin (n + 1))
    (p : Projectivization ℂ (Fin (n + 1) → ℂ))
    (hp : (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) :
    Complex.SectionEvaluation.complexSectionValue (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p).left
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) hp
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := ℂ) i k :
        Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n, AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)) =
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i p k := by
  change Complex.SectionEvaluation.complexSectionValue _ _ hp ((AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n).presheaf.map
    (homOfLE (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k)).op
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := ℂ) i k)) = _
  rw [Complex.SectionEvaluation.complexSectionValue_restrict]
  exact projective_localEquation_value n i k p
    ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen n i p).mp
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k hp))

theorem projective_transitionUnit_zpow_value (n : ℕ) (i k : Fin (n + 1))
    (p : Projectivization ℂ (Fin (n + 1) → ℂ))
    (hp : (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) (d : ℤ) :
    Complex.SectionEvaluation.complexSectionValue (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint n p).left
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) hp
      ((AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := ℂ) i k ^ d :
        Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n, AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)ˣ) :
        Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n, AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)) =
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.coordinates i p k ^ d := by
  rw [Complex.SectionEvaluation.complexRingHom_units_zpow, projective_transitionUnit_value]

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.SectionEvaluation
