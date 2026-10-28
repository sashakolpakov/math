import OAI.RepresentationTheory.Theta.Geometric.Cubical.Arguments
import OAI.RepresentationTheory.Theta.Geometric.Cubical.ComparisonGauges
import OAI.RepresentationTheory.Theta.Geometric.ProductValues

/-! # Gauge Transitions -/

namespace OAI.RepresentationTheory.Theta.Geometric.Cubical.GaugeTransitions

noncomputable section

/-! The common cubical coordinates compare the native tensor frames of
the seven original hyperplane pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hJ : J.IsCubical)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.commonTripleCube hJ).projectiveDimension))
    (e : Φ.triple.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hsurj : Function.Surjective e)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.commonTripleCube hJ).projectiveDimension
        ((F.commonTripleCube hJ).projectiveMap t))
    (fP : Fin 4 → (X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension)))
    (fN : Fin 3 → (X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension)))
    (heP : ∀ k z, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (fP k) (e (QuotientAddGroup.mk z)) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
        (F.projectiveMap (QuotientAddGroup.mk (Φ.cubePositiveArgument k z))))
    (heN : ∀ k z, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (fN k) (e (QuotientAddGroup.mk z)) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension
        (F.projectiveMap (QuotientAddGroup.mk (Φ.cubeNegativeArgument k z))))

include hsurj he

include heP in
theorem cubicalGaugeOpen_le_positive [LocallyOfFiniteType X.hom]
    (i : Fin 4 → Fin (F.projectiveDimension + 1)) (j : Fin 3 → Fin (F.projectiveDimension + 1))
    (k : Fin 4) : ComparisonGauges.cubicalGaugeOpen F hJ f i j ≤
      (fP k).left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) (i k) := by
  apply Complex.PointsDetectSections.opens_le_of_complex_points X
  intro p hp
  obtain ⟨t, rfl⟩ := hsurj p
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
  have H := ((F.cubeLeftSection_ne_zero_iff i z).mp
    ((ComparisonGauges.cubicalGaugeOpen_mem F hJ f e he i j z).mp hp).1) k
  exact (ProductValues.thetaCoordinateOpen_mem_of_point F (fP k) _ _ (heP k z) (i k)).mpr H

include heN in
theorem cubicalGaugeOpen_le_negative [LocallyOfFiniteType X.hom]
    (i : Fin 4 → Fin (F.projectiveDimension + 1)) (j : Fin 3 → Fin (F.projectiveDimension + 1))
    (k : Fin 3) : ComparisonGauges.cubicalGaugeOpen F hJ f i j ≤
      (fN k).left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) (j k) := by
  apply Complex.PointsDetectSections.opens_le_of_complex_points X
  intro p hp
  obtain ⟨t, rfl⟩ := hsurj p
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
  have H := ((F.cubeRightSection_ne_zero_iff hJ j z).mp
    ((ComparisonGauges.cubicalGaugeOpen_mem F hJ f e he i j z).mp hp).2) k
  exact (ProductValues.thetaCoordinateOpen_mem_of_point F (fN k) _ _ (heN k z) (j k)).mpr H

include heP heN in
theorem cubicalGaugeUnit_transition [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (i k : Fin 4 → Fin (F.projectiveDimension + 1))
    (j l : Fin 3 → Fin (F.projectiveDimension + 1)) (W : X.left.Opens)
    (hWij : W ≤ ComparisonGauges.cubicalGaugeOpen F hJ f i j) (hWkl : W ≤ ComparisonGauges.cubicalGaugeOpen F hJ f k l)
    (hWP : ∀ a, W ≤ (fP a).left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) (i a) (k a))
    (hWN : ∀ a, W ≤ (fN a).left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) (j a) (l a)) :
    PowerGaugeCover.restrictRegularUnit hWkl (ComparisonGauges.cubicalGaugeUnit F hJ f k l) *
        ProductFrames.thetaProductTransitionUnit (fun a => (fP a).left) i k W hWP =
      PowerGaugeCover.restrictRegularUnit hWij (ComparisonGauges.cubicalGaugeUnit F hJ f i j) *
        ProductFrames.thetaProductTransitionUnit (fun a => (fN a).left) j l W hWN := by
  apply Units.ext
  apply Complex.PointsDetectSections.complexSectionValue_ext X W
  intro p hp
  obtain ⟨t, rfl⟩ := hsurj p
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hij := (ComparisonGauges.cubicalGaugeOpen_mem F hJ f e he i j z).mp (hWij hp)
  have hkl := (ComparisonGauges.cubicalGaugeOpen_mem F hJ f e he k l z).mp (hWkl hp)
  simp only [Units.val_mul, map_mul, PowerGaugeCover.restrictRegularUnit_value]
  rw [ComparisonGauges.cubicalGaugeUnit_value F hJ f e he, ComparisonGauges.cubicalGaugeUnit_value F hJ f e he,
    ProductValues.thetaProductTransitionUnit_value F fP _ (fun a => Φ.cubePositiveArgument a z) (fun a => heP a z),
    ProductValues.thetaProductTransitionUnit_value F fN _ (fun a => Φ.cubeNegativeArgument a z) (fun a => heN a z),
    ← F.cubeLeftSection_value_prod k z, ← F.cubeLeftSection_value_prod i z,
    ← F.cubeRightSection_value_prod hJ l z, ← F.cubeRightSection_value_prod hJ j z]
  field_simp [hij.1, hij.2, hkl.1]

end

end OAI.RepresentationTheory.Theta.Geometric.Cubical.GaugeTransitions
