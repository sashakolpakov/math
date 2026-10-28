import OAI.RepresentationTheory.Theta.Geometric.TransformedGauge
import OAI.RepresentationTheory.Theta.Geometric.PowerGaugeCover

/-! # Transformed Gauge Cover -/

namespace OAI.RepresentationTheory.Theta.Geometric.TransformedGaugeCover

noncomputable section

/-! The original/transformed coordinate ratios live on the actual
intersections of the corresponding projective charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

theorem translatedTheta_coordinateOpen_mem (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (a : Φ.space)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap (t + QuotientAddGroup.mk a)))
    (i : Fin (F.projectiveDimension + 1)) (z : Φ.space) :
    (e (QuotientAddGroup.mk z)).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i ↔ F.coordinate i (z + a) ≠ 0 := by
  change (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e (QuotientAddGroup.mk z))).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
    AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i ↔ _
  rw [he]
  have hadd : (QuotientAddGroup.mk z : Φ.periodTorus) + QuotientAddGroup.mk a = QuotientAddGroup.mk (z + a) := rfl
  rw [hadd]
  exact (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen F.projectiveDimension i
    (F.projectiveMap (QuotientAddGroup.mk (z + a)))).trans (F.projectiveMap_inPatch i (z + a))

theorem transformedThetaGaugeOpen_mem (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (T : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree → AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.withSectionMap T).projectiveDimension))
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.withSectionMap T).projectiveDimension ((F.withSectionMap T).projectiveMap t))
    (i j : Fin (F.projectiveDimension + 1)) (z : Φ.space) :
    (e (QuotientAddGroup.mk z)).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ TransformedGauge.transformedThetaGaugeOpen F T f i j ↔
      F.coordinate i z ≠ 0 ∧ T (F.coordinate j) z ≠ 0 := by
  unfold TransformedGauge.transformedThetaGaugeOpen
  rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
  change (_ ∈ f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (F.withSectionMap T).projectiveDimension (F.withSectionMapOriginalIndex T i) ∧
    _ ∈ f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (F.withSectionMap T).projectiveDimension (F.withSectionMapTransformedIndex T j)) ↔ _
  rw [PowerGaugeCover.theta_coordinateOpen_mem _ f e he, PowerGaugeCover.theta_coordinateOpen_mem _ f e he,
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.withSectionMapOriginalIndex_coordinate, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.withSectionMapTransformedIndex_coordinate]

theorem transformedThetaGaugeOpen_eq [LocallyOfFiniteType X.hom]
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (T : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree → AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) (a : Φ.space) (c : Φ.space → ℂ)
    (hc : ∀ z, c z ≠ 0) (hT : ∀ i z, T (F.coordinate i) z = c z ^ F.degree * F.coordinate i (z + a))
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.withSectionMap T).projectiveDimension))
    (f₀ f₁ : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hsurj : Function.Surjective e)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.withSectionMap T).projectiveDimension ((F.withSectionMap T).projectiveMap t))
    (he₀ : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f₀ (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t))
    (he₁ : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f₁ (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap (t + QuotientAddGroup.mk a)))
    (i j : Fin (F.projectiveDimension + 1)) :
    TransformedGauge.transformedThetaGaugeOpen F T f i j =
      (f₀.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i) ⊓
        (f₁.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension j) := by
  apply Complex.PointsDetectSections.opens_eq_of_complex_points X
  intro p
  obtain ⟨t, rfl⟩ := hsurj p
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [transformedThetaGaugeOpen_mem F T f e he]
  change _ ↔ (_ ∈ f₀.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i ∧
    _ ∈ f₁.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension j)
  rw [PowerGaugeCover.theta_coordinateOpen_mem F f₀ e he₀, translatedTheta_coordinateOpen_mem F a f₁ e he₁, hT]
  simp only [mul_ne_zero_iff]
  exact and_congr_right (fun _ => and_iff_right (pow_ne_zero F.degree (hc z)))

theorem transformedThetaGaugeOpen_cover [LocallyOfFiniteType X.hom]
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (T : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree → AutomorphicFamilies.CM.Torus.AutomorphicTheta.Section J F.degree) (a : Φ.space) (c : Φ.space → ℂ)
    (hc : ∀ z, c z ≠ 0) (hT : ∀ i z, T (F.coordinate i) z = c z ^ F.degree * F.coordinate i (z + a))
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.withSectionMap T).projectiveDimension))
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hsurj : Function.Surjective e)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.withSectionMap T).projectiveDimension ((F.withSectionMap T).projectiveMap t)) :
    (⨆ i, ⨆ j, TransformedGauge.transformedThetaGaugeOpen F T f i j) = ⊤ := by
  apply top_unique
  apply Complex.PointsDetectSections.opens_le_of_complex_points X
  intro p _
  obtain ⟨t, rfl⟩ := hsurj p
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨s, hs, hsz⟩ := F.nonzero z
  obtain ⟨i, hi⟩ := F.coordinate_surjective s hs
  obtain ⟨s', hs', hs'z⟩ := F.nonzero (z + a)
  obtain ⟨j, hj⟩ := F.coordinate_surjective s' hs'
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨i, TopologicalSpace.Opens.mem_iSup.mpr ⟨j, ?_⟩⟩
  apply (transformedThetaGaugeOpen_mem F T f e he i j z).mpr
  constructor
  · exact hi.symm ▸ hsz
  · rw [hT, hj]
    exact mul_ne_zero (pow_ne_zero _ (hc z)) hs'z

end

end OAI.RepresentationTheory.Theta.Geometric.TransformedGaugeCover
