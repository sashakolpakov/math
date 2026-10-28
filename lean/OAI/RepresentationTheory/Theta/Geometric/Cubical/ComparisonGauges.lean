import OAI.RepresentationTheory.Theta.Geometric.Cubical.CoordinateNonvanishing
import OAI.RepresentationTheory.Theta.Geometric.PowerGaugeCover

/-! # Comparison Gauges -/

namespace OAI.RepresentationTheory.Theta.Geometric.Cubical.ComparisonGauges

noncomputable section

/-! The common cubical embedding supplies regular units equal to the
ratios of the two products of original theta sections. Their actual
overlap opens cover the triple-product model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
    (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hJ : J.IsCubical) {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.commonTripleCube hJ).projectiveDimension))

def cubicalGaugeOpen (i : Fin 4 → Fin (F.projectiveDimension + 1))
    (j : Fin 3 → Fin (F.projectiveDimension + 1)) : X.left.Opens :=
  f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) (F.cubeLeftIndex hJ i) (F.cubeRightIndex hJ j)

def cubicalGaugeUnit (i : Fin 4 → Fin (F.projectiveDimension + 1))
    (j : Fin 3 → Fin (F.projectiveDimension + 1)) : Γ(X.left, cubicalGaugeOpen F hJ f i j)ˣ :=
  PowerGauge.projectivePullbackTransitionUnit f.left (F.cubeLeftIndex hJ i) (F.cubeRightIndex hJ j)

variable (e : Φ.triple.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.commonTripleCube hJ).projectiveDimension
        ((F.commonTripleCube hJ).projectiveMap t))

include he

theorem cubicalGaugeUnit_value (i : Fin 4 → Fin (F.projectiveDimension + 1))
    (j : Fin 3 → Fin (F.projectiveDimension + 1)) (z : Φ.triple.space)
    (hx : (e (QuotientAddGroup.mk z)).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ cubicalGaugeOpen F hJ f i j) :
    Complex.SectionEvaluation.complexSectionValue (e (QuotientAddGroup.mk z)).left (cubicalGaugeOpen F hJ f i j) hx
      (cubicalGaugeUnit F hJ f i j : Γ(X.left, cubicalGaugeOpen F hJ f i j)) =
      F.cubeRightSection hJ j z / F.cubeLeftSection i z := by
  have H := PowerGauge.projectivePullbackTransitionUnit_value f (e (QuotientAddGroup.mk z))
    ((F.commonTripleCube hJ).projectiveMap (QuotientAddGroup.mk z)) (he (QuotientAddGroup.mk z))
    (F.cubeLeftIndex hJ i) (F.cubeRightIndex hJ j) hx
  rw [(F.commonTripleCube hJ).projectiveMap_coordinates] at H
  change _ = (F.commonTripleCube hJ).coordinate (F.cubeRightIndex hJ j) z /
    (F.commonTripleCube hJ).coordinate (F.cubeLeftIndex hJ i) z at H
  exact H.trans (by rw [AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeLeftIndex_coordinate, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightIndex_coordinate])

theorem cubicalGaugeOpen_mem (i : Fin 4 → Fin (F.projectiveDimension + 1))
    (j : Fin 3 → Fin (F.projectiveDimension + 1)) (z : Φ.triple.space) :
    (e (QuotientAddGroup.mk z)).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ cubicalGaugeOpen F hJ f i j ↔
      F.cubeLeftSection i z ≠ 0 ∧ F.cubeRightSection hJ j z ≠ 0 := by
  unfold cubicalGaugeOpen
  rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
  change (_ ∈ f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (F.commonTripleCube hJ).projectiveDimension (F.cubeLeftIndex hJ i) ∧
    _ ∈ f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (F.commonTripleCube hJ).projectiveDimension (F.cubeRightIndex hJ j)) ↔ _
  rw [PowerGaugeCover.theta_coordinateOpen_mem _ f e he, PowerGaugeCover.theta_coordinateOpen_mem _ f e he,
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeLeftIndex_coordinate, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.cubeRightIndex_coordinate]

theorem cubicalGaugeOpen_cover [LocallyOfFiniteType X.hom] (hsurj : Function.Surjective e) :
    (⨆ i, ⨆ j, cubicalGaugeOpen F hJ f i j) = ⊤ := by
  apply top_unique
  apply Complex.PointsDetectSections.opens_le_of_complex_points X
  intro p _
  obtain ⟨t, rfl⟩ := hsurj p
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨i, hi⟩ := F.cubeLeftSection_nonzero z
  obtain ⟨j, hj⟩ := F.cubeRightSection_nonzero hJ z
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i,
    TopologicalSpace.Opens.mem_iSup.mpr ⟨j, (cubicalGaugeOpen_mem F hJ f e he i j z).mpr ⟨hi, hj⟩⟩⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Cubical.ComparisonGauges
