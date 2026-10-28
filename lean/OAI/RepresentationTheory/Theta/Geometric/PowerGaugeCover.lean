import OAI.RepresentationTheory.Theta.Geometric.PowerGauge
import OAI.RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections

/-! # Power Gauge Cover -/

namespace OAI.RepresentationTheory.Theta.Geometric.PowerGaugeCover

noncomputable section

section

/-! The algebraic mixed-power gauges are defined on a genuine Zariski
cover. Their opens coincide with the intersections of the two original
theta-coordinate opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor}
  {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

theorem theta_coordinateOpen_mem (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t))
    (i : Fin (F.projectiveDimension + 1)) (z : Φ.space) :
    (e (QuotientAddGroup.mk z)).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i ↔ F.coordinate i z ≠ 0 := by
  change (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e (QuotientAddGroup.mk z))).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
    AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i ↔ _
  rw [he]
  exact (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen F.projectiveDimension i
    (F.projectiveMap (QuotientAddGroup.mk z))).trans (F.projectiveMap_inPatch i z)

variable (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
  (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.commonPower G).projectiveDimension))
  (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
    AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.commonPower G).projectiveDimension ((F.commonPower G).projectiveMap t))

include he

theorem thetaPowerGaugeOpen_mem (hF : 0 < F.degree) (hG : 0 < G.degree)
    (i : Fin (F.projectiveDimension + 1)) (j : Fin (G.projectiveDimension + 1)) (z : Φ.space) :
    (e (QuotientAddGroup.mk z)).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ PowerGauge.thetaPowerGaugeOpen F G f i j ↔
      F.coordinate i z ≠ 0 ∧ G.coordinate j z ≠ 0 := by
  unfold PowerGauge.thetaPowerGaugeOpen
  rw [AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
  change (_ ∈ f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (F.commonPower G).projectiveDimension (F.commonPowerLeftIndex G i) ∧
    _ ∈ f.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (F.commonPower G).projectiveDimension (F.commonPowerRightIndex G j)) ↔ _
  rw [theta_coordinateOpen_mem _ f e he, theta_coordinateOpen_mem _ f e he,
    AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPowerLeftIndex_coordinate, AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family.commonPowerRightIndex_coordinate,
    pow_ne_zero_iff (Nat.ne_of_gt hG), pow_ne_zero_iff (Nat.ne_of_gt hF)]

theorem thetaPowerGaugeOpen_eq [LocallyOfFiniteType X.hom]
    (hsurj : Function.Surjective e) (hF : 0 < F.degree) (hG : 0 < G.degree)
    (fF : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (fG : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (heF : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fF (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t))
    (heG : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fG (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension (G.projectiveMap t))
    (i : Fin (F.projectiveDimension + 1)) (j : Fin (G.projectiveDimension + 1)) :
    PowerGauge.thetaPowerGaugeOpen F G f i j =
      (fF.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i) ⊓
        (fG.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen G.projectiveDimension j) := by
  apply Complex.PointsDetectSections.opens_eq_of_complex_points X
  intro p
  obtain ⟨t, rfl⟩ := hsurj p
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [thetaPowerGaugeOpen_mem F G f e he hF hG]
  change _ ↔ (_ ∈ fF.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen F.projectiveDimension i ∧
    _ ∈ fG.left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen G.projectiveDimension j)
  rw [theta_coordinateOpen_mem F fF e heF, theta_coordinateOpen_mem G fG e heG]

theorem thetaPowerGaugeOpen_cover [LocallyOfFiniteType X.hom]
    (hsurj : Function.Surjective e) (hF : 0 < F.degree) (hG : 0 < G.degree) :
    (⨆ i, ⨆ j, PowerGauge.thetaPowerGaugeOpen F G f i j) = ⊤ := by
  apply top_unique
  apply Complex.PointsDetectSections.opens_le_of_complex_points X
  intro p _
  obtain ⟨t, rfl⟩ := hsurj p
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨s, hs, hsz⟩ := F.nonzero z
  obtain ⟨i, hi⟩ := F.coordinate_surjective s hs
  obtain ⟨t, ht, htz⟩ := G.nonzero z
  obtain ⟨j, hj⟩ := G.coordinate_surjective t ht
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨i, TopologicalSpace.Opens.mem_iSup.mpr ⟨j, ?_⟩⟩
  apply (thetaPowerGaugeOpen_mem F G f e he hF hG i j z).mpr
  simpa only [hi, hj] using And.intro hsz htz

end

/-! The common-power gauges satisfy their transition identity as actual
algebraic units, by equality of regular sections on the reduced model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def restrictRegularUnit {X : Scheme} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) : Γ(X, V)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom u

theorem restrictRegularUnit_value {X : Scheme} {U V : X.Opens} (h : V ≤ U)
    (u : Γ(X, U)ˣ) (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (hp : p (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈ V) :
    Complex.SectionEvaluation.complexSectionValue p V hp (restrictRegularUnit h u : Γ(X, V)) =
      Complex.SectionEvaluation.complexSectionValue p U (h hp) (u : Γ(X, U)) :=
  Complex.SectionEvaluation.complexSectionValue_restrict p U V h hp u

variable {Φ : Torus.Data.CM.ProjectivePeriodData} {J : Φ.AutomorphyFactor} {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

theorem theta_projectiveTransitionUnit_value (F : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t))
    (i k : Fin (F.projectiveDimension + 1)) (z : Φ.space)
    (hx : (e (QuotientAddGroup.mk z)).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ∈
      f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) :
    Complex.SectionEvaluation.complexSectionValue (e (QuotientAddGroup.mk z)).left
      (f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) hx
      (PowerGauge.projectivePullbackTransitionUnit f.left i k :
        Γ(X.left, f.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)) =
      F.coordinate k z / F.coordinate i z := by
  have h := PowerGauge.projectivePullbackTransitionUnit_value f (e (QuotientAddGroup.mk z))
    (F.projectiveMap (QuotientAddGroup.mk z)) (he (QuotientAddGroup.mk z)) i k hx
  rw [F.projectiveMap_coordinates] at h
  exact h

theorem thetaPowerGaugeUnit_transition [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (F G : AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family J) (hF : 0 < F.degree) (hG : 0 < G.degree)
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (F.commonPower G).projectiveDimension))
    (fF : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase F.projectiveDimension))
    (fG : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase G.projectiveDimension))
    (e : Φ.periodTorus → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hsurj : Function.Surjective e)
    (he : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint (F.commonPower G).projectiveDimension ((F.commonPower G).projectiveMap t))
    (heF : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fF (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint F.projectiveDimension (F.projectiveMap t))
    (heG : ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map fG (e t) =
      AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint G.projectiveDimension (G.projectiveMap t))
    (i k : Fin (F.projectiveDimension + 1)) (j l : Fin (G.projectiveDimension + 1))
    (W : X.left.Opens) (hWij : W ≤ PowerGauge.thetaPowerGaugeOpen F G f i j)
    (hWkl : W ≤ PowerGauge.thetaPowerGaugeOpen F G f k l)
    (hWF : W ≤ fF.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
    (hWG : W ≤ fG.left ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) j l) :
    restrictRegularUnit hWkl (PowerGauge.thetaPowerGaugeUnit F G f k l) *
        restrictRegularUnit hWF (PowerGauge.projectivePullbackTransitionUnit fF.left i k) ^ G.degree =
      restrictRegularUnit hWij (PowerGauge.thetaPowerGaugeUnit F G f i j) *
        restrictRegularUnit hWG (PowerGauge.projectivePullbackTransitionUnit fG.left j l) ^ F.degree := by
  apply Units.ext
  apply Complex.PointsDetectSections.complexSectionValue_ext X W
  intro p hp
  obtain ⟨t, rfl⟩ := hsurj p
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hij := (thetaPowerGaugeOpen_mem F G f e he hF hG i j z).mp (hWij hp)
  have hkl := (thetaPowerGaugeOpen_mem F G f e he hF hG k l z).mp (hWkl hp)
  change Complex.SectionEvaluation.complexSectionValue _ W hp
      ((restrictRegularUnit hWkl (PowerGauge.thetaPowerGaugeUnit F G f k l) : Γ(X.left, W)) *
        (restrictRegularUnit hWF (PowerGauge.projectivePullbackTransitionUnit fF.left i k) : Γ(X.left, W)) ^ G.degree) =
    Complex.SectionEvaluation.complexSectionValue _ W hp
      ((restrictRegularUnit hWij (PowerGauge.thetaPowerGaugeUnit F G f i j) : Γ(X.left, W)) *
        (restrictRegularUnit hWG (PowerGauge.projectivePullbackTransitionUnit fG.left j l) : Γ(X.left, W)) ^ F.degree)
  rw [map_mul, map_mul, map_pow, map_pow,
    restrictRegularUnit_value, restrictRegularUnit_value, restrictRegularUnit_value, restrictRegularUnit_value,
    PowerGauge.thetaPowerGaugeUnit_value F G f e he, PowerGauge.thetaPowerGaugeUnit_value F G f e he,
    theta_projectiveTransitionUnit_value F fF e heF, theta_projectiveTransitionUnit_value G fG e heG,
    div_pow, div_pow]
  field_simp [hij.1, hij.2, hkl.1, hkl.2]

end

end OAI.RepresentationTheory.Theta.Geometric.PowerGaugeCover
