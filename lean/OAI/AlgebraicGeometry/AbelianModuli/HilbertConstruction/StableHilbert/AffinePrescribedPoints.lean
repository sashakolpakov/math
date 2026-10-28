import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PrescribedPointCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ScalarCoordinateCoverage

/-! # Affine Prescribed Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffinePrescribedPoints

noncomputable section

/-! The prescribed marks of a stable Hilbert chart are the actual
affine projective points of its normalized coefficient vectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem affinePoint_congr
    {C : Type u} [CommRing C] {n : ℕ} {v w : Fin (n + 1) → C}
    (h : v = w) (i : Fin (n + 1)) (hv : v i = 1) (hw : w i = 1) :
    AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of C) C v i hv =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of C) C w i hw := by
  cases h
  rfl

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Type u} [CommRing C] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ) {f : Spec (.of C) ⟶ Spec (.of R)}

omit [IsNoetherianRing R] in
theorem stableChartRawCoordinates_cover
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) (z : Fin m) :
    ∀ p : Spec (.of C), ∃ t, p ∈ (Spec (.of C)).basicOpen
      ((Scheme.ΓSpecIso (.of C)).inv (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) x ⟨z⟩ t)) := by
  intro p
  refine ⟨j.coordinate z, ?_⟩
  rw [Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected, map_one]
  exact ((Spec (.of C)).basicOpen_of_isUnit
    (isUnit_one : IsUnit (1 : Γ(Spec (.of C), ⊤)))).symm ▸ trivial

omit [IsNoetherianRing R] in
theorem stableHilbertPrescribedPoint_scalar
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) (z : Fin m) :
    PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint
        (fun t => (Scheme.ΓSpecIso (.of C)).inv
          (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C)
            (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H) ⟨z⟩ t))
        (stableChartRawCoordinates_cover R i j
          (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H) z) := by
  let q : Spec (.of C) ⟶ Balanced.FrameChartProjectivePoints.balancedFrameChartScheme R i j.exponent j.balanced :=
    (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H).left
  change Projective.SectionBaseChange.projectiveSectionBaseChange
    (Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate
      j.exponent j.complement j.balanced j.complete z) q = _
  refine (Balanced.FramePointBaseChange.balancedFrameChartUniversalPoint_baseChange R i j.frame j.additional
    j.coordinate j.exponent j.complement j.balanced j.complete q z).trans ?_
  apply Balanced.FrameChartProjectivePoints.scalarCoordinateProjectivePoint_congr
  funext t
  exact ((Scheme.ΓSpecIso (.of C)).commRingCatIsoToRingEquiv.symm_apply_apply _).symm

omit [IsNoetherianRing R] in
theorem stableHilbertPrescribedPoint_affine
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) (z : Fin m) :
    (PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z).left =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of C) C
        (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C)
          (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H) ⟨z⟩)
        (j.coordinate z)
        (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i j (.of C)
          (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H) ⟨z⟩) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n := by
  let w := Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C)
    (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H) ⟨z⟩
  let v := fun t => (Scheme.ΓSpecIso (.of C)).inv (w t)
  have hv := stableChartRawCoordinates_cover R i j
    (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H) z
  have hi : v (j.coordinate z) = 1 := by
    exact (congrArg (Scheme.ΓSpecIso (.of C)).inv
      (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i j (.of C)
        (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H) ⟨z⟩)).trans (map_one _)
  have hs := ScalarCoordinateCoverage.StableHilbertCoverage.scalarCoordinateProjectivePoint_affine
    C v hv (j.coordinate z) hi
  have hw : (fun t => (Scheme.ΓSpecIso (.of C)).hom (v t)) = w := by
    funext t
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of C)).inv_hom_id (w t)
  have hscalar := congrArg Over.Hom.left (stableHilbertPrescribedPoint_scalar R i j D H c z)
  have hpoint := affinePoint_congr hw (j.coordinate z)
    ((congrArg (Scheme.ΓSpecIso (.of C)).hom hi).trans (map_one _))
    (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i j (.of C)
      (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H) ⟨z⟩)
  exact hscalar.trans (hs.trans (congrArg
    (fun a => a ≫ AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n) hpoint))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffinePrescribedPoints
