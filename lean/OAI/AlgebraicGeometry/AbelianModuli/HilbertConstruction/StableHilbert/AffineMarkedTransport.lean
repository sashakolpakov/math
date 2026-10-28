import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffinePrescribedPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineLevelTransport

/-! # Affine Marked Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineMarkedTransport

noncomputable section

/-! The actual coordinate isomorphism on a stable Hilbert overlap sends
every prescribed ordered projective point to its counterpart. Therefore
an original marked full-level point has an original marked lift in the
other chart on every Noetherian affine test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    {n m : ℕ} (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ) {f : Spec (.of C) ⟶ Spec (.of R)}

variable (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)

omit [IsNoetherianRing C] in
theorem stableHilbertPrescribedPoint_overlap (z : Fin m) :
    PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H (b ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) z ≫
      (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k b).hom =
    PrescribedPointCriterion.stableHilbertPrescribedPoint R i k D H (b ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) z := by
  have hL : (b ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) ≫
      IntrinsicTransport.stableHilbertChartAmbientMap R i j D H =
      (b ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D H) ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k :=
    (Category.assoc _ _ _).trans ((congrArg (fun q => b ≫ q)
      (IntrinsicTransport.stableHilbertIntersectionLeftMap_toAmbient R i j k D H hH hD)).trans (Category.assoc _ _ _).symm)
  have hR : (b ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) ≫
      IntrinsicTransport.stableHilbertChartAmbientMap R i k D H =
      (b ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D H) ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k :=
    (Category.assoc _ _ _).trans ((congrArg (fun q => b ≫ q)
      (IntrinsicTransport.stableHilbertIntersectionRightMap_toAmbient R i j k D H hH hD)).trans (Category.assoc _ _ _).symm)
  rw [AffinePrescribedPoints.stableHilbertPrescribedPoint_scalar, AffinePrescribedPoints.stableHilbertPrescribedPoint_scalar, hL, hR]
  exact Affine.RelativeCoordinateTransport.affineConfigurationRelativeIso_point _ _
    (StableChartFrames.stablePolynomialIntersection_frameRelated R i j k
      (b ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D H)) ⟨z⟩ _ _

variable (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

theorem stableHilbertFullLevel_overlap_hasPoint
    (h : ∃ u : Over.mk f ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels =
        b ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) :
    ∃ u : Over.mk f ⟶ LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels =
        b ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD := by
  obtain ⟨y, hy, hm⟩ :=
    (PrescribedPointCriterion.StableHilbertFullLevel.hasPoint_iff_hilbert_markedPoints R i j D H hH g Hm Hi N labels _).mp h
  apply (PrescribedPointCriterion.StableHilbertFullLevel.hasPoint_iff_hilbert_markedPoints R i k D H hH g Hm Hi N labels _).mpr
  let yR := AffineLevelTransport.StableHilbertAffineFullLevelTransport.point R i D H hH hD j k b g Hm Hi N y hy
  refine ⟨yR, AffineLevelTransport.StableHilbertAffineFullLevelTransport.point_forget R i D H hH hD j k b g Hm Hi N y hy, ?_⟩
  intro z
  exact (AffineLevelTransport.StableHilbertAffineFullLevelTransport.point_markedPoint R i D H hH hD j k b
    g Hm Hi N y hy (labels z)).trans
      ((congrArg (fun q => q ≫ (AffineProjectiveEmbedding.StableHilbertAffineTransport.coordinateIso R i D H j k b).hom)
        (hm z)).trans (stableHilbertPrescribedPoint_overlap R i j D H hH hD k b z))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineMarkedTransport
