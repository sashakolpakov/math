import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.GrassmannChartLoci
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackLocusRecognition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.TargetProperties

/-! # Grassmann Immersion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.GrassmannImmersion

noncomputable section

/-! The generated finite parameter scheme is an actual quasi-compact locally closed subscheme of its single generating-degree Grassmannian, over arbitrary bases. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (n B : ℕ) (r : ℕ → ℕ) (N : ℕ) (hN : N ≤ B)

theorem truncatedGeneratedDegreeProjection_chart_locus
    (a : ULift.{u} (Fin (r N)) → ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) :
    IsImmersion (pullback.snd (DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN)
      (HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S)).left ∧
    QuasiCompact (pullback.snd (DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN)
      (HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S)).left :=
  Affine.PullbackLocusRecognition.pullback_locus_of_affine_lifts (DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN)
    (HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S) (GrassmannChartLoci.generatedGrassmannChartSubfunctor S n B r N a)
    (GrassmannChartLoci.generatedGrassmannChart_immersion S n B r N a)
    (GrassmannChartLoci.generatedGrassmannChart_affine_lift_iff S n B r N a hN)

theorem truncatedGeneratedDegreeProjection_isImmersion :
    IsImmersion (DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN).left :=
  Grassmann.TargetProperties.grassmannTarget_property (DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN) (@IsImmersion)
    (fun a => (truncatedGeneratedDegreeProjection_chart_locus S n B r N hN a).1)

theorem truncatedGeneratedDegreeProjection_quasiCompact :
    QuasiCompact (DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN).left := by
  let : IsZariskiLocalAtTarget (@QuasiCompact.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  exact Grassmann.TargetProperties.grassmannTarget_property (DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN) (@QuasiCompact)
    (fun a => (truncatedGeneratedDegreeProjection_chart_locus S n B r N hN a).2)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.GrassmannImmersion
