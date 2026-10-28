import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.AmbientTransport
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Tangent Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentCoordinates.Constructions

noncomputable section

/-! Changing the tangent coordinates by an actual complex linear isometry
preserves the normal coordinate and its genuine normalized relative class. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E F G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
  (e : E ≃L[ℂ] G) (he : ∀ v, ‖e v‖ = ‖v‖)

include he in
theorem tangentCoordinates_symm_ball (r : ℝ) {z : G} (hz : z ∈ Metric.ball 0 r) :
    e.symm z ∈ Metric.ball 0 r := by
  rw [Metric.mem_ball, dist_zero_right] at hz ⊢
  rw [← he (e.symm z), e.apply_symm_apply]
  exact hz

def tangentCoordinateNormalPair : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair G F f x := by
  let k := e.prodCongr (ContinuousLinearEquiv.refl ℂ F)
  let q := P.ambientChart.transHomeomorph k.toHomeomorph
  have hN : q.symm '' (Metric.ball (0 : G) P.radius ×ˢ Metric.ball (0 : F) P.radius) ⊆ P.neighborhood := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨(e.symm z.1, z.2), ⟨tangentCoordinates_symm_ball e he P.radius hz.1, hz.2⟩, rfl⟩
  refine { radius := P.radius
           radius_pos := P.radius_pos
           ambientChart := q
           product_subset_target := ?_
           point_mem_source := P.point_mem_source
           point_coordinates := ?_
           range_iff := ?_ }
  · intro z hz
    exact P.product_subset_target ⟨tangentCoordinates_symm_ball e he P.radius hz.1, hz.2⟩
  · change k (P.ambientChart (f x)) = 0
    rw [P.point_coordinates]
    exact k.map_zero
  · intro y hy
    exact P.range_iff y (hN hy)

theorem tangentCoordinateNormalPair_neighborhood :
    (tangentCoordinateNormalPair P e he).neighborhood = P.neighborhood := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(e.symm z.1, z.2), ⟨tangentCoordinates_symm_ball e he P.radius hz.1, hz.2⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(e z.1, z.2), ⟨?_, hz.2⟩, ?_⟩
    · change e z.1 ∈ Metric.ball 0 P.radius
      simpa only [Metric.mem_ball, dist_zero_right, he] using hz.1
    · change P.ambientChart.symm (e.symm (e z.1), z.2) = P.ambientChart.symm z
      rw [e.symm_apply_apply]

def tangentCoordinateNeighborhoodMap : TopCat.of (tangentCoordinateNormalPair P e he).neighborhood ⟶
    TopCat.of P.neighborhood := by
  let g : (tangentCoordinateNormalPair P e he).neighborhood → P.neighborhood := fun z =>
    ⟨z.val, (Set.ext_iff.mp (tangentCoordinateNormalPair_neighborhood P e he) z.val).mp z.property⟩
  refine TopCat.ofHom ⟨g, ?_⟩
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem tangentCoordinateNeighborhoodMap_normalCoordinate :
    tangentCoordinateNeighborhoodMap P e he ≫ P.normalCoordinate =
      (tangentCoordinateNormalPair P e he).normalCoordinate := rfl

theorem tangentCoordinateNeighborhoodMap_mapsTo :
    Set.MapsTo (tangentCoordinateNeighborhoodMap P e he)
      (tangentCoordinateNormalPair P e he).relativeComplement P.relativeComplement := fun _ hz => hz

theorem tangentCoordinateNormalPair_mdifferentiable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [ChartedSpace H N]
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, E × F)) :
    (tangentCoordinateNormalPair P e he).ambientChart.MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, G × F) := by
  let k := e.prodCongr (ContinuousLinearEquiv.refl ℂ F)
  change (P.ambientChart.transHomeomorph k.toHomeomorph).MDifferentiable _ _
  rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
  exact hP.trans
    ⟨(k.contDiff (n := 1)).contMDiff.mdifferentiable one_ne_zero |>.mdifferentiableOn,
      (k.symm.contDiff (n := 1)).contMDiff.mdifferentiable one_ne_zero |>.mdifferentiableOn⟩

variable [NormedSpace ℝ E] [NormedSpace ℝ G]

theorem tangentCoordinateNormalClass {p : ℕ} (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (tangentCoordinateNeighborhoodMap Q e he)
      (tangentCoordinateNeighborhoodMap_mapsTo Q e he) (2 * p) Q.rationalClassFin =
        (tangentCoordinateNormalPair Q e he).rationalClassFin := by
  rw [Q.rationalClassFin_eq_normalPullback, (tangentCoordinateNormalPair Q e he).rationalClassFin_eq_normalPullback]
  simp only [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap]
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (tangentCoordinateNeighborhoodMap Q e he) Q.normalCoordinate
      (tangentCoordinateNeighborhoodMap_mapsTo Q e he) Q.normalCoordinate_mapsTo (2 * p))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  simp only [tangentCoordinateNeighborhoodMap_normalCoordinate, ConcreteCategory.comp_apply] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentCoordinates.Constructions
