import OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Normal Pair Reindex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions

noncomputable section

section

/-!
# DegreeTwo: retain genuine normal coordinates when identifying the support

A proved equality of full support images on the actual normal neighborhood
allows replacement of the support parametrization without changing the
ambient chart, coordinate function, or removed subset of the local pair.
-/

variable {M M' N E F : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
  (g : M' → N) (x' : M') (hpoint : g x' = f x)
  (hrange : ∀ y ∈ P.neighborhood, y ∈ Set.range g ↔ y ∈ Set.range f)

/-- Identify the actual support while retaining its proved ambient
normal coordinates and their geometric neighborhood. -/
def normalPairReplaceSupport : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F g x' where
  radius := P.radius
  radius_pos := P.radius_pos
  ambientChart := P.ambientChart
  product_subset_target := P.product_subset_target
  point_mem_source := by rw [hpoint]; exact P.point_mem_source
  point_coordinates := by rw [hpoint]; exact P.point_coordinates
  range_iff y hy := (hrange y hy).trans (P.range_iff y hy)

@[simp]
theorem normalPairReplaceSupport_ambientChart :
    (normalPairReplaceSupport P g x' hpoint hrange).ambientChart = P.ambientChart := rfl

@[simp]
theorem normalPairReplaceSupport_neighborhood :
    (normalPairReplaceSupport P g x' hpoint hrange).neighborhood = P.neighborhood := rfl

theorem normalPairReplaceSupport_complement :
    (normalPairReplaceSupport P g x' hpoint hrange).relativeComplement = P.relativeComplement := by
  ext y
  exact not_congr (hrange y.val y.property)

@[simp]
theorem normalPairReplaceSupport_coordinate :
    (normalPairReplaceSupport P g x' hpoint hrange).normalCoordinate = P.normalCoordinate := rfl

end

/-!
# DegreeTwo: complex linear reindexing of the normal coordinate

A norm-preserving complex equivalence changes the normal model while
retaining the same actual geometric neighborhood and full support.
-/

open scoped _root_.Manifold ContDiff

variable {M N E F G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
  (e : F ≃L[ℂ] G) (he : ∀ v, ‖e v‖ = ‖v‖)

include he in
private theorem normalReindex_symm_ball (r : ℝ) {z : G} (hz : z ∈ Metric.ball 0 r) :
    e.symm z ∈ Metric.ball 0 r := by
  rw [Metric.mem_ball, dist_zero_right] at hz ⊢
  rw [← he (e.symm z), e.apply_symm_apply]
  exact hz

/-- Change only the normal model by a complex linear isometry. -/
def normalPairReindex : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E G f x := by
  let k := (ContinuousLinearEquiv.refl ℂ E).prodCongr e
  let q := P.ambientChart.transHomeomorph k.toHomeomorph
  have hN : q.symm '' (Metric.ball (0 : E) P.radius ×ˢ Metric.ball (0 : G) P.radius)
      ⊆ P.neighborhood := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨(z.1, e.symm z.2),
      ⟨hz.1, normalReindex_symm_ball e he P.radius hz.2⟩, rfl⟩
  refine {
    radius := P.radius
    radius_pos := P.radius_pos
    ambientChart := q
    product_subset_target := ?_
    point_mem_source := P.point_mem_source
    point_coordinates := ?_
    range_iff := ?_ }
  · intro z hz
    exact P.product_subset_target
      ⟨hz.1, normalReindex_symm_ball e he P.radius hz.2⟩
  · change k (P.ambientChart (f x)) = 0
    rw [P.point_coordinates]
    exact k.map_zero
  · intro y hy
    change y ∈ Set.range f ↔ e (P.ambientChart y).2 = 0
    rw [e.map_eq_zero_iff]
    exact P.range_iff y (hN hy)

theorem normalPairReindex_neighborhood :
    (normalPairReindex P e he).neighborhood = P.neighborhood := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(z.1, e.symm z.2),
      ⟨hz.1, normalReindex_symm_ball e he P.radius hz.2⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(z.1, e z.2), ⟨hz.1, ?_⟩, ?_⟩
    · change e z.2 ∈ Metric.ball 0 P.radius
      simpa only [Metric.mem_ball, dist_zero_right, he] using hz.2
    · change P.ambientChart.symm (z.1, e.symm (e z.2)) = P.ambientChart.symm z
      rw [e.symm_apply_apply]

theorem normalPairReindex_coordinate (y : (normalPairReindex P e he).neighborhood) :
    (normalPairReindex P e he).normalCoordinate y = e (P.ambientChart y.val).2 := rfl

theorem normalPairReindex_mdifferentiable
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [ChartedSpace H N]
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, E × F)) :
    (normalPairReindex P e he).ambientChart.MDifferentiable 𝓘(ℂ, H) 𝓘(ℂ, E × G) := by
  let k := (ContinuousLinearEquiv.refl ℂ E).prodCongr e
  change (P.ambientChart.transHomeomorph k.toHomeomorph).MDifferentiable _ _
  rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
  exact hP.trans
    ⟨(k.contDiff (n := 1)).contMDiff.mdifferentiable one_ne_zero |>.mdifferentiableOn,
      (k.symm.contDiff (n := 1)).contMDiff.mdifferentiable one_ne_zero |>.mdifferentiableOn⟩

/-- The complex line as the canonical single normal coordinate. -/
def planeCoordinates : ℂ ≃L[ℂ] (Fin 1 → ℂ) :=
  (ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)).symm

theorem planeCoordinates_norm (z : ℂ) : ‖planeCoordinates z‖ = ‖z‖ := by
  change ‖(fun _ : Fin 1 => z)‖ = ‖z‖
  exact pi_norm_const _

@[simp]
theorem planeCoordinates_apply (z : ℂ) (i : Fin 1) : planeCoordinates z i = z := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairReindex.Constructions
