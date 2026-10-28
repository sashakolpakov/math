import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.AnalyticFibers
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts

/-! # Cone Charts -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone

noncomputable section

/-!
# Holomorphic equations on the punctured projective cone

The standard affine projective charts pull back to coordinate-ratio maps on
the cone. These maps are holomorphic wherever the denominator is nonzero,
so local holomorphic equations in projective charts give local holomorphic
equations on the cone away from its vertex.
-/

open Set Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

/-- The affine coordinate ratios on the patch where coordinate `i` is nonzero. -/
def dehomogenize {n : ℕ} (i : Fin (n + 1)) (v : Fin (n + 1) → ℂ) (j : Fin n) : ℂ :=
  v (i.succAbove j) / v i

theorem differentiableOn_dehomogenize {n : ℕ} (i : Fin (n + 1)) :
    DifferentiableOn ℂ (dehomogenize i) {v | v i ≠ 0} := by
  apply differentiableOn_pi.mpr
  intro j
  have hnum : Differentiable ℂ (fun v : Fin (n + 1) → ℂ => v (i.succAbove j)) :=
    differentiable_apply _
  have hden : Differentiable ℂ (fun v : Fin (n + 1) → ℂ => v i) :=
    differentiable_apply _
  have hinv : DifferentiableOn ℂ (fun v : Fin (n + 1) → ℂ => (v i)⁻¹)
      {v | v i ≠ 0} := hden.differentiableOn.fun_inv (fun _ h => h)
  simpa only [dehomogenize, div_eq_mul_inv] using hnum.differentiableOn.fun_mul hinv

theorem dehomogenize_eq_projectiveChart {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    dehomogenize i v = ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (Projectivization.mk ℂ v hv) := by
  ext j
  simp only [dehomogenize, ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart_apply, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio_mk]

/-- Membership in the cone is tested by its actual projective affine chart. -/
theorem mem_projectiveCone_iff_dehomogenize {n : ℕ}
    (Z : Set (Projectivization ℂ (Fin (n + 1) → ℂ)))
    (i : Fin (n + 1)) (v : Fin (n + 1) → ℂ) (hvi : v i ≠ 0) :
    v ∈ ProjectiveCone.Constructions.Cone.projectiveCone Z ↔ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm (dehomogenize i v) ∈ Z := by
  have hv : v ≠ 0 := by
    intro h
    apply hvi
    simp [h]
  rw [ProjectiveCone.Constructions.Cone.mem_projectiveCone_iff Z v hv, dehomogenize_eq_projectiveChart i v hv]
  have hp : Projectivization.mk ℂ v hv ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source :=
    (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i v hv).mpr hvi
  rw [(ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).left_inv hp]

/-- Holomorphic equations in one projective patch pull back to genuine local
holomorphic equations on the punctured affine cone. -/
theorem holomorphicZeroSetAt_projectiveCone_of_chart {n : ℕ}
    (Z : Set (Projectivization ℂ (Fin (n + 1) → ℂ)))
    (i : Fin (n + 1)) (v : Fin (n + 1) → ℂ) (hvi : v i ≠ 0)
    (hlocal : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt ((ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm ⁻¹' Z)
      (dehomogenize i v)) : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (ProjectiveCone.Constructions.Cone.projectiveCone Z) v := by
  have hopen : IsOpen {w : Fin (n + 1) → ℂ | w i ≠ 0} :=
    isOpen_ne_fun (continuous_apply i) continuous_const
  have hpull := hlocal.preimage hopen hvi (differentiableOn_dehomogenize i)
  apply hpull.congr
  filter_upwards [hopen.mem_nhds hvi] with w hw
  exact mem_projectiveCone_iff_dehomogenize Z i w hw

/-- Projective local holomorphic equations supply the needed local cone
equations at every nonzero vector. -/
theorem holomorphicZeroSetAt_projectiveCone {n : ℕ}
    (Z : Set (Projectivization ℂ (Fin (n + 1) → ℂ)))
    (hlocal : ∀ i p, p ∈ Z → p ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt ((ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm ⁻¹' Z) (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i p))
    (v : Fin (n + 1) → ℂ) (hv : v ∈ ProjectiveCone.Constructions.Cone.projectiveCone Z) (hv0 : v ≠ 0) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (ProjectiveCone.Constructions.Cone.projectiveCone Z) v := by
  obtain ⟨i, hi⟩ := ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source (Projectivization.mk ℂ v hv0)
  have hvi : v i ≠ 0 := (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i v hv0).mp hi
  apply holomorphicZeroSetAt_projectiveCone_of_chart Z i v hvi
  rw [dehomogenize_eq_projectiveChart i v hv0]
  exact hlocal i _ (hv hv0) hi

/-- The projective center of the coordinate projection. -/
def coordinateProjectionCenter (n : ℕ) : Projectivization ℂ (Fin (n + 1) → ℂ) :=
  Projectivization.mk ℂ (Fin.cons 1 0) (by
    intro h
    have hc := congrFun h 0
    simp only [Fin.cons_zero, Pi.zero_apply, one_ne_zero] at hc)

theorem axis_mem_projectiveCone_iff {n : ℕ}
    (Z : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) :
    (Fin.cons 1 0 : Fin (n + 1) → ℂ) ∈ ProjectiveCone.Constructions.Cone.projectiveCone Z ↔
      coordinateProjectionCenter n ∈ Z :=
  ProjectiveCone.Constructions.Cone.mem_projectiveCone_iff Z _ _

/-- A closed projective set with local holomorphic equations and avoiding
the projection center has a proper affine-cone projection with finite fibers. -/
theorem proper_finite_projectiveCone_projection {n : ℕ}
    (Z : Set (Projectivization ℂ (Fin (n + 1) → ℂ))) (hZ : IsClosed Z)
    (hcenter : coordinateProjectionCenter n ∉ Z)
    (hlocal : ∀ i p, p ∈ Z → p ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt ((ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm ⁻¹' Z) (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i p)) :
    IsProperMap (fun x : ProjectiveCone.Constructions.Cone.projectiveCone Z => Projection.Constructions.Cone.tailProjection n x) ∧
      ∀ y : Fin n → ℂ, {c : ℂ | Fin.cons c y ∈ ProjectiveCone.Constructions.Cone.projectiveCone Z}.Finite := by
  have haxis : (Fin.cons 1 0 : Fin (n + 1) → ℂ) ∉ ProjectiveCone.Constructions.Cone.projectiveCone Z :=
    fun h => hcenter ((axis_mem_projectiveCone_iff Z).mp h)
  have hclosed := ProjectiveCone.Constructions.Cone.isClosed_projectiveCone Z hZ
  have hcone := ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone Z
  refine ⟨Projection.Constructions.Cone.isProperMap_projection hclosed hcone (Projection.Constructions.Cone.tailProjection n)
    (Projection.Constructions.Cone.tailProjection_kernel_trivial hcone haxis), fun y => ?_⟩
  exact AnalyticFibers.Constructions.Cone.finite_coordinateFiber_of_holomorphic hclosed hcone haxis
    (holomorphicZeroSetAt_projectiveCone Z hlocal) y

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone
