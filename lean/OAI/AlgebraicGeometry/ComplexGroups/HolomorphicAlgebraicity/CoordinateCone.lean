import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts

/-! # Coordinate Cone -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.CoordinateCone.Constructions.Cone

noncomputable section

/-!
# Punctured cone equations for arbitrary finite projective coordinates

This version includes the product coordinate set of the Segre embedding.
-/

open Set Filter
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.propDecidable

def coordinateRatios (i : ι) (v : ι → ℂ) (j : {j : ι // j ≠ i}) : ℂ := v j / v i

theorem differentiableOn_coordinateRatios (i : ι) :
    DifferentiableOn ℂ (coordinateRatios i) {v | v i ≠ 0} := by
  apply differentiableOn_pi.mpr
  intro j
  have hnum : Differentiable ℂ (fun v : ι → ℂ => v j) := differentiable_apply _
  have hden : Differentiable ℂ (fun v : ι → ℂ => v i) := differentiable_apply _
  have hinv : DifferentiableOn ℂ (fun v : ι → ℂ => (v i)⁻¹) {v | v i ≠ 0} :=
    hden.differentiableOn.fun_inv (fun _ h => h)
  simpa only [coordinateRatios, div_eq_mul_inv] using hnum.differentiableOn.fun_mul hinv

omit [Fintype ι] in
theorem coordinateRatios_eq_projectiveChart (i : ι) (v : ι → ℂ) (hv : v ≠ 0) :
    coordinateRatios i v = ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i (Projectivization.mk ℂ v hv) := by
  ext j
  simp only [coordinateRatios, ComplexPoints.Analytic.ProjectiveCharts.projectiveChart_apply, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio_mk]

omit [Fintype ι] in
theorem projectiveChart_image_eq_preimage (i : ι)
    (Z : Set (Projectivization ℂ (ι → ℂ))) :
    ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i '' (Z ∩ (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).source) = (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).symm ⁻¹' Z := by
  rw [inter_comm, (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).image_source_inter_eq', ComplexPoints.Analytic.ProjectiveCharts.projectiveChart_target, univ_inter]

omit [Fintype ι] in
theorem mem_projectiveCone_iff_coordinateRatios
    (Z : Set (Projectivization ℂ (ι → ℂ))) (i : ι) (v : ι → ℂ) (hi : v i ≠ 0) :
    v ∈ ProjectiveCone.Constructions.Cone.projectiveCone Z ↔ (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).symm (coordinateRatios i v) ∈ Z := by
  have hv : v ≠ 0 := by
    intro h
    exact hi (by simp [h])
  rw [ProjectiveCone.Constructions.Cone.mem_projectiveCone_iff Z v hv, coordinateRatios_eq_projectiveChart i v hv]
  rw [(ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).left_inv ((Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i v hv).mpr hi)]

/-- Holomorphic equations in actual standard projective charts pull back to
holomorphic equations everywhere on the affine cone except its vertex. -/
theorem holomorphicZeroSetAt_coordinateCone
    (Z : Set (Projectivization ℂ (ι → ℂ)))
    (hlocal : ∀ i p, p ∈ Z → p ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).source →
      ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt
        (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i '' (Z ∩ (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i).source)) (ComplexPoints.Analytic.ProjectiveCharts.projectiveChart i p))
    (v : ι → ℂ) (hv : v ∈ ProjectiveCone.Constructions.Cone.projectiveCone Z) (hv0 : v ≠ 0) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (ProjectiveCone.Constructions.Cone.projectiveCone Z) v := by
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch (Projectivization.mk ℂ v hv0)
  have hvi : v i ≠ 0 := (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i v hv0).mp hi
  have h := hlocal i _ (hv hv0) hi
  rw [projectiveChart_image_eq_preimage, ← coordinateRatios_eq_projectiveChart] at h
  have hopen : IsOpen {w : ι → ℂ | w i ≠ 0} :=
    isOpen_ne_fun (continuous_apply i) continuous_const
  have hpull := h.preimage hopen hvi (differentiableOn_coordinateRatios i)
  apply hpull.congr
  filter_upwards [hopen.mem_nhds hvi] with w hw
  exact mem_projectiveCone_iff_coordinateRatios Z i w hw

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.CoordinateCone.Constructions.Cone
