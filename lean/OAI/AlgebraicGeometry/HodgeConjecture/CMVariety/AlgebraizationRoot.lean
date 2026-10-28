import OAI.Geometry.ComplexTorus.RiemannProjectivity.Fin
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusManifold

/-! # Algebraization Root -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraizationRoot.CM.Abelian.Algebraization

noncomputable section

/-! Generic projective period charts, using the actual RiemannProjectivity embedding. -/
open scoped _root_.Topology
open OAI.Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

theorem projective_period_torus (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) :
    Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions.IsProjectiveComplexTorus Φ.space
      Φ.periodIntegerLattice.toAddSubgroup := Φ.projective

/-- The embedding supplied by RiemannProjectivity is differentiable with injective derivative
in every standard affine chart containing its value. -/
theorem projective_period_torus_all_charts
    (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      ∀ (z : Φ.space) (i : Fin (n + 1)),
        Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) →
          DifferentiableAt ℂ
            (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z ∧
          Function.Injective (fderiv ℂ
            (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z) := by
  obtain ⟨n, f, hf, hd⟩ := projective_period_torus Φ
  refine ⟨n, f, hf, ?_⟩
  intro z i hi
  let g : Φ.space → Projectivization ℂ (Fin (n + 1) → ℂ) :=
    fun w => f (QuotientAddGroup.mk w)
  have hg : ContinuousAt g z := (hf.continuous.comp QuotientAddGroup.continuous_mk).continuousAt
  obtain ⟨j, hj, hdj, hinjj⟩ := hd z
  have hdi := Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions.coordinates_differentiableAt_change g hg j i hj hi hdj
  have hinji := Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions.coordinates_injective_fderiv_change g hg j i hj hi hdj hinjj
  exact ⟨Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions.projectiveFinChart_differentiableAt g i hdi,
    Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions.projectiveFinChart_injective_fderiv g hg i hi hdi hinji⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraizationRoot.CM.Abelian.Algebraization
