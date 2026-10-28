import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ExteriorMetricLowDegree
import OAI.Analysis.DifferentialForms.Manifold.Bidegree

/-! # Pure One Covector -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PureOneCovector.CM.Construction

noncomputable section

/-! Actual covectors of type (1,0), bundled as continuous complex-linear maps. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def holomorphicOneCovector (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 a) : E →L[ℂ] ℂ :=
  let D := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).symm a
  { toFun := D
    map_add' := D.map_add
    map_smul' := fun z u => by
      by_cases hz : z = 0
      · simp [hz]
      · have h := ha (Units.mk0 z hz) (fun _ => u)
        change D (z • u) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 (Units.mk0 z hz) * D u at h
        simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Units.val_mk0, pow_one, pow_zero, mul_one, smul_eq_mul,
          RingHom.id_apply] using h
    cont := D.continuous }

omit [IsScalarTower ℝ ℂ E] in
theorem holomorphicOneCovector_apply (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 a) (u : E) :
    holomorphicOneCovector a ha u = a (fun _ => u) := rfl

theorem holomorphicOneCovector_reconstruct (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 a) :
    Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (holomorphicOneCovector a ha) = a := by
  ext v
  change a (fun _ => v 0) = a v
  congr 1
  exact funext (fun i => congrArg v (Subsingleton.elim 0 i))

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem holomorphicOneCovector_restrict (a : Analysis.DifferentialForms.Manifold.Basic.FormValue F 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree F 1 0 a) :
    (holomorphicOneCovector a ha).toLinearMap.restrictScalars ℝ = ExteriorMetricLowDegree.CM.Construction.oneFormCovector a := by
  ext u
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PureOneCovector.CM.Construction
