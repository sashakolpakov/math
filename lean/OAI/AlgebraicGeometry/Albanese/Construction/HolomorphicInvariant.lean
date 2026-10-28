import OAI.AlgebraicGeometry.AbelianVariety.PureAverage

/-! # Holomorphic Invariant -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.HolomorphicInvariant

noncomputable section

open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

/-- A complex covector, viewed as a complex-valued real one-covector. -/
def holomorphicOneCovector : Module.Dual ℂ E →ₗ[ℂ] (E [⋀^Fin 1]→L[ℝ] ℂ) where
  toFun α := ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)
    (α.toContinuousLinearMap.restrictScalars ℝ)
  map_add' α β := by ext v; rfl
  map_smul' z α := by ext v; rfl

@[simp]
theorem holomorphicOneCovector_apply (α : Module.Dual ℂ E) (v : Fin 1 → E) :
    holomorphicOneCovector E α v = α (v 0) := rfl

theorem holomorphicOneCovector_injective : Function.Injective (holomorphicOneCovector E) := by
  intro α β h
  ext v
  exact congrArg (fun η : E [⋀^Fin 1]→L[ℝ] ℂ => η (fun _ => v)) h

theorem holomorphicOneCovector_pure (α : Module.Dual ℂ E) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 (holomorphicOneCovector E α) := by
  intro z v
  change α ((z : ℂ) • v 0) = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 z * α (v 0)
  simp [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter]

variable (G : Type) [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G] [LieGroup 𝓘(ℂ, E) ∞ G]

/-- Translation extends a complex chart covector at the identity to an
invariant holomorphic one-form on the actual complex Lie group. -/
def holomorphicInvariantOneForm : Module.Dual ℂ E →ₗ[ℂ]
    AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) 1 :=
  (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := E) (G := G) 1).symm.toLinearMap.comp (holomorphicOneCovector E)

omit [LieGroup 𝓘(ℂ, E) ∞ G] in
theorem holomorphicInvariantOneForm_injective :
    Function.Injective (holomorphicInvariantOneForm E G) :=
  (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := E) (G := G) 1).symm.injective.comp
    (holomorphicOneCovector_injective E)

theorem holomorphicInvariantOneForm_pure (α : Module.Dual ℂ E) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E G 1 0 (holomorphicInvariantOneForm E G α).val.val := by
  rw [AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantForm_pure_iff, ← AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv_apply]
  change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0
    ((AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := E) (G := G) 1)
      ((AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := E) (G := G) 1).symm (holomorphicOneCovector E α)))
  rw [LinearEquiv.apply_symm_apply]
  exact holomorphicOneCovector_pure E α

end

end OAI.AlgebraicGeometry.Albanese.Construction.HolomorphicInvariant
