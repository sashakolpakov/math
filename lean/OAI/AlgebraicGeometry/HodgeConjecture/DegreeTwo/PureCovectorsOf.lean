import OAI.Analysis.DifferentialForms.Manifold.Bidegree
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Pure Covectors Of -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PureCovectorsOf.Constructions.PureCovectors

noncomputable section

/-! A pure (1,0) real covector is precisely a complex-linear functional. -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- The pure-type character gives complex homogeneity of the actual covector. -/
def complexLinearOfPure (α : E [⋀^Fin 1]→L[ℝ] ℂ) (hα : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 α) : E →L[ℂ] ℂ := by
  let D := (ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1)).symm α
  have hD (v : E) : D v = α (fun _ => v) := rfl
  refine ⟨⟨⟨D, D.map_add⟩, ?_⟩, D.continuous⟩
  intro z v
  by_cases hz : z = 0
  · simp [hz]
  · have h := hα (Units.mk0 z hz) (fun _ => v)
    change D (z • v) = z • D v
    rw [hD, hD]
    simpa only [OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Units.val_mk0, pow_one, pow_zero, mul_one, smul_eq_mul] using h

@[simp]
theorem complexLinearOfPure_apply (α : E [⋀^Fin 1]→L[ℝ] ℂ)
    (hα : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 α) (v : E) : complexLinearOfPure α hα v = α (fun _ => v) := by
  let _ := (inferInstance : IsScalarTower ℝ ℂ E)
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PureCovectorsOf.Constructions.PureCovectors
