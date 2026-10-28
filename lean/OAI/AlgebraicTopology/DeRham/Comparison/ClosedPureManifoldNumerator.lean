import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses
import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import OAI.Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence

/-! # Closed Pure Manifold Numerator -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ClosedPureManifoldNumerator

noncomputable section

/-!
# The literal numerator of the Clay pure-form quotient

The nested submodule used by the class maps is canonically the actual
intersection of closed forms and pure forms. Its type condition is precisely
the inverse-character action on real tangent covectors, or equivalently on
the literal real exterior-power dual in finite dimensions.
-/

open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The nested numerator is exactly the actual intersection of closed and pure forms. -/
def pureClosedManifoldNumeratorEquiv (p q : ℕ) :
    ManifoldPureClasses.pureClosedManifoldForms E M p q ≃ₗ[ℂ] ManifoldPureClasses.closedPureManifoldForms E M p q where
  toFun form := ⟨form.val.val, ⟨form.val.property, form.property⟩⟩
  invFun form := ⟨⟨form.val, form.property.1⟩, form.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem pureClosedManifoldNumeratorEquiv_val (p q : ℕ)
    (form : ManifoldPureClasses.pureClosedManifoldForms E M p q) :
    (pureClosedManifoldNumeratorEquiv E M p q form).val = form.val.val := rfl

/-- The numerator condition is the actual exterior differential equation and
the official inverse-character action on the real tangent bundle. -/
theorem mem_closedPureManifoldForms_iff_tangent (p q : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q)) :
    form ∈ ManifoldPureClasses.closedPureManifoldForms E M p q ↔
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 ∧
        Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M p q (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)) := by
  rw [ManifoldPureClasses.mem_closedPureManifoldForms]
  exact and_congr Iff.rfl (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _)

/-- In finite dimensions the same numerator is expressed literally on the
complex-valued real exterior-power dual appearing in the official statement. -/
theorem mem_closedPureManifoldForms_iff_exteriorDual [FiniteDimensional ℝ E] (p q : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q)) :
    form ∈ ManifoldPureClasses.closedPureManifoldForms E M p q ↔
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 ∧
        ∀ (x : M) (z : ℂˣ),
          (Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.tangentExteriorCovectorEquiv x (p + q) (form.val x)).comp
              (exteriorPower.map (p + q)
                (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentScalarMap x (↑(z⁻¹) : ℂ)).toLinearMap) =
            ((z : ℂ) ^ (-(p : ℤ)) * (star (z : ℂ)) ^ (-(q : ℤ))) •
              Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.tangentExteriorCovectorEquiv x (p + q) (form.val x) := by
  rw [ManifoldPureClasses.mem_closedPureManifoldForms]
  exact and_congr Iff.rfl (Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.hasManifoldBidegree_iff_exteriorDual_action _)

end

end OAI.AlgebraicTopology.DeRham.Comparison.ClosedPureManifoldNumerator
