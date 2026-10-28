import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison
import OAI.RepresentationTheory.Weil.Local.FourierEquivalence

/-! # Heisenberg -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.Heisenberg.CM

noncomputable section

/-! Real Heisenberg operators on PoissonAutomorphy's actual Schwartz functions,
with stability supplied by the proved LocalWeil real test-space construction. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison.CM
variable (n : ℕ)

theorem heisenberg_mem (p q : Fin n → ℝ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter p q f.val ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) := by
  have h := RepresentationTheory.Weil.Local.FourierEquivalence.Construction.real_heisenberg_mem 1 (Sum.elim q p) (SchwartzComparison.CM.tests n f)
  have he : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter p q f.val =
      RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1)
        (Sum.elim q p) (SchwartzComparison.CM.tests n f).val := funext (SchwartzComparison.CM.heisenberg_formula n p q f.val)
  rw [he]
  exact (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff _).mpr
    (RepresentationTheory.Weil.Local.RealTestSpace.Construction.schwartzBruhat_real_iff.mp h)

def operator (p q : Fin n → ℝ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) where
  toFun f := ⟨RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter p q f.val, heisenberg_mem n p q f⟩
  map_add' f h := by
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact mul_left_comm _ _ _

theorem operator_apply (p q : Fin n → ℝ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (x : Fin n → ℝ) :
    (operator n p q f).val x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter p q f.val x := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.Heisenberg.CM
