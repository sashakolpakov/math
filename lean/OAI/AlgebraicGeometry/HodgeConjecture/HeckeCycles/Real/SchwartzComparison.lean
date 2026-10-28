import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
import OAI.RepresentationTheory.Weil.Local.RealTestSpace

/-! # Schwartz Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison.CM

noncomputable section

/-! PoissonAutomorphy's real test space and LocalWeil's constructed real Bruhat space are
the same functions. Their standard additive characters and Heisenberg
formulas agree after the prescribed momentum-position swap. -/

open scoped Classical

def tests (n : ℕ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n where
  toFun f := ⟨f.val, RepresentationTheory.Weil.Local.RealTestSpace.Construction.schwartzBruhat_real_iff.mpr
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff f.val |>.mp f.property)⟩
  invFun f := ⟨f.val, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff f.val |>.mpr
    (RepresentationTheory.Weil.Local.RealTestSpace.Construction.schwartzBruhat_real_iff.mp f.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tests_apply (n : ℕ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (x : Fin n → ℝ) :
    (tests n f).val x = f.val x := rfl

theorem tests_symm_apply (n : ℕ) (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : Fin n → ℝ) :
    ((tests n).symm f).val x = f.val x := rfl

theorem standard_character : RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1 = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter := by
  ext t
  simp only [RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter_apply, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter_apply, mul_one]

theorem heisenberg_formula (n : ℕ) (p q : Fin n → ℝ) (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter p q f x =
      RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (Sum.elim q p) f x := by
  rw [standard_character]
  unfold RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction
  simp only [Sum.elim_inl, Sum.elim_inr, map_div₀, map_one, map_ofNat]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison.CM
