import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.RestrictionTorsion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Square

/-! # Scalar Variables -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ScalarVariables.ProjectiveCech

noncomputable section

/-! Variables acting by coefficient scalars do so on all actual localized Čech cochains. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Module.RestrictionTorsion.GradedModules

universe u v w

variable {σ : Type u}
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

theorem moduleChart_variable_scalar (j : σ) (a : R)
    (ha : ∀ m : M, X (R := R) j • m = a • m) (s : Finset σ) (x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s) :
    X (R := R) j • x = a • x := by
  obtain ⟨k, m, rfl⟩ := Presentations.Module.Fractions.GradedModules.moduleFractionMap_surj (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) x
  rw [← Presentations.Module.RestrictionTorsion.GradedModules.moduleFractionMap_scalar_apply, ha, map_smul]

theorem moduleCech_variable_scalar (j : σ) (a : R)
    (ha : ∀ m : M, X (R := R) j • m = a • m) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    X (R := R) j • f = a • f := by
  funext s
  exact moduleChart_variable_scalar R M j a ha s (f s)

theorem moduleCech_variable_power_scalar (j : σ) (a : R)
    (ha : ∀ m : M, X (R := R) j • m = a • m) (k : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    X (R := R) j ^ k • f = a ^ k • f := by
  induction k with
  | zero => rw [pow_zero, pow_zero, one_smul, one_smul]
  | succ k ih =>
    rw [pow_succ', pow_succ', mul_smul, mul_smul, ih, moduleCech_variable_scalar R M j a ha]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ScalarVariables.ProjectiveCech
