import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.VariableTorsion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ScalarVariables
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Boundaries
import Mathlib.RingTheory.Ideal.Operations

/-! # Unit Ideal Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.UnitIdealExactness.ProjectiveCech

noncomputable section

/-! The augmented Čech complex is exact when its scalar denominators generate the unit ideal. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [Fintype σ] [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

theorem moduleCech_exact_of_scalar_unit_ideal (a : σ → R)
    (ha : ∀ j (m : M), X (R := R) j • m = a j • m)
    (hunit : Ideal.span (Set.range a) = ⊤)
    (q : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f) (hcycle : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f = 0) :
    ∃ g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
      ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q - 1) g ∧ ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g = f := by
  apply (Boundaries.ProjectiveCech.mem_moduleCechBoundarySubmodule R M q f).mp
  apply (Boundaries.ProjectiveCech.moduleCechBoundarySubmodule R M q).mem_of_span_eq_top_of_smul_pow_mem (Set.range a) hunit f
  intro r
  obtain ⟨j, hj⟩ := r.property
  obtain ⟨k, g, hgc, hgd⟩ := VariableTorsion.ProjectiveCech.moduleCech_variable_power_boundary R M j q f hf hcycle
  refine ⟨k, (Boundaries.ProjectiveCech.mem_moduleCechBoundarySubmodule R M q _).mpr ⟨g, hgc, ?_⟩⟩
  rw [hgd, ScalarVariables.ProjectiveCech.moduleCech_variable_power_scalar R M j (a j) (ha j), hj]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.UnitIdealExactness.ProjectiveCech
