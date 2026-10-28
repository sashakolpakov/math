import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Square

/-! # Boundaries -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Boundaries.ProjectiveCech

noncomputable section

/-! Actual cochains of fixed cardinal support and their boundary submodules. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

def moduleCechCardSubmodule (q : ℕ) : Submodule R (ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) where
  carrier := {f | ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f}
  zero_mem' := fun _ _ => rfl
  add_mem' {f g} hf hg s hs := by
    change f s + g s = 0
    rw [hf s hs, hg s hs, add_zero]
  smul_mem' r f hf s hs := by
    change r • f s = 0
    rw [hf s hs, smul_zero]

def moduleCechBoundarySubmodule (q : ℕ) : Submodule R (ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :=
  (moduleCechCardSubmodule R M (q - 1)).map (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M)

theorem mem_moduleCechBoundarySubmodule (q : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    f ∈ moduleCechBoundarySubmodule R M q ↔
      ∃ g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
        ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q - 1) g ∧ ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g = f :=
  Submodule.mem_map

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Boundaries.ProjectiveCech
