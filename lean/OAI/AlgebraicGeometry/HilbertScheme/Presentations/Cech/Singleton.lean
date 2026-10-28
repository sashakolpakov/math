import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Square

/-! # Singleton -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Singleton.ProjectiveCech

/-! The first projective Čech differential on a singleton chart. -/

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

theorem moduleCechDifferential_singleton (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (i : σ) :
    ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f {i} = Signs.ProjectiveCech.alternatingSign R {i} i •
      ModuleCech.Square.ProjectiveCech.moduleCechValue R M f {i} (({i} : Finset σ).erase i) (Finset.erase_subset i {i}) :=
  Finset.sum_singleton _ _

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Singleton.ProjectiveCech
