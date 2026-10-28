import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Card

/-! # Cech Restriction Index Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.CechRestrictionIndexEquality

noncomputable section

/-! Graded Čech restriction values respect equality of their finite source indices. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech

universe u v w

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M]

theorem moduleChartRestriction_family_congr (f : HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    {s s' t : Finset σ} (he : s = s') (h : s ⊆ t) (h' : s' ⊆ t) :
    HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h (f s) = HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h' (f s') := by
  subst s'
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.CechRestrictionIndexEquality
