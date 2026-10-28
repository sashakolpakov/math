import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FreeModuleCechExactness

/-! # Free Cech Linear Assembly -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FreeCechLinearAssembly.ProjectiveCech

noncomputable section

/-! The actual assembly of polynomial coordinate cochains into free-module Čech cochains is linear. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [Fintype σ] [LinearOrder σ]
variable (R : Type v) [CommRing R] (ι : Type w) [Fintype ι]

omit [Fintype σ] [LinearOrder σ] [Fintype ι] in
theorem freeCechCoordinate_add (i : ι)
    (f g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R)) :
    ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i (f + g) = ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i f + ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i g := by
  funext s
  change Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s (f s + g s) i = _
  rw [map_add, Finsupp.add_apply]
  rfl

omit [Fintype σ] [LinearOrder σ] [Fintype ι] in
theorem freeCechCoordinate_sub (i : ι)
    (f g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R)) :
    ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i (f - g) = ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i f - ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i g := by
  funext s
  change Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s (f s - g s) i = _
  rw [map_sub, Finsupp.sub_apply]
  rfl

omit [Fintype σ] [LinearOrder σ] [Fintype ι] in
theorem freeCechCoordinate_smul (i : ι) (r : R)
    (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R)) :
    ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i (r • f) = r • ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i f := by
  funext s
  change Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s (r • f s) i = _
  rw [map_smul, Finsupp.smul_apply]
  rfl

def freeCechAssembleLinear :
    (ι → Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) →ₗ[R] ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R) where
  toFun := FreeModuleCechExactness.ProjectiveCech.freeCechAssemble R ι
  map_add' f g := by
    apply FreeModuleCechExactness.ProjectiveCech.freeCechCoordinate_ext R ι
    intro i
    rw [FreeModuleCechExactness.ProjectiveCech.freeCechCoordinate_assemble, freeCechCoordinate_add, FreeModuleCechExactness.ProjectiveCech.freeCechCoordinate_assemble, FreeModuleCechExactness.ProjectiveCech.freeCechCoordinate_assemble]
    rfl
  map_smul' r f := by
    apply FreeModuleCechExactness.ProjectiveCech.freeCechCoordinate_ext R ι
    intro i
    rw [FreeModuleCechExactness.ProjectiveCech.freeCechCoordinate_assemble, freeCechCoordinate_smul, FreeModuleCechExactness.ProjectiveCech.freeCechCoordinate_assemble]
    rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FreeCechLinearAssembly.ProjectiveCech
