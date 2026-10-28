import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReversedCechSigns
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DimensionShift

/-! # Reversed Module Cech -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReversedModuleCech.ProjectiveCech

noncomputable section

/-! Reversing the variable order preserves the actual augmented Čech exactness in every homogeneous degree. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

local instance : Module (MvPolynomial σᵒᵈ R) M := ‹Module (MvPolynomial σ R) M›
local instance : IsScalarTower R (MvPolynomial σᵒᵈ R) M := ‹IsScalarTower R (MvPolynomial σ R) M›

def reversedModuleCechDifferential : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M →ₗ[R] ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M :=
  ModuleCech.Card.ProjectiveCech.moduleCechDifferential (σ := σᵒᵈ) R M

theorem moduleCechDifferential_orderDual (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (s : Finset σ) :
    reversedModuleCechDifferential R M f s =
      (-1 : R) ^ (s.card - 1) • ModuleCech.Card.ProjectiveCech.moduleCechDifferential (σ := σ) R M f s := by
  change (∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign (σ := σᵒᵈ) R s i •
    Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset i s) (f (s.erase i))) =
    (-1 : R) ^ (s.card - 1) • ∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign R s i •
      Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset i s) (f (s.erase i))
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ReversedCechSigns.ProjectiveCech.alternatingSign_orderDual R s i hi, mul_smul]

theorem moduleCechDifferential_orderDual_card (q : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f) :
    reversedModuleCechDifferential R M f = (-1 : R) ^ q • ModuleCech.Card.ProjectiveCech.moduleCechDifferential (σ := σ) R M f := by
  funext s
  rw [moduleCechDifferential_orderDual]
  by_cases hs : s.card = q + 1
  · rw [hs, Nat.add_sub_cancel]
    rfl
  · have hz := ModuleCech.Card.ProjectiveCech.moduleCechDifferential_card R M q f hf s hs
    change (-1 : R) ^ (s.card - 1) • ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f s =
      (-1 : R) ^ q • ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f s
    rw [hz, smul_zero, smul_zero]

theorem moduleCechDifferential_orderDual_eq_zero_iff (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) :
    reversedModuleCechDifferential R M f = 0 ↔ ModuleCech.Card.ProjectiveCech.moduleCechDifferential (σ := σ) R M f = 0 := by
  constructor
  · intro h
    funext s
    have hs := congrFun h s
    rw [moduleCechDifferential_orderDual] at hs
    have h' := congrArg (fun x : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s => (-1 : R) ^ (s.card - 1) • x) hs
    simpa only [smul_smul, ReversedCechSigns.ProjectiveCech.neg_one_power_square, one_smul, Pi.zero_apply, smul_zero] using h'
  · intro h
    funext s
    rw [moduleCechDifferential_orderDual, show ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f s = 0 from congrFun h s, smul_zero]
    rfl

theorem moduleCechExactAt_orderDual (ℳ : ℤ → Submodule R M) (d : ℤ) (q : ℕ)
    (hex : Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q) : Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σᵒᵈ) R M ℳ d q := by
  change ∀ f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
    ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f → ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f → reversedModuleCechDifferential R M f = 0 →
    ∃ g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d g ∧ ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q - 1) g ∧ reversedModuleCechDifferential R M g = f
  intro f hf hfc hcycle
  obtain ⟨g, hg, hgc, hgd⟩ := hex f hf hfc ((moduleCechDifferential_orderDual_eq_zero_iff (σ := σ) R M f).mp hcycle)
  refine ⟨(-1 : R) ^ (q - 1) • g, fun s => Submodule.smul_mem _ _ (hg s), ?_, ?_⟩
  · intro s hs
    change (-1 : R) ^ (q - 1) • g s = 0
    rw [hgc s hs, smul_zero]
  · rw [map_smul, moduleCechDifferential_orderDual_card R M (q - 1) g hgc, hgd,
      smul_smul, ReversedCechSigns.ProjectiveCech.neg_one_power_square, one_smul]

theorem moduleCechExactAt_orderDual_iff (ℳ : ℤ → Submodule R M) (d : ℤ) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σᵒᵈ) R M ℳ d q ↔ Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q :=
  ⟨moduleCechExactAt_orderDual (σ := σᵒᵈ) R M ℳ d q, moduleCechExactAt_orderDual R M ℳ d q⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ReversedModuleCech.ProjectiveCech
