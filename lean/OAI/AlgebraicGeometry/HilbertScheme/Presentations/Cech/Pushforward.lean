import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ConstantModuleContraction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Square

/-! # Pushforward -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Pushforward.ProjectiveCech

noncomputable section

/-! Restrict all subfaces to one actual projective chart, so their Čech sums have a common target. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

def moduleCechPushforward (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (a : Finset σ) :
    Finset σ → Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M a :=
  fun s => if h : s ⊆ a then Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h (f s) else 0

theorem moduleCechPushforward_of_subset (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (a s : Finset σ) (h : s ⊆ a) :
    moduleCechPushforward R M f a s = Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h (f s) := by
  rw [moduleCechPushforward, dite_eq_left h]

theorem moduleCechPushforward_differential (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (a s : Finset σ) (h : s ⊆ a) :
    Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f s) =
      ConstantModuleContraction.ProjectiveCech.constantModuleDifferential R (Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M a) (moduleCechPushforward R M f a) s := by
  change Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h
    (∑ i ∈ s, Signs.ProjectiveCech.alternatingSign R s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset i s)
      (f (s.erase i))) = ∑ i ∈ s, Signs.ProjectiveCech.alternatingSign R s i • moduleCechPushforward R M f a (s.erase i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, moduleCechPushforward_of_subset R M f a (s.erase i)
    ((Finset.erase_subset i s).trans h)]
  apply congrArg (fun x => Signs.ProjectiveCech.alternatingSign R s i • x)
  exact LinearMap.congr_fun (Presentations.Module.ChartCompatibility.ProjectiveCech.moduleChartRestriction_comp R M (Finset.erase_subset i s) h) (f (s.erase i))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Pushforward.ProjectiveCech
