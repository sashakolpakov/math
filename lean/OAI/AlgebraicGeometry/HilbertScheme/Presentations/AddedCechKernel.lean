import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedCoordinateCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PiSupportedEquiv
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.CechDifferential

/-! # Added Cech Kernel -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedCechKernel.ProjectiveCech

noncomputable section

/-! The kernel of restriction to retained coordinates consists exactly of the actual cochains on the added chart. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable [Algebra (MvPolynomial (WithBot σ) R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial (WithBot σ) R) (MvPolynomial σ R)]
variable (he : ∀ i : σ, algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X (i : WithBot σ)) = X i)
variable (M : Type w) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial (WithBot σ) R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial (WithBot σ) R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) M]

theorem retainedModuleCechMap_eq_zero_iff (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M) :
    ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M f = 0 ↔
      ∀ s : Finset (WithBot σ), ⊥ ∉ s → f s = 0 := by
  constructor
  · intro h s hs
    obtain ⟨t, rfl⟩ : ∃ t : Finset σ, AddedCoordinateFinsets.ProjectiveCech.retainedCoordinates t = s :=
      ⟨AddedCoordinateFinsets.ProjectiveCech.removeAddedCoordinate s, AddedCoordinateFinsets.ProjectiveCech.retainedCoordinates_representation s hs⟩
    apply (VariableCharts.ProjectiveCech.retainedModuleChartEquiv R Function.Embedding.coeWithBot he M t).injective
    exact (congrFun h t).trans (map_zero (VariableCharts.ProjectiveCech.retainedModuleChartEquiv R Function.Embedding.coeWithBot he M t)).symm
  · intro h
    funext s
    change VariableCharts.ProjectiveCech.retainedModuleChartEquiv R Function.Embedding.coeWithBot he M s (f (AddedCoordinateFinsets.ProjectiveCech.retainedCoordinates s)) = 0
    exact (congrArg (VariableCharts.ProjectiveCech.retainedModuleChartEquiv R Function.Embedding.coeWithBot he M s)
      (h _ (AddedCoordinateFinsets.ProjectiveCech.bot_not_mem_retainedCoordinates s))).trans
      (map_zero (VariableCharts.ProjectiveCech.retainedModuleChartEquiv R Function.Embedding.coeWithBot he M s))

theorem retainedModuleCechMap_ker_support :
    (ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M).ker =
      PiSupportedEquiv.piImageSupport (R := R) (Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := WithBot σ) R M) AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFaceEmbedding := by
  apply Submodule.ext
  intro f
  change ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M f = 0 ↔
    ∀ s, s ∉ Set.range AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFaceEmbedding → f s = 0
  rw [retainedModuleCechMap_eq_zero_iff]
  simp only [AddedCoordinateFinsets.ProjectiveCech.mem_range_addedCoordinateFace]

variable (l : MvPolynomial σ R)
variable (hl : algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X ⊥) = l)

def addedModuleCechComponent :
    ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M →ₗ[R] ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (Presentations.Module.Fractions.GradedModules.AwayModule l M) :=
  PiRestrictionEquiv.piRestrictionLinear (Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := σ) R (Presentations.Module.Fractions.GradedModules.AwayModule l M)) (Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := WithBot σ) R M)
    AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFaceEmbedding (AddedCoordinateCharts.ProjectiveCech.addedModuleChartEquiv R he l hl M)

def addedModuleCechKernelEquiv :
    (ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M).ker ≃ₗ[R]
      ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (Presentations.Module.Fractions.GradedModules.AwayModule l M) :=
  (LinearEquiv.ofEq _ _ (retainedModuleCechMap_ker_support R he M)).trans
    (PiSupportedEquiv.piSupportedRestrictionEquiv (Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := σ) R (Presentations.Module.Fractions.GradedModules.AwayModule l M))
      (Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := WithBot σ) R M) AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFaceEmbedding (AddedCoordinateCharts.ProjectiveCech.addedModuleChartEquiv R he l hl M))

theorem addedModuleCechKernelEquiv_apply
    (f : (ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M).ker) :
    addedModuleCechKernelEquiv R he M l hl f = addedModuleCechComponent R he M l hl f.val := rfl

theorem addedModuleCechComponent_injective_on_kernel
    (f g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M)
    (hf : ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M f = 0)
    (hg : ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M g = 0)
    (hfg : addedModuleCechComponent R he M l hl f = addedModuleCechComponent R he M l hl g) : f = g := by
  have h : (⟨f, hf⟩ : (ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M).ker) = ⟨g, hg⟩ :=
    (addedModuleCechKernelEquiv R he M l hl).injective hfg
  exact congrArg Subtype.val h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedCechKernel.ProjectiveCech
