import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedCechKernel
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedChartRestriction

/-! # Added Kernel Differential -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedKernelDifferential.ProjectiveCech

noncomputable section

/-! On the kernel of retained-coordinate restriction, the added-chart component negates the Čech differential. -/

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
variable (l : MvPolynomial σ R)
variable (hl : algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X ⊥) = l)

theorem retainedModuleCechMap_kernel_differential (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M)
    (hf : ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M f = 0) :
    ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f) = 0 := by
  let e : σ ↪o WithBot σ :=
    { toEmbedding := Function.Embedding.coeWithBot, map_rel_iff' := WithBot.coe_le_coe }
  have he' : ∀ i : σ, algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X (e i)) = X i := he
  have hd := Cech.CechDifferential.ProjectiveCech.retainedModuleCechMap_differential R e he' M f
  have hzero : ModuleCech.Card.ProjectiveCech.moduleCechDifferential (σ := σ) R M
      (ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M f) = 0 :=
    (congrArg (ModuleCech.Card.ProjectiveCech.moduleCechDifferential (σ := σ) R M) hf).trans
      (map_zero (ModuleCech.Card.ProjectiveCech.moduleCechDifferential (σ := σ) R M))
  exact hd.trans hzero

theorem addedModuleCechComponent_differential (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M)
    (hf : ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M f = 0) :
    AddedCechKernel.ProjectiveCech.addedModuleCechComponent R he M l hl (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f) =
      -ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (AddedCechKernel.ProjectiveCech.addedModuleCechComponent R he M l hl f) := by
  funext s
  let E := AddedCoordinateCharts.ProjectiveCech.addedModuleChartEquiv R he l hl M s
  have hzero : ModuleCech.Square.ProjectiveCech.moduleCechValue R M f (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) ((AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s).erase ⊥)
      (Finset.erase_subset ⊥ (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s)) = 0 := by
    have hv := ModuleCech.Square.ProjectiveCech.moduleCechValue_congr R M f (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) ((AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s).erase ⊥)
      (AddedCoordinateFinsets.ProjectiveCech.retainedCoordinates s) (Finset.erase_subset ⊥ (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s))
      (Finset.subset_insert ⊥ (AddedCoordinateFinsets.ProjectiveCech.retainedCoordinates s)) (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace_erase_bot s)
    rw [hv]
    change Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M _ (f (AddedCoordinateFinsets.ProjectiveCech.retainedCoordinates s)) = 0
    rw [(AddedCechKernel.ProjectiveCech.retainedModuleCechMap_eq_zero_iff R he M f).mp hf _ (AddedCoordinateFinsets.ProjectiveCech.bot_not_mem_retainedCoordinates s), map_zero]
  change E (∑ i ∈ insert ⊥ (AddedCoordinateFinsets.ProjectiveCech.retainedCoordinates s), Cech.Signs.ProjectiveCech.alternatingSign R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) i •
    ModuleCech.Square.ProjectiveCech.moduleCechValue R M f (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) ((AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s).erase i)
      (Finset.erase_subset i (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s))) =
    -(∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign R s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (Finset.erase_subset i s)
      (AddedCechKernel.ProjectiveCech.addedModuleCechComponent R he M l hl f (s.erase i)))
  rw [Finset.sum_insert (AddedCoordinateFinsets.ProjectiveCech.bot_not_mem_retainedCoordinates s), hzero, smul_zero, zero_add, map_sum]
  change (∑ i ∈ s.map Function.Embedding.coeWithBot, E (Cech.Signs.ProjectiveCech.alternatingSign R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) i •
    ModuleCech.Square.ProjectiveCech.moduleCechValue R M f (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) ((AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s).erase i)
      (Finset.erase_subset i (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s)))) = _
  rw [Finset.sum_map, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change E (Cech.Signs.ProjectiveCech.alternatingSign R (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) (i : WithBot σ) •
    ModuleCech.Square.ProjectiveCech.moduleCechValue R M f (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s) ((AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s).erase (i : WithBot σ))
      (Finset.erase_subset (i : WithBot σ) (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s))) = _
  rw [map_smul, AddedCoordinateFinsets.ProjectiveCech.alternatingSign_added_coe, neg_smul]
  apply congrArg (fun x => -(Cech.Signs.ProjectiveCech.alternatingSign R s i • x))
  have hv := ModuleCech.Square.ProjectiveCech.moduleCechValue_congr R M f (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s)
    ((AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s).erase (i : WithBot σ)) (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace (s.erase i))
    (Finset.erase_subset (i : WithBot σ) (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s))
    (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace_subset (Finset.erase_subset i s)) (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace_erase_coe s i)
  rw [hv]
  exact AddedChartRestriction.ProjectiveCech.addedModuleChartEquiv_restriction R he l hl M (Finset.erase_subset i s) (f (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace (s.erase i)))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedKernelDifferential.ProjectiveCech
