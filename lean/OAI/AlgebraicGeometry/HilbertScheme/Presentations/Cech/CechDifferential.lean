import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.HomogeneousLift

/-! # Cech Differential -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.CechDifferential.ProjectiveCech

noncomputable section

/-! The restriction from an enlarged coordinate cover commutes with the actual Čech differential. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type v} {τ : Type w} [LinearOrder σ] [LinearOrder τ]
variable (R : Type u) [CommRing R] (e : σ ↪o τ)
variable [Algebra (MvPolynomial τ R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial τ R) (MvPolynomial σ R)]
variable (he : ∀ i : σ, algebraMap (MvPolynomial τ R) (MvPolynomial σ R) (X (e i)) = X i)
variable (M : Type t) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial τ R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial τ R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial τ R) (MvPolynomial σ R) M]

theorem retainedModuleCechMap_differential (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M) :
    ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R e.toEmbedding he M (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f) =
      ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M (ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R e.toEmbedding he M f) := by
  funext s
  change VariableCharts.ProjectiveCech.retainedModuleChartEquiv R e.toEmbedding he M s
    (∑ j ∈ s.map e.toEmbedding, Signs.ProjectiveCech.alternatingSign R (s.map e.toEmbedding) j •
      ModuleCech.Square.ProjectiveCech.moduleCechValue R M f (s.map e.toEmbedding) ((s.map e.toEmbedding).erase j)
        (Finset.erase_subset j (s.map e.toEmbedding))) = _
  rw [map_sum, Finset.sum_map]
  change (∑ i ∈ s, VariableCharts.ProjectiveCech.retainedModuleChartEquiv R e.toEmbedding he M s
    (Signs.ProjectiveCech.alternatingSign R (s.map e.toEmbedding) (e i) •
      ModuleCech.Square.ProjectiveCech.moduleCechValue R M f (s.map e.toEmbedding) ((s.map e.toEmbedding).erase (e i))
        (Finset.erase_subset (e i) (s.map e.toEmbedding)))) =
    ∑ i ∈ s, Signs.ProjectiveCech.alternatingSign R s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset i s)
      (ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R e.toEmbedding he M f (s.erase i))
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, VariableEmbedding.ProjectiveCech.alternatingSign_map]
  apply congrArg (fun x => Signs.ProjectiveCech.alternatingSign R s i • x)
  have hv := ModuleCech.Square.ProjectiveCech.moduleCechValue_congr R M f (s.map e.toEmbedding)
    ((s.map e.toEmbedding).erase (e i)) ((s.erase i).map e.toEmbedding)
    (Finset.erase_subset (e i) (s.map e.toEmbedding))
    (Finset.map_subset_map.mpr (Finset.erase_subset i s)) (Finset.map_erase e.toEmbedding s i).symm
  rw [hv]
  exact VariableCharts.ProjectiveCech.retainedModuleChartEquiv_restriction R e.toEmbedding he M (Finset.erase_subset i s)
    (f ((s.erase i).map e.toEmbedding))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.CechDifferential.ProjectiveCech
