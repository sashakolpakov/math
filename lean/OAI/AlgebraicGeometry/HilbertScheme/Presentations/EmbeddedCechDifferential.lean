import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedModuleCech

/-! # Embedded Cech Differential -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedCechDifferential.ProjectiveCech

noncomputable section

/-! Ordered deletion of zero variables preserves the actual alternating Čech differential. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type v} {τ : Type w} [LinearOrder σ] [LinearOrder τ]
variable (R : Type u) [CommRing R] (e : σ ↪o τ)
variable [Algebra (MvPolynomial τ R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial τ R) (MvPolynomial σ R)]
variable (he : algebraMap (MvPolynomial τ R) (MvPolynomial σ R) =
  (MvPolynomial.killCompl e.injective).toRingHom)
variable (M : Type t) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial τ R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial τ R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial τ R) (MvPolynomial σ R) M]

theorem embeddedModuleCechEquiv_differential (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M) :
    EmbeddedModuleCech.ProjectiveCech.embeddedModuleCechEquiv R e.toEmbedding he M (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f) =
      ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M (EmbeddedModuleCech.ProjectiveCech.embeddedModuleCechEquiv R e.toEmbedding he M f) := by
  funext s
  change EmbeddedModuleCharts.ProjectiveCech.embeddedModuleChartEquiv R e.toEmbedding he M s
    (∑ j ∈ s.map e.toEmbedding, Cech.Signs.ProjectiveCech.alternatingSign R (s.map e.toEmbedding) j •
      ModuleCech.Square.ProjectiveCech.moduleCechValue R M f (s.map e.toEmbedding) ((s.map e.toEmbedding).erase j)
        (Finset.erase_subset j (s.map e.toEmbedding))) = _
  rw [map_sum, Finset.sum_map]
  change (∑ i ∈ s, EmbeddedModuleCharts.ProjectiveCech.embeddedModuleChartEquiv R e.toEmbedding he M s
    (Cech.Signs.ProjectiveCech.alternatingSign R (s.map e.toEmbedding) (e i) •
      ModuleCech.Square.ProjectiveCech.moduleCechValue R M f (s.map e.toEmbedding) ((s.map e.toEmbedding).erase (e i))
        (Finset.erase_subset (e i) (s.map e.toEmbedding)))) =
    ∑ i ∈ s, Cech.Signs.ProjectiveCech.alternatingSign R s i • Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.erase_subset i s)
      (EmbeddedModuleCech.ProjectiveCech.embeddedModuleCechEquiv R e.toEmbedding he M f (s.erase i))
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, Cech.VariableEmbedding.ProjectiveCech.alternatingSign_map]
  apply congrArg (fun x => Cech.Signs.ProjectiveCech.alternatingSign R s i • x)
  have hv := ModuleCech.Square.ProjectiveCech.moduleCechValue_congr R M f (s.map e.toEmbedding)
    ((s.map e.toEmbedding).erase (e i)) ((s.erase i).map e.toEmbedding)
    (Finset.erase_subset (e i) (s.map e.toEmbedding))
    (Finset.map_subset_map.mpr (Finset.erase_subset i s)) (Finset.map_erase e.toEmbedding s i).symm
  rw [hv, EmbeddedChartRestriction.ProjectiveCech.embeddedModuleCechValue]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedCechDifferential.ProjectiveCech
