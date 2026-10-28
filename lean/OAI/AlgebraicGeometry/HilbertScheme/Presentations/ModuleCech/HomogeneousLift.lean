import OAI.AlgebraicGeometry.HilbertScheme.Presentations.VariableCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PiRestrictionLift
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Square

/-! # Homogeneous Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.HomogeneousLift.ProjectiveCech

noncomputable section

/-! Restriction to retained coordinates gives the actual map from an enlarged Čech complex. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type v} {τ : Type w}
variable (R : Type u) [CommRing R] (e : σ ↪ τ)
variable [Algebra (MvPolynomial τ R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial τ R) (MvPolynomial σ R)]
variable (he : ∀ i : σ, algebraMap (MvPolynomial τ R) (MvPolynomial σ R) (X (e i)) = X i)
variable (M : Type t) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial τ R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial τ R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial τ R) (MvPolynomial σ R) M]

def retainedModuleCechMap : Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M →ₗ[R] Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M :=
  PiRestrictionEquiv.piRestrictionLinear (Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := σ) R M) (Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := τ) R M)
    (Finset.mapEmbedding e).toEmbedding (VariableCharts.ProjectiveCech.retainedModuleChartEquiv R e he M)

theorem retainedModuleCechMap_card (q : ℕ) (f : Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M)
    (hf : Card.ProjectiveCech.ModuleCechCardSupported R M q f) :
    Card.ProjectiveCech.ModuleCechCardSupported R M q (retainedModuleCechMap R e he M f) := by
  intro s hs
  change VariableCharts.ProjectiveCech.retainedModuleChartEquiv R e he M s (f (s.map e)) = 0
  rw [hf (s.map e) (by simpa only [Finset.card_map] using hs), map_zero]

theorem retainedModuleCechMap_homogeneous (ℳ : ℤ → Submodule R M) (d : ℤ)
    (f : Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M) (hf : Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f) :
    Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d (retainedModuleCechMap R e he M f) := by
  intro s
  rw [← VariableCharts.ProjectiveCech.retainedModuleChartEquiv_degree R e he M ℳ s d]
  exact Submodule.mem_map.mpr ⟨f (s.map e), hf _, rfl⟩

theorem retainedModuleCechMap_homogeneous_lift (ℳ : ℤ → Submodule R M) (d : ℤ) (q : ℕ)
    (f : Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (hf : Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f)
    (hfc : Card.ProjectiveCech.ModuleCechCardSupported R M q f) :
    ∃ g : Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M,
      Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d g ∧ Card.ProjectiveCech.ModuleCechCardSupported R M q g ∧ retainedModuleCechMap R e he M g = f := by
  obtain ⟨g, hg, hzero⟩ := PiRestrictionLift.piRestrictionLinear_lift_supported
    (Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := σ) R M) (Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := τ) R M)
    (Finset.mapEmbedding e).toEmbedding (VariableCharts.ProjectiveCech.retainedModuleChartEquiv R e he M) f
  refine ⟨g, ?_, ?_, hg⟩
  · intro s
    by_cases hs : s ∈ Set.range (Finset.map e)
    · obtain ⟨a, rfl⟩ := hs
      have hm := hf a
      rw [← VariableCharts.ProjectiveCech.retainedModuleChartEquiv_degree R e he M ℳ a d, ← congrFun hg a] at hm
      obtain ⟨x, hx, heq⟩ := Submodule.mem_map.mp hm
      exact ((VariableCharts.ProjectiveCech.retainedModuleChartEquiv R e he M a).injective heq) ▸ hx
    · rw [hzero s hs]
      exact Submodule.zero_mem _
  · intro s hsc
    by_cases hs : s ∈ Set.range (Finset.map e)
    · obtain ⟨a, rfl⟩ := hs
      apply (VariableCharts.ProjectiveCech.retainedModuleChartEquiv R e he M a).injective
      rw [map_zero]
      exact (congrFun hg a).trans (hfc a (by simpa only [Finset.card_map] using hsc))
    · exact hzero s hs

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.HomogeneousLift.ProjectiveCech
