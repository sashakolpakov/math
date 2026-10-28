import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedChartRestriction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PiRestrictionEquiv

/-! # Embedded Module Cech -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedModuleCech.ProjectiveCech

noncomputable section

/-! Actual Čech cochains after deleting variables that act by zero. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type v} {τ : Type w}
variable (R : Type u) [CommRing R] (e : σ ↪ τ)
variable [Algebra (MvPolynomial τ R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial τ R) (MvPolynomial σ R)]
variable (he : algebraMap (MvPolynomial τ R) (MvPolynomial σ R) =
  (MvPolynomial.killCompl e.injective).toRingHom)
variable (M : Type t) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial τ R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial τ R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial τ R) (MvPolynomial σ R) M]

def embeddedModuleCechEquiv :
    ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M ≃ₗ[R] ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M :=
  PiRestrictionEquiv.piRestrictionEquiv (Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := σ) R M) (Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := τ) R M)
    (Finset.mapEmbedding e).toEmbedding (EmbeddedModuleCharts.ProjectiveCech.embeddedModuleChartEquiv R e he M)
    (EmbeddedModuleCharts.ProjectiveCech.moduleChart_subsingleton_outside_embedding R e he M)

theorem embeddedModuleCechEquiv_apply (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M) (s : Finset σ) :
    embeddedModuleCechEquiv R e he M f s =
      EmbeddedModuleCharts.ProjectiveCech.embeddedModuleChartEquiv R e he M s (f (s.map e)) := rfl

theorem embeddedModuleCechEquiv_card (q : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M) :
    ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q (embeddedModuleCechEquiv R e he M f) ↔
      ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f := by
  constructor
  · intro h s hs
    by_cases hr : s ∈ Set.range (Finset.map e)
    · obtain ⟨a, rfl⟩ := hr
      apply (EmbeddedModuleCharts.ProjectiveCech.embeddedModuleChartEquiv R e he M a).injective
      rw [map_zero]
      exact h a (by simpa only [Finset.card_map] using hs)
    · exact @Subsingleton.elim _ (EmbeddedModuleCharts.ProjectiveCech.moduleChart_subsingleton_outside_embedding R e he M s hr) _ _
  · intro h s hs
    rw [embeddedModuleCechEquiv_apply, h (s.map e) (by simpa only [Finset.card_map] using hs), map_zero]

theorem embeddedModuleCechEquiv_homogeneous (ℳ : ℤ → Submodule R M) (d : ℤ)
    (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := τ) R M) :
    ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d (embeddedModuleCechEquiv R e he M f) ↔
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f := by
  constructor
  · intro h s
    by_cases hr : s ∈ Set.range (Finset.map e)
    · obtain ⟨a, rfl⟩ := hr
      have hm := h a
      rw [← EmbeddedModuleCharts.ProjectiveCech.embeddedModuleChartEquiv_degree R e he M ℳ a d] at hm
      obtain ⟨x, hx, heq⟩ := Submodule.mem_map.mp hm
      have hx' : x = f (a.map e) := (EmbeddedModuleCharts.ProjectiveCech.embeddedModuleChartEquiv R e he M a).injective heq
      exact hx' ▸ hx
    · have hz := @Subsingleton.elim _ (EmbeddedModuleCharts.ProjectiveCech.moduleChart_subsingleton_outside_embedding R e he M s hr) (f s) 0
      rw [hz]
      exact Submodule.zero_mem _
  · intro h s
    rw [← EmbeddedModuleCharts.ProjectiveCech.embeddedModuleChartEquiv_degree R e he M ℳ s d]
    exact Submodule.mem_map.mpr ⟨f (s.map e), h _, rfl⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedModuleCech.ProjectiveCech
