import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.VariableEmbedding
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationDenominatorImage
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ZeroScalarLocalization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleRestriction
import Mathlib.Data.Finset.Preimage

/-! # Embedded Module Charts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedModuleCharts.ProjectiveCech

noncomputable section

/-! Actual projective module charts after deleting complementary variables. -/

open _root_.MvPolynomial

universe u v w t

variable {σ : Type v} {τ : Type w}

theorem finset_not_range_map (e : σ ↪ τ) (s : Finset τ)
    (hs : s ∉ Set.range (Finset.map e)) : ∃ j ∈ s, j ∉ Set.range e := by
  classical
  by_contra! h
  apply hs
  refine ⟨s.preimage e e.injective.injOn, ?_⟩
  rw [Finset.map_eq_image, Finset.image_preimage]
  exact Finset.filter_eq_self.mpr h

variable (R : Type u) [CommRing R] (e : σ ↪ τ)
variable [Algebra (MvPolynomial τ R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial τ R) (MvPolynomial σ R)]
variable (he : algebraMap (MvPolynomial τ R) (MvPolynomial σ R) = (MvPolynomial.killCompl e.injective).toRingHom)

include he in
omit [IsScalarTower R (MvPolynomial τ R) (MvPolynomial σ R)] in
theorem embeddedChartDenominator (s : Finset σ) :
    algebraMap (MvPolynomial τ R) (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.inversionMonomial R (s.map e)) =
      LaurentMonomials.ProjectiveCech.inversionMonomial R s := by
  rw [he]
  exact Cech.VariableEmbedding.ProjectiveCech.killVariables_inversionMonomial_map R e s

variable (M : Type t) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial τ R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial τ R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial τ R) (MvPolynomial σ R) M]

def embeddedModuleChartEquiv (s : Finset σ) :
    Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := τ) R M (s.map e) ≃ₗ[R] Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := σ) R M s :=
  LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq (R := R) M (LaurentMonomials.ProjectiveCech.inversionMonomial R (s.map e)) (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
    (embeddedChartDenominator R e he s)

theorem embeddedModuleChartEquiv_fraction (s : Finset σ) (k : ℕ) (m : M) :
    embeddedModuleChartEquiv R e he M s (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R (s.map e)) k m) =
      Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) k m :=
  LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq_fraction M _ _ _ k m

theorem embeddedModuleChartEquiv_degree (ℳ : ℤ → Submodule R M) (s : Finset σ) (d : ℤ) :
    (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ (s.map e) d).map (embeddedModuleChartEquiv R e he M s).toLinearMap =
      Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d := by
  change (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ _ ((s.map e).card : ℤ) d).map _ = Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ _ (s.card : ℤ) d
  rw [Finset.card_map]
  exact LocalizationDenominatorImage.GradedModules.awayModuleScalarEquivOfEq_degree M ℳ _ _ _ (s.card : ℤ) d

def embeddedModuleChartDegreeEquiv (ℳ : ℤ → Submodule R M) (s : Finset σ) (d : ℤ) :
    Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ (s.map e) d ≃ₗ[R] Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d :=
  (embeddedModuleChartEquiv R e he M s).ofSubmodules _ _ (embeddedModuleChartEquiv_degree R e he M ℳ s d)

include he in
omit [IsScalarTower R (MvPolynomial τ R) (MvPolynomial σ R)] [Module R M]
  [IsScalarTower R (MvPolynomial τ R) M] [IsScalarTower R (MvPolynomial σ R) M] in
theorem moduleChart_subsingleton_outside_embedding (s : Finset τ) (hs : s ∉ Set.range (Finset.map e)) :
    Subsingleton (Graded.ModuleRestriction.ProjectiveCech.ModuleChart (σ := τ) R M s) := by
  obtain ⟨j, hj, hje⟩ := finset_not_range_map e s hs
  apply ZeroScalarLocalization.GradedModules.awayModule_subsingleton_of_algebraMap_zero (B := MvPolynomial σ R) M (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
  rw [he]
  exact Cech.VariableEmbedding.ProjectiveCech.killVariables_inversionMonomial_zero R e s j hj hje

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EmbeddedModuleCharts.ProjectiveCech
