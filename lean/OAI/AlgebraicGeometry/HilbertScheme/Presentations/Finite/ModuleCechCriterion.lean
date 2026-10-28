import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.CechComplex
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CohomologyRepresentatives

/-! # Module Cech Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ModuleCechCriterion.ProjectiveCech

noncomputable section

/-! Finite representatives of actual homogeneous Čech cycles give finite cohomology of the associated cochain complex. -/

open _root_.MvPolynomial _root_.CategoryTheory

universe u v w

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R] [IsNoetherianRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

theorem moduleCech_homology_finite_of_representatives (d : ℤ) (q : ℕ)
    (G : Submodule R (ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)) [Module.Finite R G]
    (hrep : ∀ f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f → ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q + 1) f →
      ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f = 0 →
      ∃ g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
        ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d g ∧ ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q g ∧
          f - ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g ∈ G) :
    Module.Finite R ((ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R M ℳ d).homology (q + 1)) := by
  let K := ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := σ) R M ℳ d
  let S := K.sc' q (q + 1) (q + 1 + 1)
  let U : Submodule R S.X₂ := G.comap (ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d (q + 1)).subtype
  let : Module.Finite R U := CohomologyRepresentatives.finite_comap_of_injective R
    (ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d (q + 1)).subtype (Submodule.subtype_injective _) G
  have hS : Module.Finite R S.homology := by
    apply CohomologyRepresentatives.finite_shortComplex_homology_of_representatives R S U
    intro b hb
    have hb' : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M b.val = 0 := by
      change (K.d (q + 1) (q + 1 + 1)) b = 0 at hb
      rw [ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex_d] at hb
      exact congrArg Subtype.val hb
    obtain ⟨g, hg, hgc, hgr⟩ := hrep b.val b.property.1 b.property.2 hb'
    refine ⟨⟨g, hg, hgc⟩, ?_⟩
    change b.val - ((K.d q (q + 1)) ⟨g, hg, hgc⟩).val ∈ G
    rw [ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex_d]
    exact hgr
  let := hS
  let e := K.homologyIsoSc' q (q + 1) (q + 1 + 1)
    ((ComplexShape.up ℕ).prev_eq' rfl) ((ComplexShape.up ℕ).next_eq' rfl)
  exact Module.Finite.of_surjective e.inv.hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ModuleCechCriterion.ProjectiveCech
