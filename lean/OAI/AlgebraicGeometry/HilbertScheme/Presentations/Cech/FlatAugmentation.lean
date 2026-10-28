import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.CechVanishing

/-! # Flat Augmentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.FlatAugmentation.ProjectiveCech

noncomputable section

/-! Eventual flatness of the augmentation term from flat projective charts. -/

open _root_.MvPolynomial DirectSum

universe u v

variable {σ : Type v} [Fintype σ] [LinearOrder σ]
variable (R : Type u) [CommRing R]
variable (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

omit [Fintype σ] in
theorem moduleCechTermDifferential_exact (d : ℤ) (q : ℕ)
    (hex : DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d (q + 1)) :
    Function.Exact (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d q)
      (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d (q + 1)) := by
  intro f
  constructor
  · intro hf
    have hf' : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f.val = 0 := congrArg Subtype.val hf
    obtain ⟨g, hg, hgcard, hgd⟩ := hex f.val f.property.1 f.property.2 hf'
    exact ⟨⟨g, hg, hgcard⟩, Subtype.ext hgd⟩
  · rintro ⟨g, rfl⟩
    exact ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_square R M ℳ d q g

omit [Fintype σ] in
theorem moduleCechTermDifferential_injective (d : ℤ)
    (haug : ∀ f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f → ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M 0 f →
      ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f = 0 → f = 0) :
    Function.Injective (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d 0) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply haug (f - g).val (f - g).property.1 (f - g).property.2
  have hzero : ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R M ℳ d 0 (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  exact congrArg Subtype.val hzero

theorem moduleCech_augmentation_flat (d : ℤ)
    (hex : ∀ q, DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d (q + 1))
    (haug : ∀ f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f → ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M 0 f →
      ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f = 0 → f = 0)
    (hflat : ∀ s : Finset σ, s.Nonempty → Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d)) :
    Module.Flat R (ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 0) := by
  apply Presentations.Flat.BoundedComplex.flat_augmentation_of_bounded_exact R (Fintype.card σ)
    (fun q => ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d q) (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R M ℳ d)
  · exact fun q => moduleCechTermDifferential_exact R M ℳ d q (hex q)
  · exact ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_zero R M ℳ d (Fintype.card σ + 1) (by omega)
  · exact moduleCechTermDifferential_injective R M ℳ d haug
  · intro q hq _
    exact ModuleCech.Terms.ProjectiveCech.moduleCechTerm_flat R M ℳ d q hq hflat

theorem moduleCech_eventual_augmentation_flat [Nonempty σ] [IsNoetherianRing R]
    [Decomposition ℳ] [Module.Finite (MvPolynomial σ R) M] :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      (∀ s : Finset σ, s.Nonempty → Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d)) →
      Module.Flat R (ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 0) := by
  obtain ⟨B, hB⟩ := Graded.CechVanishing.ProjectiveCech.moduleCech_eventual_exactness_explicit (σ := σ) R M ℳ
  refine ⟨B, fun d hd hflat => ?_⟩
  exact moduleCech_augmentation_flat R M ℳ d (hB d hd).2 (hB d hd).1 hflat

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.FlatAugmentation.ProjectiveCech
