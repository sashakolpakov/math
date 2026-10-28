import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PairCompatibility

/-! # All Pair Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AllPairCompatibility

noncomputable section

/-! The first homogeneous Čech kernel can be checked on every pair, including repeated and reversed indices. -/

universe u v w

variable {σ : Type u} [LinearOrder σ] (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

theorem moduleCechPairAgreement_symm (f : HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M) (i j : σ)
    (h : PairDifferential.moduleCechPairRestrictionLeft R M i j (f {i}) = PairDifferential.moduleCechPairRestrictionRight R M i j (f {j})) :
    PairDifferential.moduleCechPairRestrictionLeft R M j i (f {j}) = PairDifferential.moduleCechPairRestrictionRight R M j i (f {i}) := by
  have he : ∀ (s : Finset σ) (hi : {i} ⊆ s) (hj : {j} ⊆ s), s = {i, j} →
      HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (s := {j}) (t := s) hj (f {j}) =
        HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (s := {i}) (t := s) hi (f {i}) := by
    intro s hi hj hs
    subst s
    exact h.symm
  exact he {j, i} _ _ (Finset.pair_comm j i)

theorem moduleCech_one_cocycle_iff_all (d : ℤ) (f : HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 1) :
    HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d 1 f = 0 ↔
      ∀ i j : σ, PairDifferential.moduleCechPairRestrictionLeft R M i j (f.val {i}) =
        PairDifferential.moduleCechPairRestrictionRight R M i j (f.val {j}) := by
  rw [PairCompatibility.moduleCech_one_cocycle_iff]
  constructor
  · intro h i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact h i j hij
    · rfl
    · exact moduleCechPairAgreement_symm R M f.val j i (h j i hji)
  · intro h i j _
    exact h i j

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AllPairCompatibility
