import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DimensionShift
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedPolynomialModules

/-! # Cech Vanishing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.CechVanishing.ProjectiveCech

noncomputable section

/-!
Eventual exactness of the augmented projective Čech complex for every
finitely generated graded polynomial module over a noetherian ring.
The proof uses constructed finite free covers and bounded Čech length.
-/

open _root_.MvPolynomial DirectSum

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules

universe u v

variable {σ : Type v} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type u) [CommRing R]

theorem freeModuleCech_exactAt (ι : Type (max u v)) [Fintype ι] (w : ι → ℤ) (d : ℤ)
    (hd : (FreeModuleCechExactness.ProjectiveCech.freeCechDegreeBound ι w : ℤ) ≤ d) (q : ℕ) :
    Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R (ι →₀ MvPolynomial σ R) (WeightedFreeModules.GradedModules.weightedFreeGrading R w) d q := by
  cases q with
  | zero =>
    intro f hf hcard hcycle
    have hz := FreeModuleCechExactness.ProjectiveCech.freeModuleCech_augmentation_injective R ι w d
      (fun i => (FreeModuleCechExactness.ProjectiveCech.freeCechDegreeBound_ge ι w i).trans hd) f hf hcard hcycle
    refine ⟨0, fun _ => Submodule.zero_mem _, fun _ _ => rfl, ?_⟩
    rw [map_zero, hz]
  | succ q =>
    intro f hf hcard hcycle
    obtain ⟨g, hg, hgcard, hgd⟩ := FreeModuleCechExactness.ProjectiveCech.freeModuleCech_eventually_exact R ι w d hd q f hf hcard hcycle
    exact ⟨g, hg, hgcard, hgd⟩

variable [IsNoetherianRing R]

theorem exists_moduleCech_bound_above (r : ℕ) :
    ∀ D : Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R, ∃ B : ℕ,
      ∀ d : ℤ, (B : ℤ) ≤ d → ∀ q : ℕ, Fintype.card σ < q + r →
        Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R D.Carrier D.grading d q := by
  induction r with
  | zero =>
    intro D
    refine ⟨0, fun d _ q hq => ?_⟩
    exact Cech.DimensionShift.ProjectiveCech.moduleCechExactAt_of_bounded R D.Carrier D.grading d q (by simpa only [Nat.add_zero] using hq)
  | succ r ih =>
    intro D
    obtain ⟨B, hB⟩ := ih D.syzygy
    let F := FreeModuleCechExactness.ProjectiveCech.freeCechDegreeBound D.cover.generators D.cover.degree
    refine ⟨B + F, fun d hd q hq => ?_⟩
    have hdB : (B : ℤ) ≤ d := by
      have h : (B : ℤ) ≤ ((B + F : ℕ) : ℤ) := by exact_mod_cast Nat.le_add_right B F
      exact h.trans hd
    have hdF : (F : ℤ) ≤ d := by
      have h : (F : ℤ) ≤ ((B + F : ℕ) : ℤ) := by exact_mod_cast Nat.le_add_left F B
      exact h.trans hd
    apply Cech.DimensionShift.ProjectiveCech.moduleCech_dimension_shift R D.syzygy.Carrier D.syzygy.grading D.freeModule.grading D.grading
      D.kernelInclusion D.projection D.kernelInclusion_homogeneous D.projection_homogeneous
      D.kernelInclusion_injective D.projection_surjective D.cover_exact d q
    · exact hB d hdB (q + 1) (by omega)
    · exact freeModuleCech_exactAt R D.cover.generators D.cover.degree d hdF q

theorem finiteGradedPolynomialModule_eventual_cech_exact (D : Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ q : ℕ,
      Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R D.Carrier D.grading d q := by
  obtain ⟨B, hB⟩ := exists_moduleCech_bound_above R (Fintype.card σ + 1) D
  exact ⟨B, fun d hd q => hB d hd q (by omega)⟩

theorem moduleCech_eventual_exactness (M : Type (max u v)) [AddCommGroup M] [Module R M]
    [Module (MvPolynomial σ R) M] [IsScalarTower R (MvPolynomial σ R) M]
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
    [Module.Finite (MvPolynomial σ R) M] :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ q : ℕ,
      Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q :=
  finiteGradedPolynomialModule_eventual_cech_exact R (Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule.ofModule M ℳ)

theorem moduleCech_eventual_exactness_explicit (M : Type (max u v)) [AddCommGroup M] [Module R M]
    [Module (MvPolynomial σ R) M] [IsScalarTower R (MvPolynomial σ R) M]
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
    [Module.Finite (MvPolynomial σ R) M] :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      (∀ f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
        ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f → ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M 0 f →
        ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f = 0 → f = 0) ∧
      (∀ q : ℕ, ∀ f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
        ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f → ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q + 1) f →
        ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f = 0 →
        ∃ g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
          ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d g ∧ ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q g ∧
          ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g = f) := by
  obtain ⟨B, hB⟩ := moduleCech_eventual_exactness (σ := σ) R M ℳ
  refine ⟨B, fun d hd => ⟨?_, ?_⟩⟩
  · intro f hf hcard hcycle
    obtain ⟨g, _, hgcard, hgd⟩ := hB d hd 0 f hf hcard hcycle
    have hdgcard := ModuleCech.Card.ProjectiveCech.moduleCechDifferential_card R M 0 g hgcard
    funext s
    by_cases hs : s.card = 0
    · have hs' : s.card ≠ 0 + 1 := by omega
      exact (congrFun hgd s).symm.trans (hdgcard s hs')
    · exact hcard s hs
  · intro q f hf hcard hcycle
    obtain ⟨g, hg, hgcard, hgd⟩ := hB d hd (q + 1) f hf hcard hcycle
    exact ⟨g, hg, hgcard, hgd⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.CechVanishing.ProjectiveCech
