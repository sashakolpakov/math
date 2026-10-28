import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.FiberwiseComplex
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CechKernelQuotients
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.AugmentationDegree
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.DimensionShift

/-! # Fiberwise Module Cech -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech

noncomputable section

/-! Finite and flat degree-section modules and higher exactness from flat charts and actual residue-field Čech complexes. -/

open _root_.MvPolynomial DirectSum

universe u v

variable {σ : Type v} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M] [Module.Finite (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

abbrev moduleCechSections (d : ℤ) := (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d 1).ker

theorem moduleCechSections_finite (d : ℤ) [Module.Finite R (ℳ d)] :
    Module.Finite R (moduleCechSections (σ := σ) R M ℳ d) := by
  let : Module.Finite R (ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 0) :=
    Module.Finite.equiv (Cech.AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := σ) R M ℳ d).symm
  let : Module.Finite R (FiberwiseExactness.linearKernelCohomology R (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d 0)
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d 1) (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_square R M ℳ d 0)) :=
    Presentations.Finite.CechKernelQuotients.ProjectiveCech.moduleCech_kernelQuotient_finite R M ℳ d 0
  exact FiberwiseExactness.kernel_finite_of_finite_cohomology R (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d 0)
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d 1) (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_square R M ℳ d 0)

theorem moduleCech_fiberwise_exact_flat (d : ℤ)
    (hflat : ∀ s : Finset σ, s.Nonempty → Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d))
    (hfiber : ∀ q : ℕ, ∀ p : PrimeSpectrum R,
      Function.Exact ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d (q + 1)).lTensor p.asIdeal.ResidueField)
        ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d (q + 1 + 1)).lTensor p.asIdeal.ResidueField)) :
    Module.Flat R (moduleCechSections (σ := σ) R M ℳ d) ∧
      ∀ q : ℕ, Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d (q + 2) := by
  have h := Bounded.FiberwiseComplex.bounded_fiberwise_exact_flat R (Fintype.card σ)
    (fun q => ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d (q + 1))
    (fun q => ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d (q + 1))
    (fun q => ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_square R M ℳ d (q + 1))
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_zero R M ℳ d (Fintype.card σ + 1) (by omega))
    (fun q _ => ModuleCech.Terms.ProjectiveCech.moduleCechTerm_flat R M ℳ d (q + 1) (Nat.zero_lt_succ q) hflat)
    (fun q _ => Presentations.Finite.CechKernelQuotients.ProjectiveCech.moduleCech_kernelQuotient_finite R M ℳ d (q + 1)) (fun q _ => hfiber q)
  refine ⟨h.1, fun q => ?_⟩
  by_cases hq : q < Fintype.card σ
  · intro f hf hfc hfd
    have hz : ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R M ℳ d (q + 1 + 1) ⟨f, hf, hfc⟩ = 0 := Subtype.ext hfd
    obtain ⟨g, hg⟩ := (h.2.2 q hq _).mp hz
    refine ⟨g.val, g.property.1, ?_, congrArg Subtype.val hg⟩
    have hdegree : q + 2 - 1 = q + 1 := by omega
    simpa only [hdegree] using g.property.2
  · exact Cech.DimensionShift.ProjectiveCech.moduleCechExactAt_of_bounded R M ℳ d (q + 2) (by omega)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FiberwiseModuleCech.ProjectiveCech
