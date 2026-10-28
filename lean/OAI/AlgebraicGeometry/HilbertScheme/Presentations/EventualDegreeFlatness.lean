import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreeShift
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.AugmentationDegree
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.FlatAugmentation

/-! # Eventual Degree Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech

noncomputable section

/-!
Finitely generated graded polynomial modules over noetherian rings have
flat homogeneous pieces in high degree when their projective chart
degree-zero modules are flat.
-/

open _root_.MvPolynomial DirectSum

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreeShift.GradedModules

universe u v

variable {σ : Type v} [Fintype σ] [LinearOrder σ]
variable (R : Type u) [CommRing R]

omit [Fintype σ] [LinearOrder σ] in
theorem inversionMonomial_singleton (i : σ) : LaurentMonomials.ProjectiveCech.inversionMonomial R {i} = X i := by
  simp [LaurentMonomials.ProjectiveCech.inversionMonomial, LaurentExponents.ProjectiveCech.inversionExponent, X]

omit [Fintype σ] in
theorem inversionMonomial_factor_variable (s : Finset σ) (i : σ) (hi : i ∈ s) :
    LaurentMonomials.ProjectiveCech.inversionMonomial R s = X i * LaurentMonomials.ProjectiveCech.inversionMonomial R (s.erase i) := by
  have h := LaurentRestriction.ProjectiveCech.inversionMonomial_sdiff R (Finset.singleton_subset_iff.mpr hi)
  simpa only [inversionMonomial_singleton, Finset.sdiff_singleton_eq_erase] using h.symm

variable (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

omit [Fintype σ] in
theorem moduleChartDegree_flat_of_zero (s : Finset σ) (hs : s.Nonempty) (d : ℤ) (hd : 0 ≤ d)
    [Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s 0)] :
    Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d) := by
  obtain ⟨i, hi⟩ := hs
  let : Module.Flat R (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) 0) :=
    inferInstanceAs (Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s 0))
  have hflat := Localized.DegreeShift.GradedModules.localizedDegree_flat_of_degree_zero (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s)
    (X i) (LaurentMonomials.ProjectiveCech.inversionMonomial R (s.erase i)) (inversionMonomial_factor_variable R s i hi)
    (isWeightedHomogeneous_X R (fun _ : σ => (1 : ℤ)) i) d.toNat
  let : Module.Flat R (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (d.toNat : ℤ)) := hflat
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofEq _ _
    (congrArg (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ))
      (Int.toNat_of_nonneg hd)).symm)

theorem eventual_degree_flat_of_projective_charts [Nonempty σ] [IsNoetherianRing R]
    [Module.Finite (MvPolynomial σ R) M]
    (hflat : ∀ s : Finset σ, s.Nonempty → Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s 0)) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → Module.Flat R (ℳ d) := by
  obtain ⟨B, hB⟩ := Cech.FlatAugmentation.ProjectiveCech.moduleCech_eventual_augmentation_flat (σ := σ) R M ℳ
  refine ⟨B, fun d hd => ?_⟩
  have hd' : 0 ≤ d := (Int.natCast_nonneg B).trans hd
  let : Module.Flat R (ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 0) := hB d hd (fun s hs => by
    let : Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s 0) := hflat s hs
    exact moduleChartDegree_flat_of_zero R M ℳ s hs d hd')
  exact Module.Flat.of_linearEquiv (Cech.AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := σ) R M ℳ d).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech
