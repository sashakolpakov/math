import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.TensorInclusions
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.TensorAugmentation

/-! # Term Tensor Inclusion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.TermTensorInclusion.ProjectiveCech

noncomputable section

/-! Homogeneous Čech terms split inside the full localized cochains, including after tensoring. -/

open _root_.MvPolynomial DirectSum

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.TensorInclusions.GradedModules

universe u v w t

variable {σ : Type v} [LinearOrder σ]
variable (R : Type u) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

def moduleChartDegreeProjection (s : Finset σ) (d : ℤ) :
    Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s →ₗ[R] Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d := by
  let := Localized.Grading.GradedModules.localizedDegreeDecomposition (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s)
  exact Graded.TensorInclusions.GradedModules.homogeneousComponentProjection (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ)) d

omit [LinearOrder σ] in
theorem moduleChartDegreeProjection_subtype (s : Finset σ) (d : ℤ)
    (x : Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d) : moduleChartDegreeProjection R M ℳ s d x.val = x := by
  let := Localized.Grading.GradedModules.localizedDegreeDecomposition (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ
    (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ) (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s)
  exact DFunLike.congr_fun (Graded.TensorInclusions.GradedModules.homogeneousComponentProjection_subtype
    (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ (LaurentMonomials.ProjectiveCech.inversionMonomial R s) (s.card : ℤ)) d) x

def moduleCechTermProjection (d : ℤ) (q : ℕ) :
    ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M →ₗ[R] ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d q :=
  (ModuleCech.Terms.ProjectiveCech.moduleCechTermEquiv (σ := σ) R M ℳ d q).symm.toLinearMap.comp
    (LinearMap.pi (fun s : {s : Finset σ // s.card = q} =>
      (moduleChartDegreeProjection R M ℳ s.val d).comp (LinearMap.proj s.val)))

omit [LinearOrder σ] in
theorem moduleCechTermProjection_subtype (d : ℤ) (q : ℕ) :
    (moduleCechTermProjection (σ := σ) R M ℳ d q).comp
      (ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d q).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply (ModuleCech.Terms.ProjectiveCech.moduleCechTermEquiv (σ := σ) R M ℳ d q).injective
  change (ModuleCech.Terms.ProjectiveCech.moduleCechTermEquiv (σ := σ) R M ℳ d q)
      ((ModuleCech.Terms.ProjectiveCech.moduleCechTermEquiv (σ := σ) R M ℳ d q).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  funext s
  exact moduleChartDegreeProjection_subtype R M ℳ s.val d ⟨f.val s.val, f.property.1 s.val⟩

omit [LinearOrder σ] in
theorem moduleCechTermSubtype_lTensor_injective (d : ℤ) (q : ℕ)
    (S : Type t) [AddCommGroup S] [Module R S] :
    Function.Injective ((ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d q).subtype.lTensor S) := by
  have h : ((moduleCechTermProjection (σ := σ) R M ℳ d q).lTensor S).comp
      ((ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d q).subtype.lTensor S) = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, moduleCechTermProjection_subtype, LinearMap.lTensor_id]
  intro x y hxy
  have he := congrArg ((moduleCechTermProjection (σ := σ) R M ℳ d q).lTensor S) hxy
  exact (DFunLike.congr_fun h x).symm.trans (he.trans (DFunLike.congr_fun h y))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.TermTensorInclusion.ProjectiveCech
