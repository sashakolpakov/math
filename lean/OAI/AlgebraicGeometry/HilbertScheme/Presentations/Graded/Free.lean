import OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedFreeModules
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleGenerators
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.SubmoduleGrading
import Mathlib.RingTheory.Polynomial.Basic

/-! # Free -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Free.GradedModules

noncomputable section

/-!
Finite homogeneous generators give actual weighted free surjections.
Over a noetherian coefficient ring their kernels again have finite
homogeneous generators.
-/

open _root_.MvPolynomial DirectSum

universe u v w

variable {σ : Type u} (R : Type v) [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)

structure HomogeneousFreeCover where
  generators : Finset M
  degree : generators → ℤ
  homogeneous : ∀ i : generators, i.val ∈ ℳ (degree i)
  span_eq_top : Submodule.span (MvPolynomial σ R) (generators : Set M) = ⊤

variable [Decomposition ℳ] [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

def homogeneousFreeCover [Module.Finite (MvPolynomial σ R) M] :
    HomogeneousFreeCover (σ := σ) R ℳ := by
  classical
  apply Classical.choice
  have htop : (⊤ : Submodule (MvPolynomial σ R) M).IsHomogeneous ℳ := fun _ _ _ => trivial
  obtain ⟨s, hspan, hs⟩ := ModuleGenerators.GradedModules.exists_finite_homogeneous_generators ℳ
    (⊤ : Submodule (MvPolynomial σ R) M) htop Module.Finite.fg_top
  choose d hd using (fun i : s => hs i.val i.property)
  exact ⟨{ generators := s, degree := d, homogeneous := hd, span_eq_top := hspan }⟩

namespace HomogeneousFreeCover

variable (C : HomogeneousFreeCover (σ := σ) R ℳ)

abbrev FreeModule := C.generators →₀ MvPolynomial σ R

def map : C.FreeModule →ₗ[MvPolynomial σ R] M :=
  Finsupp.linearCombination (MvPolynomial σ R) Subtype.val

omit [IsScalarTower R (MvPolynomial σ R) M] [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ] in
theorem map_surjective : Function.Surjective (map R ℳ C) := by
  rw [← LinearMap.range_eq_top, map, Finsupp.range_linearCombination]
  rw [Subtype.range_coe_subtype]
  exact C.span_eq_top

omit [IsScalarTower R (MvPolynomial σ R) M] [Decomposition ℳ] in
theorem map_homogeneous (d : ℤ) (f : C.FreeModule)
    (hf : f ∈ WeightedFreeModules.GradedModules.weightedFreeGrading R C.degree d) : (map R ℳ C) f ∈ ℳ d :=
  WeightedFreeModules.GradedModules.weightedFree_linearCombination_homogeneous R ℳ C.degree Subtype.val C.homogeneous d f hf

omit [IsScalarTower R (MvPolynomial σ R) M] in
theorem kernel_homogeneous : (map R ℳ C).ker.IsHomogeneous (WeightedFreeModules.GradedModules.weightedFreeGrading R C.degree) :=
  ModuleGenerators.GradedModules.homogeneous_kernel (WeightedFreeModules.GradedModules.weightedFreeGrading R C.degree) ℳ (map R ℳ C) (map_homogeneous R ℳ C)

omit [IsScalarTower R (MvPolynomial σ R) M] in
theorem kernel_finite_homogeneous_generators [Finite σ] [IsNoetherianRing R] :
    ∃ s : Finset C.FreeModule,
      Submodule.span (MvPolynomial σ R) (s : Set C.FreeModule) = (map R ℳ C).ker ∧
      ∀ x ∈ s, ∃ d, x ∈ WeightedFreeModules.GradedModules.weightedFreeGrading R C.degree d :=
  ModuleGenerators.GradedModules.noetherian_homogeneous_generators (WeightedFreeModules.GradedModules.weightedFreeGrading R C.degree) (map R ℳ C).ker C.kernel_homogeneous

def kernelGrading (d : ℤ) : Submodule R (map R ℳ C).ker :=
  (WeightedFreeModules.GradedModules.weightedFreeGrading R C.degree d).comap ((map R ℳ C).ker.subtype.restrictScalars R)

instance kernelDecomposition : Decomposition C.kernelGrading :=
  Homogeneous.SubmoduleGrading.GradedModules.homogeneousSubmoduleDecomposition (WeightedFreeModules.GradedModules.weightedFreeGrading R C.degree)
    ((map R ℳ C).ker.restrictScalars R) C.kernel_homogeneous

instance kernelGradedSMul :
    SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) C.kernelGrading where
  smul_mem := by
    intro n d a x ha hx
    change x.val ∈ WeightedFreeModules.GradedModules.weightedFreeGrading R C.degree d at hx
    change a • x.val ∈ WeightedFreeModules.GradedModules.weightedFreeGrading R C.degree (n + d)
    exact SetLike.GradedSMul.smul_mem ha hx

instance kernelFinite [Finite σ] [IsNoetherianRing R] :
    Module.Finite (MvPolynomial σ R) (map R ℳ C).ker := inferInstance

end HomogeneousFreeCover

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Free.GradedModules
