import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionMultiplication

/-! # Manifold Holomorphic Modules -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModules

noncomputable section

/-! Actual holomorphic forms are modules over standard holomorphic functions, compatibly with actual pullback. -/

open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

instance manifoldFormsFunctionSMul (n : ℕ) :
    SMul C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ), ℂ⟯ (Holomorphic.DeRhamComplex.forms E M n) where
  smul f a := Holomorphic.FunctionMultiplication.multiplyByHolomorphicFunction f n a

instance manifoldFormsFunctionModule (n : ℕ) :
    Module C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ), ℂ⟯ (Holomorphic.DeRhamComplex.forms E M n) where
  one_smul a := by
    apply Holomorphic.HolomorphicPullback.inclusion_injective n
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    exact one_smul ℂ (Holomorphic.DeRhamComplex.inclusion E M n a x)
  mul_smul f g a := by
    apply Holomorphic.HolomorphicPullback.inclusion_injective n
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    exact mul_smul (f x) (g x) (Holomorphic.DeRhamComplex.inclusion E M n a x)
  smul_add f a b := by
    apply Holomorphic.HolomorphicPullback.inclusion_injective n
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    exact smul_add (f x) (Holomorphic.DeRhamComplex.inclusion E M n a x) (Holomorphic.DeRhamComplex.inclusion E M n b x)
  add_smul f g a := by
    apply Holomorphic.HolomorphicPullback.inclusion_injective n
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    exact add_smul (f x) (g x) (Holomorphic.DeRhamComplex.inclusion E M n a x)
  zero_smul a := by
    apply Holomorphic.HolomorphicPullback.inclusion_injective n
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    exact zero_smul ℂ (Holomorphic.DeRhamComplex.inclusion E M n a x)
  smul_zero f := by
    apply Holomorphic.HolomorphicPullback.inclusion_injective n
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    change f x • (0 : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) = 0
    exact _root_.smul_zero (A := Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (f x)

theorem manifoldFormsFunctionModule_apply (n : ℕ) (f : C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ), ℂ⟯)
    (a : Holomorphic.DeRhamComplex.forms E M n) (x : M) : Holomorphic.DeRhamComplex.inclusion E M n (f • a) x = f x • Holomorphic.DeRhamComplex.inclusion E M n a x := rfl

variable {F N : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ∞ N]

theorem pullback_function_smul (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ g)
    (n : ℕ) (f : C^∞⟮𝓘(ℂ, F), N; 𝓘(ℂ), ℂ⟯) (a : Holomorphic.DeRhamComplex.forms F N n) :
    Holomorphic.HolomorphicPullback.pullback g hg n (f • a) = f.comp ⟨g, hg⟩ • Holomorphic.HolomorphicPullback.pullback g hg n a := by
  apply Holomorphic.HolomorphicPullback.inclusion_injective n
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicModules
