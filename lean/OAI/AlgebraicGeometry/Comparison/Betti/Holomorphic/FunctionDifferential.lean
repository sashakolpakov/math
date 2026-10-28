import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ZeroFunctions
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientIndependence
import OAI.AlgebraicGeometry.Comparison.Betti.Pure.OneCovectorDual
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionManifold

/-! # Function Differential -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionDifferential

noncomputable section

/-! The actual holomorphic differential of a function has its ordinary complex cotangent derivative. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] {U : Opens E}

omit [FiniteDimensional ℂ E] in
theorem holomorphicFunctionZeroForm_extension (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯) (x : U) :
    ((Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U 0).symm (DeRhamComplex.inclusion E U 0 (ZeroFunctions.holomorphicFunctionZeroForm f))).extension =ᶠ[𝓝 (x : E)]
      (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (CoefficientMem.openCoefficientExtension U f y)) := by
  filter_upwards [U.isOpen.mem_nhds x.property] with y hy
  rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_apply _ ⟨y, hy⟩, CoefficientMem.openCoefficientExtension_apply U _ ⟨y, hy⟩]
  ext v
  rfl

omit [FiniteDimensional ℂ E] in
theorem holomorphicFunctionDifferential_coefficients
    (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯) (x : U) (v : Fin 1 → E) :
    (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U 1).symm
        (DeRhamComplex.inclusion E U 1 (DeRhamComplex.differential E U 0 (ZeroFunctions.holomorphicFunctionZeroForm f))) x v =
      fderiv ℂ (CoefficientMem.openCoefficientExtension U f) (x : E) (v 0) := by
  rw [DeRhamComplex.inclusion_differential, Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv_symm_d, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_apply,
    (holomorphicFunctionZeroForm_extension f x).extDeriv_eq, extDeriv_constOfIsEmpty]
  have hc : ContDiffOn ℂ ∞ (CoefficientMem.openCoefficientExtension U f) (U : Set E) :=
    (SectionManifold.holomorphicSection_iff_contMDiff U f).mpr f.property
  have hd := (hc.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp)
  rw [hd.fderiv_restrictScalars ℝ]
  rfl

theorem holomorphicFunctionDifferential_dual
    (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯) (x : U) :
    Pure.OneCovectorDual.Holomorphic.pureOneCovectorDualEquiv E
        ((CoefficientIndependence.openFormHolomorphicSectionFunctionEquiv U 1
          (DeRhamComplex.differential E U 0 (ZeroFunctions.holomorphicFunctionZeroForm f))).val x) =
      (fderiv ℂ (CoefficientMem.openCoefficientExtension U f) (x : E)).toLinearMap := by
  apply LinearMap.ext
  intro v
  exact holomorphicFunctionDifferential_coefficients f x (fun _ => v)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionDifferential
