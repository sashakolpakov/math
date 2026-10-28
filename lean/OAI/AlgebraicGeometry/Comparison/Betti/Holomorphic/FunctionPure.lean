import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientMem
import Mathlib.Algebra.Module.RingHom

/-! # Function Pure -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionPure

noncomputable section

section

/-! The actual holomorphic function algebra acts pointwise on holomorphic vector-valued sections. -/

open _root_.TopologicalSpace
open scoped ContDiff

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def holomorphicFunctions (U : Opens E) : Subalgebra ℂ (U → ℂ) where
  carrier := CoefficientMem.holomorphicSections U ℂ
  zero_mem' := (CoefficientMem.holomorphicSections U ℂ).zero_mem
  add_mem' := (CoefficientMem.holomorphicSections U ℂ).add_mem
  one_mem' := by
    apply contDiffOn_const.congr
    intro x hx
    exact CoefficientMem.openCoefficientExtension_apply U (1 : U → ℂ) ⟨x, hx⟩
  mul_mem' := by
    intro f g hf hg
    change ContDiffOn ℂ ∞ (CoefficientMem.openCoefficientExtension U f) (U : Set E) at hf
    change ContDiffOn ℂ ∞ (CoefficientMem.openCoefficientExtension U g) (U : Set E) at hg
    apply (hf.mul hg).congr
    intro x hx
    simp only [CoefficientMem.openCoefficientExtension_apply U _ ⟨x, hx⟩, Pi.mul_apply]
  algebraMap_mem' c := by
    apply contDiffOn_const.congr
    intro x hx
    exact CoefficientMem.openCoefficientExtension_apply U (fun _ : U => c) ⟨x, hx⟩

instance holomorphicFunctionsRawModule (U : Opens E) :
    Module (holomorphicFunctions U) (U → F) :=
  Module.compHom (U → F) (holomorphicFunctions U).val.toRingHom

instance holomorphicSectionsFunctionSMul (U : Opens E) :
    SMul (holomorphicFunctions U) (CoefficientMem.holomorphicSections U F) where
  smul f s := ⟨fun x => f.val x • s.val x, by
    have hf : ContDiffOn ℂ ∞ (CoefficientMem.openCoefficientExtension U f.val) (U : Set E) := f.property
    have hs : ContDiffOn ℂ ∞ (CoefficientMem.openCoefficientExtension U s.val) (U : Set E) := s.property
    apply (hf.smul hs).congr
    intro x hx
    change CoefficientMem.openCoefficientExtension U (fun y => f.val y • s.val y) x =
      CoefficientMem.openCoefficientExtension U f.val x • CoefficientMem.openCoefficientExtension U s.val x
    simp only [CoefficientMem.openCoefficientExtension_apply U _ ⟨x, hx⟩]⟩

instance holomorphicSectionsFunctionModule (U : Opens E) :
    Module (holomorphicFunctions U) (CoefficientMem.holomorphicSections U F) :=
  Function.Injective.module (holomorphicFunctions U)
    (CoefficientMem.holomorphicSections U F).subtype.toAddMonoidHom Subtype.val_injective (fun _ _ => rfl)

theorem holomorphicSections_function_smul (U : Opens E) (f : holomorphicFunctions U)
    (s : CoefficientMem.holomorphicSections U F) (x : U) : (f • s).val x = f.val x • s.val x := rfl

end

section

/-! Holomorphic functions act on the genuine pure holomorphic coefficient fields by pointwise multiplication. -/

open _root_.TopologicalSpace
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

instance holomorphicCoefficientFunctionSMul (U : Opens E) (n : ℕ) :
    SMul (holomorphicFunctions U) (CoefficientMem.holomorphicOpenCoefficients U n) where
  smul f a := ⟨fun x => f.val x • a.val x, by
    constructor
    · intro x
      exact (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0).smul_mem (f.val x) (a.property.1 x)
    · have hf : ContDiffOn ℂ ∞ (CoefficientMem.openCoefficientExtension U f.val) (U : Set E) := f.property
      have ha := a.property.2
      apply (hf.smul ha).congr
      intro x hx
      change Analysis.DifferentialForms.Manifold.OpenD.openFormExtension U (fun y => f.val y • a.val y) x =
        CoefficientMem.openCoefficientExtension U f.val x • Analysis.DifferentialForms.Manifold.OpenD.openFormExtension U a.val x
      simp only [CoefficientMem.openCoefficientExtension_apply U _ ⟨x, hx⟩,
        Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_apply U _ ⟨x, hx⟩]⟩

instance holomorphicCoefficientFunctionModule (U : Opens E) (n : ℕ) :
    Module (holomorphicFunctions U) (CoefficientMem.holomorphicOpenCoefficients U n) :=
  Function.Injective.module (holomorphicFunctions U)
    (CoefficientMem.holomorphicOpenCoefficients U n).subtype.toAddMonoidHom Subtype.val_injective (fun _ _ => rfl)

omit [IsScalarTower ℝ ℂ E] in
theorem holomorphicCoefficients_function_smul (U : Opens E) (n : ℕ) (f : holomorphicFunctions U)
    (a : CoefficientMem.holomorphicOpenCoefficients U n) (x : U) :
    (f • a).val x = f.val x • a.val x := rfl

end

/-! Pure holomorphic coefficient fields are precisely holomorphic sections of the genuine pure covector space. -/

open _root_.TopologicalSpace
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

def holomorphicPureSectionEquiv (U : Opens E) (n : ℕ) :
    CoefficientMem.holomorphicOpenCoefficients U n ≃ₗ[holomorphicFunctions U]
      CoefficientMem.holomorphicSections U (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) where
  toFun a := ⟨fun x => ⟨a.val x, a.property.1 x⟩, by
    let b := Module.finBasis ℂ E
    have hL : ContDiff ℂ ∞ (Pure.CovectorReconstruction.Holomorphic.pureCovectorProjection b n) := ContinuousLinearMap.contDiff _
    apply (hL.comp_contDiffOn a.property.2).congr
    intro x hx
    rw [CoefficientMem.openCoefficientExtension_apply U _ ⟨x, hx⟩]
    apply Subtype.ext
    change a.val ⟨x, hx⟩ = (Pure.CovectorReconstruction.Holomorphic.pureCovectorProjection b n (Analysis.DifferentialForms.Manifold.OpenD.openFormExtension U a.val x)).val
    rw [Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_apply U _ ⟨x, hx⟩]
    exact (Pure.CovectorReconstruction.Holomorphic.pureCovectorProjection_eq_self b n _ (a.property.1 ⟨x, hx⟩)).symm⟩
  invFun a := ⟨fun x => (a.val x).val, by
    constructor
    · intro x
      exact (a.val x).property
    · have hL : ContDiff ℂ ∞ (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0).subtypeL :=
        ContinuousLinearMap.contDiff _
      apply (hL.comp_contDiffOn a.property).congr
      intro x hx
      simp only [Function.comp_apply, Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_apply U _ ⟨x, hx⟩,
        CoefficientMem.openCoefficientExtension_apply U _ ⟨x, hx⟩]
      rfl⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv a := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    rfl
  map_add' a b := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    rfl
  map_smul' f a := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    rfl

theorem holomorphicPureSectionEquiv_apply (U : Opens E) (n : ℕ)
    (a : CoefficientMem.holomorphicOpenCoefficients U n) (x : U) :
    ((holomorphicPureSectionEquiv U n a).val x).val = a.val x := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionPure
