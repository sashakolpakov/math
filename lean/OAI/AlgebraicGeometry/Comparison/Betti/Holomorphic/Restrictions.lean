import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionFrames

/-! # Restrictions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Restrictions

noncomputable section

/-! Actual open restriction for holomorphic functions and vector-valued sections. -/

open _root_.TopologicalSpace
open scoped ContDiff

variable {E F ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {U V : Opens E}

def holomorphicSectionRestrict (h : V ≤ U) :
    CoefficientMem.holomorphicSections U F →ₗ[ℂ] CoefficientMem.holomorphicSections V F where
  toFun f := ⟨fun x => f.val (Opens.inclusion h x), by
    apply (f.property.mono h).congr
    intro x hx
    rw [CoefficientMem.openCoefficientExtension_apply V _ ⟨x, hx⟩,
      CoefficientMem.openCoefficientExtension_apply U _ ⟨x, h hx⟩]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def holomorphicFunctionRestrict (h : V ≤ U) : FunctionPure.holomorphicFunctions U →ₐ[ℂ] FunctionPure.holomorphicFunctions V where
  toFun f := ⟨(holomorphicSectionRestrict (F := ℂ) h ⟨f.val, f.property⟩).val,
    (holomorphicSectionRestrict (F := ℂ) h ⟨f.val, f.property⟩).property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

theorem holomorphicSectionRestrict_function_smul (h : V ≤ U)
    (f : FunctionPure.holomorphicFunctions U) (a : CoefficientMem.holomorphicSections U F) :
    holomorphicSectionRestrict h (f • a) =
      holomorphicFunctionRestrict h f • holomorphicSectionRestrict h a := rfl

theorem holomorphicSectionsBasisEquiv_restrict [Fintype ι] (b : Module.Basis ι ℂ F)
    (h : V ≤ U) (a : CoefficientMem.holomorphicSections U F) :
    SectionFrames.holomorphicSectionsBasisEquiv V b (holomorphicSectionRestrict h a) =
      fun i => holomorphicFunctionRestrict h (SectionFrames.holomorphicSectionsBasisEquiv U b a i) := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Restrictions
