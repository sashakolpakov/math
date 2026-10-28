import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionPure

/-! # Section Frames -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionFrames

noncomputable section

/-! A finite covector basis gives a free module of holomorphic sections over actual holomorphic functions. -/

open _root_.TopologicalSpace
open scoped ContDiff

variable {E F G ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

def holomorphicSectionFunctionMap (U : Opens E) (L : F →L[ℂ] G) :
    CoefficientMem.holomorphicSections U F →ₗ[FunctionPure.holomorphicFunctions U] CoefficientMem.holomorphicSections U G where
  toFun := CoefficientMem.holomorphicSectionMap U L
  map_add' := (CoefficientMem.holomorphicSectionMap U L).map_add
  map_smul' f s := by
    apply Subtype.ext
    funext x
    exact L.map_smul (f.val x) (s.val x)

def holomorphicSectionFunctionEquiv (U : Opens E) (L : F ≃L[ℂ] G) :
    CoefficientMem.holomorphicSections U F ≃ₗ[FunctionPure.holomorphicFunctions U] CoefficientMem.holomorphicSections U G where
  toLinearMap := holomorphicSectionFunctionMap U L.toContinuousLinearMap
  invFun := holomorphicSectionFunctionMap U L.symm.toContinuousLinearMap
  left_inv := (CoefficientMem.holomorphicSectionEquiv U L).left_inv
  right_inv := (CoefficientMem.holomorphicSectionEquiv U L).right_inv

def holomorphicPiSectionsEquiv (U : Opens E) (ι : Type) [Fintype ι] :
    CoefficientMem.holomorphicSections U (ι → ℂ) ≃ₗ[FunctionPure.holomorphicFunctions U] (ι → FunctionPure.holomorphicFunctions U) where
  toFun f i := ⟨fun x => f.val x i, by
    have hs := contDiffOn_pi.mp f.property i
    apply hs.congr
    intro x hx
    simp only [CoefficientMem.openCoefficientExtension_apply U _ ⟨x, hx⟩]⟩
  invFun f := ⟨fun x i => (f i).val x, by
    apply contDiffOn_pi.mpr
    intro i
    have hs : ContDiffOn ℂ ∞ (CoefficientMem.openCoefficientExtension U (f i).val) (U : Set E) := (f i).property
    apply hs.congr
    intro x hx
    simp only [CoefficientMem.openCoefficientExtension_apply U _ ⟨x, hx⟩]⟩
  left_inv f := by
    apply Subtype.ext
    funext x i
    rfl
  right_inv f := by
    funext i
    apply Subtype.ext
    funext x
    rfl
  map_add' f g := by
    funext i
    apply Subtype.ext
    funext x
    rfl
  map_smul' c f := by
    funext i
    apply Subtype.ext
    funext x
    rfl

def holomorphicSectionsBasisEquiv (U : Opens E) [Fintype ι] (b : Module.Basis ι ℂ F) :
    CoefficientMem.holomorphicSections U F ≃ₗ[FunctionPure.holomorphicFunctions U] (ι → FunctionPure.holomorphicFunctions U) :=
  (holomorphicSectionFunctionEquiv U b.equivFunL).trans (holomorphicPiSectionsEquiv U ι)

def holomorphicSectionsBasis (U : Opens E) [Fintype ι] (b : Module.Basis ι ℂ F) :
    Module.Basis ι (FunctionPure.holomorphicFunctions U) (CoefficientMem.holomorphicSections U F) :=
  Module.Basis.ofEquivFun (holomorphicSectionsBasisEquiv U b)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionFrames
