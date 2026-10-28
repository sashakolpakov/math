import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientMem
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-! # Section Manifold -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionManifold

noncomputable section

/-! Actual coefficient holomorphicity agrees with the standard complex smooth-map predicate. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem holomorphicSection_iff_contMDiff (U : Opens E) (f : U → F) :
    f ∈ CoefficientMem.holomorphicSections U F ↔ ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f := by
  constructor
  · intro hf x
    have heq : (fun y : U => CoefficientMem.openCoefficientExtension U f y) = f :=
      funext (CoefficientMem.openCoefficientExtension_apply U f)
    rw [← heq]
    exact (hf.contDiffAt (U.isOpen.mem_nhds x.property)).contMDiffAt.comp x
      (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (n := ∞) x)
  · intro hf y hy
    let x : U := ⟨y, hy⟩
    have hyc : y ∈ (chartAt E x).target := by
      rw [Analysis.DifferentialForms.Manifold.OpenEquivalence.open_chartAt_target]
      exact hy
    have hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (chartAt E x).symm y :=
      contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (chart_mem_atlas E x)) hyc
    have hs : ContDiffAt ℂ ∞ (fun z => f ((chartAt E x).symm z)) y :=
      ((hf _).comp y hi).contDiffAt
    have heq : CoefficientMem.openCoefficientExtension U f =ᶠ[𝓝 y]
        (fun z => f ((chartAt E x).symm z)) := by
      filter_upwards [U.isOpen.mem_nhds hy] with z hz
      rw [CoefficientMem.openCoefficientExtension_apply U f ⟨z, hz⟩,
        Analysis.DifferentialForms.Manifold.OpenEquivalence.openChart_symm_apply _ (chart_mem_atlas E x) hz]
    exact (hs.congr_of_eventuallyEq heq).contDiffWithinAt

def holomorphicSectionContMDiffEquiv (U : Opens E) :
    CoefficientMem.holomorphicSections U F ≃ₗ[ℂ] C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ, F), F⟯ where
  toFun f := ⟨f.val, (holomorphicSection_iff_contMDiff U f.val).mp f.property⟩
  invFun f := ⟨f.val, (holomorphicSection_iff_contMDiff U f.val).mpr f.property⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := by apply ContMDiffMap.ext; intro x; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionManifold
