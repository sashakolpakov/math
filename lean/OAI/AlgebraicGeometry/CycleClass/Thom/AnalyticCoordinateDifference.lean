import OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Analytic Coordinate Difference -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticCoordinateDifference.Constructions

noncomputable section

/-! The difference of two copies of a local analytic coordinate map
is submersive. On any domain where the coordinates are injective, its
zero set is exactly the diagonal. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

local instance (priority := low) : ChartedSpace (E × E) (M × M) := prodChartedSpace E M E M
local instance : IsManifold 𝓘(ℂ, E × E) ω (M × M) := Product.Immersion.Constructions.productModel_isManifold

def coordinateDifference (n : ℕ) (c : M → (Fin n → ℂ)) (z : M × M) : Fin n → ℂ := c z.1 - c z.2

variable (n : ℕ) (c : M → (Fin n → ℂ)) (hc : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ω c)

include hc in
omit [IsManifold 𝓘(ℂ, E) ω M] in
theorem coordinateDifference_analytic :
    ContMDiff 𝓘(ℂ, E × E) 𝓘(ℂ, Fin n → ℂ) ω (coordinateDifference n c) := by
  rw [modelWithCornersSelf_prod]
  exact (hc.comp contMDiff_fst).sub (hc.comp contMDiff_snd)

include hc in
omit [IsManifold 𝓘(ℂ, E) ω M] in
theorem coordinateDifference_submersion
    (hs : ∀ x, Function.Surjective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) c x)) (z : M × M) :
    Function.Surjective (mfderiv 𝓘(ℂ, E × E) 𝓘(ℂ, Fin n → ℂ) (coordinateDifference n c) z) := by
  rcases z with ⟨x, y⟩
  let i : M → M × M := fun a => (a, y)
  have hi : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E × E) ω i := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_id.prodMk contMDiff_const
  have he : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) (coordinateDifference n c ∘ i) x =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) c x := by
    change mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) (c - fun _ => c y) x = _
    rw [mfderiv_sub (hc.mdifferentiableAt (by simp)) mdifferentiableAt_const, mfderiv_const, sub_zero]
  have h := mfderiv_comp x ((coordinateDifference_analytic n c hc).mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  have heq := h.symm.trans he
  intro w
  obtain ⟨v, hv⟩ := hs x w
  refine ⟨mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E × E) i x v, ?_⟩
  exact (congrArg (fun L => L v) heq).trans hv

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] in
theorem coordinateDifference_zero_iff (U : Set M) (hi : Set.InjOn c U)
    (z : M × M) (hz : z ∈ U ×ˢ U) : coordinateDifference n c z = 0 ↔ z.1 = z.2 := by
  change c z.1 - c z.2 = 0 ↔ z.1 = z.2
  exact sub_eq_zero.trans ⟨fun h => hi hz.1 hz.2 h, fun h => congrArg c h⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticCoordinateDifference.Constructions
