import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.GermMaps
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # Holomorphic Germ Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.HolomorphicGermPullback.AnalyticLocal

noncomputable section

/-! A holomorphic partial homeomorphism pulls back actual holomorphic
germs at every point of its source. Only local differentiability is used. -/

open Set Filter
open scoped _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def openHolomorphicGermPullback (e : OpenPartialHomeomorph E F)
    (he : DifferentiableOn ℂ e e.source) (x : E) (hx : x ∈ e.source) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x where
  toFun a := ⟨GermComposition.AnalyticLocal.germComposition e (e.continuousAt hx) a.val, by
    obtain ⟨f, hfa, U, hU, hxU, hf⟩ := a.property
    refine ⟨f ∘ e, ?_, e.source ∩ e ⁻¹' U, e.isOpen_inter_preimage hU, ⟨hx, hxU⟩, ?_⟩
    · rw [← hfa]
      rfl
    · exact hf.comp (he.mono inter_subset_left) (fun _ hy => hy.2)⟩
  map_zero' := by apply Subtype.ext; exact map_zero (GermComposition.AnalyticLocal.germComposition e (e.continuousAt hx))
  map_one' := by apply Subtype.ext; exact map_one (GermComposition.AnalyticLocal.germComposition e (e.continuousAt hx))
  map_add' a b := by apply Subtype.ext; exact map_add (GermComposition.AnalyticLocal.germComposition e (e.continuousAt hx)) a.val b.val
  map_mul' a b := by apply Subtype.ext; exact map_mul (GermComposition.AnalyticLocal.germComposition e (e.continuousAt hx)) a.val b.val

def openHolomorphicGermPullbackAt (e : OpenPartialHomeomorph E F)
    (he : DifferentiableOn ℂ e e.source) (x : E) (hx : x ∈ e.source) (y : F) (hxy : e x = y) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x := hxy ▸ openHolomorphicGermPullback e he x hx

theorem openHolomorphicGermPullbackAt_val (e : OpenPartialHomeomorph E F)
    (he : DifferentiableOn ℂ e e.source) (x : E) (hx : x ∈ e.source) (y : F) (hxy : e x = y)
    (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y) : (openHolomorphicGermPullbackAt e he x hx y hxy a).val =
      GermComposition.AnalyticLocal.germComposition e (by
        simpa only [hxy] using (show Tendsto e (𝓝 x) (𝓝 (e x)) from e.continuousAt hx)) a.val := by
  subst y
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.HolomorphicGermPullback.AnalyticLocal
