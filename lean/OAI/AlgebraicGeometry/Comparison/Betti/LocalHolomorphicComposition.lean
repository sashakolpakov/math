import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.GermMaps
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Local Holomorphic Composition -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.LocalHolomorphicComposition.Analytic

noncomputable section

/-! Holomorphic maps defined near a point act on the actual holomorphic germ rings. -/

open Set Filter
open scoped _root_.Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem exists_open_differentiableOn_of_contDiffAt {f : E → F} {x : E}
    (hf : ContDiffAt ℂ ω f x) : ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ DifferentiableOn ℂ f U := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ f y :=
    (hf.eventually (by simp)).mono (fun _ h => h.differentiableAt (by simp))
  obtain ⟨U, hU, hopen, hx⟩ := mem_nhds_iff.mp hd
  exact ⟨U, hopen, hx, fun y hy => (hU hy).differentiableWithinAt⟩

def localHolomorphicComposition (f : E → F) (x : E) (hf : ContDiffAt ℂ ω f x) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (f x) →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x where
  toFun a := ⟨GermComposition.AnalyticLocal.germComposition f hf.continuousAt a.val, by
    obtain ⟨v, hva, V, hV, hfxV, hv⟩ := a.property
    obtain ⟨U, hU, hxU, hfd⟩ := exists_open_differentiableOn_of_contDiffAt hf
    have hW : U ∩ f ⁻¹' V ∈ 𝓝 x := inter_mem (hU.mem_nhds hxU) (hf.continuousAt (hV.mem_nhds hfxV))
    obtain ⟨W, hWU, hWopen, hxW⟩ := mem_nhds_iff.mp hW
    refine ⟨v ∘ f, ?_, W, hWopen, hxW, ?_⟩
    · rw [← hva]
      rfl
    · exact hv.comp (hfd.mono (fun y hy => (hWU hy).1)) (fun y hy => (hWU hy).2)⟩
  map_zero' := by apply Subtype.ext; exact map_zero (GermComposition.AnalyticLocal.germComposition f hf.continuousAt)
  map_one' := by apply Subtype.ext; exact map_one (GermComposition.AnalyticLocal.germComposition f hf.continuousAt)
  map_add' a b := by apply Subtype.ext; exact map_add (GermComposition.AnalyticLocal.germComposition f hf.continuousAt) a.val b.val
  map_mul' a b := by apply Subtype.ext; exact map_mul (GermComposition.AnalyticLocal.germComposition f hf.continuousAt) a.val b.val

theorem localHolomorphicComposition_val (f : E → F) (x : E) (hf : ContDiffAt ℂ ω f x)
    (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (f x)) :
    (localHolomorphicComposition f x hf a).val = GermComposition.AnalyticLocal.germComposition f hf.continuousAt a.val := rfl

def localHolomorphicCompositionAt (f : E → F) (x : E) (hf : ContDiffAt ℂ ω f x)
    (y : F) (hxy : f x = y) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  hxy ▸ localHolomorphicComposition f x hf

theorem localHolomorphicCompositionAt_val (f : E → F) (x : E) (hf : ContDiffAt ℂ ω f x)
    (y : F) (hxy : f x = y) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y) :
    (localHolomorphicCompositionAt f x hf y hxy a).val =
      GermComposition.AnalyticLocal.germComposition f (by simpa only [hxy] using
        (show Tendsto f (𝓝 x) (𝓝 (f x)) from hf.continuousAt)) a.val := by
  subst y
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.LocalHolomorphicComposition.Analytic
