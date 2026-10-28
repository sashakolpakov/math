import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Complex.Basic

/-! # Split Submersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SplitSubmersion.Constructions

noncomputable section

/-! A normal submersion combined with an equation that is a submersion
along its source is a submersion in the full ambient manifold. -/

open scoped _root_.Manifold

variable {D E F G : Type}
  [NormedAddCommGroup D] [NormedSpace ℂ D] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem prod_surjective (L : E →L[ℂ] F) (K : E →L[ℂ] G) (I : D →L[ℂ] E)
    (hL : Function.Surjective L) (hLI : L.comp I = 0) (hKI : Function.Surjective (K.comp I)) :
    Function.Surjective (L.prod K) := by
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := hL a
  obtain ⟨y, hy⟩ := hKI (b - K x)
  refine ⟨x + I y, Prod.ext ?_ ?_⟩
  · change L (x + I y) = a
    have hz : L (I y) = 0 := congrArg (fun H : D →L[ℂ] F => H y) hLI
    rw [map_add, hx, hz, add_zero]
  · change K (x + I y) = b
    change K (I y) = b - K x at hy
    rw [map_add, hy, add_sub_cancel]

variable {S M : Type} [TopologicalSpace S] [ChartedSpace D S]
  [TopologicalSpace M] [ChartedSpace E M]

theorem mfderiv_pair_surjective (i : S → M) (n : M → F) (h : M → G) (x : S)
    (hi : MDifferentiableAt 𝓘(ℂ, D) 𝓘(ℂ, E) i x)
    (hn : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) n (i x))
    (hh : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, G) h (i x))
    (hn0 : n ∘ i = fun _ => 0)
    (hns : Function.Surjective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) n (i x)))
    (hhs : Function.Surjective (mfderiv 𝓘(ℂ, D) 𝓘(ℂ, G) (h ∘ i) x)) :
    Function.Surjective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F × G) (fun y => (n y, h y)) (i x)) := by
  have hnc := mfderiv_comp x hn hi
  rw [hn0, mfderiv_const] at hnc
  rw [mfderiv_comp x hh hi] at hhs
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod, mfderiv_prodMk hn hh]
  exact prod_surjective (D := D) (E := E) (F := F) (G := G) _ _ _ hns hnc.symm hhs

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SplitSubmersion.Constructions
