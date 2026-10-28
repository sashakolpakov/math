/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
This file has been modified.
-/
import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import Mathlib.AlgebraicTopology.SingularSet

/-! # Excision Lebesgue -/

namespace OAI.AlgebraicTopology.Singular.ExcisionLebesgue

noncomputable section

/-!

# Lebesgue numbers for pullbacks along singular simplices

For an open cover of a space, every singular simplex pulls the cover back to an open cover of its
compact standard-simplex domain. This file packages the resulting Lebesgue number independently
of the barycentric mesh estimate.
-/

open Set

/-- The pullback of an open cover along one singular simplex has a positive Lebesgue number. -/
theorem singularSimplex_openCover_lebesgueNumber
    {ι : Type} (X : TopCat.{0}) (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ)
    (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ∃ δ > 0, ∀ w : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i, Metric.ball w δ ⊆ (X.toSSetObjEquiv _ x) ⁻¹' U i := by
  let f := X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) x
  obtain ⟨δ, hδ, hLeb⟩ := lebesgue_number_lemma_of_metric
    (s := Set.univ) isCompact_univ
    (fun i ↦ (hUopen i).preimage f.continuous) (by
      intro w _
      rw [Set.mem_iUnion]
      have hw : f w ∈ ⋃ i, U i := by rw [hUcover]; exact Set.mem_univ _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
      exact ⟨i, hi⟩)
  exact ⟨δ, hδ, fun w ↦ hLeb w (Set.mem_univ w)⟩

end

end OAI.AlgebraicTopology.Singular.ExcisionLebesgue
