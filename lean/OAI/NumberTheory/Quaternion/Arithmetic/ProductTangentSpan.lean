import OAI.NumberTheory.Quaternion.Arithmetic.RegularMatrixEmbedding
import Mathlib.Analysis.Calculus.TangentCone.Pi

/-! # Product Tangent Span -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ProductTangentSpan

noncomputable section

/-! The tangent span of a finite product is the product of its factor
tangent spans, over one common scalar field. -/

open scoped Classical
open Set

theorem tangentSpan_pi
    {κ ι : Type*} [Field κ] [Fintype ι] {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module κ (E i)]
    [∀ i, TopologicalSpace (E i)] [∀ i, ContinuousAdd (E i)]
    [∀ i, ContinuousConstSMul κ (E i)]
    (s : ∀ i, Set (E i)) (x : ∀ i, E i) (hx : ∀ i, x i ∈ closure (s i)) :
    Submodule.span κ (tangentConeAt κ (Set.pi univ s) x) =
      Submodule.pi univ (fun i => Submodule.span κ (tangentConeAt κ (s i) (x i))) := by
  let W := Submodule.span κ (tangentConeAt κ (Set.pi univ s) x)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro y hy i _
    have ht := Arithmetic.TangentCone.continuousLinearMap_mapsTo_tangentCone (ContinuousLinearMap.proj i)
      (Set.pi univ s) x hy
    have hs : (ContinuousLinearMap.proj i : (∀ j, E j) →L[κ] E i) '' Set.pi univ s ⊆ s i := by
      rintro z ⟨a, ha, rfl⟩
      exact ha i (mem_univ i)
    exact Submodule.subset_span (tangentConeAt_mono hs ht)
  · intro y hy
    have hsingle (i : ι) :
        Submodule.span κ (tangentConeAt κ (s i) (x i)) ≤ W.comap (LinearMap.single κ E i) := by
      apply Submodule.span_le.mpr
      intro z hz
      exact Submodule.subset_span (mapsTo_tangentConeAt_pi (fun j _ => hx j) hz)
    have hsum : (∑ i, Pi.single i (y i)) ∈ W :=
      W.sum_mem (fun i _ => hsingle i (hy i (mem_univ i)))
    simpa only [LinearMap.sum_single_apply] using hsum

end

end OAI.NumberTheory.Quaternion.Arithmetic.ProductTangentSpan
