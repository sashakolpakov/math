import Mathlib.LinearAlgebra.Pi

/-! # Product Local Span -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ProductLocalSpan

noncomputable section

/-! A common-field submodule contains a product of local spans once
it contains all locally scaled generators supported in one factor. -/

open scoped Classical

theorem product_mem_of_local_spans
    {κ ι : Type*} [Field κ] [Fintype ι] {K A : ι → Type*}
    [∀ i, Field (K i)] [∀ i, AddCommGroup (A i)] [∀ i, Module (K i) (A i)]
    [∀ i, Module κ (A i)]
    (W : Submodule κ (∀ i, A i)) (s : ∀ i, Set (A i))
    (hs : ∀ i, ∀ a ∈ s i, ∀ c : K i, LinearMap.single κ A i (c • a) ∈ W)
    (x : ∀ i, A i) (hx : ∀ i, x i ∈ Submodule.span (K i) (s i)) : x ∈ W := by
  have hspan (i : ι) : ∀ a ∈ Submodule.span (K i) (s i),
      ∀ c : K i, LinearMap.single κ A i (c • a) ∈ W := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact hs i a ha
    | zero => intro c; simpa only [smul_zero, map_zero] using W.zero_mem
    | add a b _ _ ha hb =>
      intro c
      rw [smul_add, map_add]
      exact W.add_mem (ha c) (hb c)
    | smul c a _ ha =>
      intro d
      simpa only [smul_smul] using ha (d * c)
  have hsum : (∑ i, LinearMap.single κ A i (x i)) ∈ W := by
    apply W.sum_mem
    intro i _
    simpa only [one_smul] using hspan i (x i) (hx i) 1
  have he : (∑ i, LinearMap.single κ A i (x i)) = x := by
    change (∑ i, Pi.single i (x i)) = x
    exact Finset.univ_sum_single x
  exact he ▸ hsum

end

end OAI.NumberTheory.Quaternion.Arithmetic.ProductLocalSpan
