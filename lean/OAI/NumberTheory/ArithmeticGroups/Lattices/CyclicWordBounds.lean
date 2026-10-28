import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedCyclicWords
import Mathlib.Analysis.Normed.Operator.Basic

/-! # Cyclic Word Bounds -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CyclicWordBounds.Construction

noncomputable section

/-! Word actions preserve integral modules, intertwine representations,
and have a uniform norm bound at bounded word length. -/

open scoped Classical

theorem operatorWord_preserves_submodule
    {k R V ι : Type*} [Field k] [CommRing R] [AddCommGroup V] [Module k V] [Module R V]
    (A : ι → Module.End k V) (Λ : Submodule R V)
    (hA : ∀ i x, x ∈ Λ → A i x ∈ Λ) (w : List ι) (x : V) (hx : x ∈ Λ) :
    BoundedCyclicWords.Construction.operatorWord A w x ∈ Λ := by
  induction w with
  | nil => exact hx
  | cons i w hw => exact hA i _ hw

theorem operatorWord_intertwines
    {k K V W ι : Type*} [Field k] [Field K] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module K W]
    (A : ι → Module.End k V) (B : ι → Module.End K W) (f : V → W)
    (h : ∀ i x, f (A i x) = B i (f x)) (w : List ι) (x : V) :
    f (BoundedCyclicWords.Construction.operatorWord A w x) = BoundedCyclicWords.Construction.operatorWord B w (f x) := by
  induction w with
  | nil => rfl
  | cons i w hw =>
      change f (A i (BoundedCyclicWords.Construction.operatorWord A w x)) = B i (BoundedCyclicWords.Construction.operatorWord B w (f x))
      rw [h, hw]

theorem operatorWord_norm_bound
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ι → E →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (w : List ι) (x : E) :
    ‖BoundedCyclicWords.Construction.operatorWord (fun i => (A i).toLinearMap) w x‖ ≤ C ^ w.length * ‖x‖ := by
  induction w with
  | nil => simp [BoundedCyclicWords.Construction.operatorWord]
  | cons i w hw =>
      change ‖A i (BoundedCyclicWords.Construction.operatorWord (fun i => (A i).toLinearMap) w x)‖ ≤ C ^ (w.length + 1) * ‖x‖
      calc
        _ ≤ ‖A i‖ * ‖BoundedCyclicWords.Construction.operatorWord (fun i => (A i).toLinearMap) w x‖ := (A i).le_opNorm _
        _ ≤ C * (C ^ w.length * ‖x‖) := mul_le_mul (hA i) hw (norm_nonneg _) hC
        _ = _ := by rw [pow_succ]; ring

theorem operatorWord_norm_bound_of_length_le
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ι → E →L[ℝ] E) (C : ℝ) (hC : 1 ≤ C) (hA : ∀ i, ‖A i‖ ≤ C)
    (w : List ι) (r : ℕ) (hw : w.length ≤ r) (x : E) :
    ‖BoundedCyclicWords.Construction.operatorWord (fun i => (A i).toLinearMap) w x‖ ≤ C ^ r * ‖x‖ :=
  (operatorWord_norm_bound A C (by positivity) hA w x).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hw) (norm_nonneg x))

theorem cyclicWordSpan_invariant_of_mem_operator_span
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : ι → Module.End k V) (x : V) (T : Module.End k V)
    (hT : T ∈ Submodule.span k (Set.range A))
    (y : V) (hy : y ∈ BoundedCyclicWords.Construction.cyclicWordSpan A x (Module.finrank k V)) :
    T y ∈ BoundedCyclicWords.Construction.cyclicWordSpan A x (Module.finrank k V) := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
      obtain ⟨i, rfl⟩ := hT
      exact BoundedCyclicWords.Construction.cyclicWordSpan_finrank_invariant A x i y hy
  | zero => simpa only [LinearMap.zero_apply] using (BoundedCyclicWords.Construction.cyclicWordSpan A x (Module.finrank k V)).zero_mem
  | add T S _ _ hT hS =>
      simpa only [LinearMap.add_apply] using (BoundedCyclicWords.Construction.cyclicWordSpan A x (Module.finrank k V)).add_mem hT hS
  | smul c T _ hT =>
      simpa only [LinearMap.smul_apply] using (BoundedCyclicWords.Construction.cyclicWordSpan A x (Module.finrank k V)).smul_mem c hT

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CyclicWordBounds.Construction
