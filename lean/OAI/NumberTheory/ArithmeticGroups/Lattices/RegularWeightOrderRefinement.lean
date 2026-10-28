import OAI.NumberTheory.ArithmeticGroups.Lattices.DenseRegularSplitElements
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrderedSplitWeightData
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-! # Regular Weight Order Refinement -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RegularWeightOrderRefinement.Construction

noncomputable section

/-! Every weak ordering of weight values can be refined by the
reverse ordering at a regular element separating distinct weights. -/

open scoped Classical

theorem exists_reverse_regular_weight_order
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (w : Fin n → E →ₗ[ℝ] ℝ) (A : E) :
    ∃ H : E, (∀ i, w i H = 0 ↔ w i = 0) ∧
      (∀ i j, w i H = w j H ↔ w i = w j) ∧
      ∀ i j, w i A < w j A → w j H < w i H := by
  let f : Fin n ⊕ (Fin n × Fin n) → E →ₗ[ℝ] ℝ := Sum.elim w (fun p => w p.1 - w p.2)
  let O : Set E := {H | ∀ i j, w i A < w j A → w j H < w i H}
  have hO : IsOpen O := by
    simp only [O, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => isOpen_lt (w j).continuous_of_finiteDimensional
        (w i).continuous_of_finiteDimensional
  have hnO : O.Nonempty := by
    refine ⟨-A, fun i j hij => ?_⟩
    simpa only [map_neg] using neg_lt_neg hij
  obtain ⟨H, hH, hOrder⟩ := (DenseRegularSplitElements.Construction.regular_linear_forms_dense f).exists_mem_open hO hnO
  refine ⟨H, fun i => hH (Sum.inl i), fun i j => ?_, hOrder⟩
  simpa only [f, Sum.elim_inr, LinearMap.sub_apply, sub_eq_zero] using hH (Sum.inr (i, j))

theorem exists_regular_weight_permutation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (w : Fin n → E →ₗ[ℝ] ℝ) (A : E) :
    ∃ (σ : Equiv.Perm (Fin n)) (H : E), (∀ i, w i H = 0 ↔ w i = 0) ∧
      (∀ i j, w i H = w j H ↔ w i = w j) ∧
      Antitone (fun i => w (σ i) H) ∧ Monotone (fun i => w (σ i) A) := by
  obtain ⟨H, hH, hsep, hReverse⟩ := exists_reverse_regular_weight_order w A
  let f := fun i => OrderDual.toDual (w i H)
  let σ := Tuple.sort f
  have hσ : Antitone (fun i => w (σ i) H) := Tuple.monotone_sort f
  refine ⟨σ, H, hH, hsep, hσ, fun i j hij => ?_⟩
  by_contra hn
  exact (not_lt_of_ge (hσ hij)) (hReverse (σ j) (σ i) (lt_of_not_ge hn))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RegularWeightOrderRefinement.Construction
