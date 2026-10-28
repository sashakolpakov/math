import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Continuous

/-! # Gram Schmidt Continuity -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.GramSchmidtContinuity.Construction

noncomputable section

/-! Gram--Schmidt varies continuously in a linearly independent
finite family of vectors. -/

open InnerProductSpace
open scoped Classical

theorem gramSchmidt_continuous_family
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (f : X → Fin n → E) (hf : ∀ i, Continuous (fun x => f x i))
    (hli : ∀ x, LinearIndependent ℝ (f x)) (i : Fin n) :
    Continuous (fun x => gramSchmidt ℝ (f x) i) := by
  induction i using (wellFounded_lt (α := Fin n)).induction with
  | h i ih =>
    have hrec (x : X) : gramSchmidt ℝ (f x) i = f x i -
        ∑ j ∈ Finset.Iio i,
          (inner ℝ (gramSchmidt ℝ (f x) j) (f x i) / ‖gramSchmidt ℝ (f x) j‖ ^ 2) •
            gramSchmidt ℝ (f x) j := by
      rw [eq_sub_iff_add_eq]
      exact (gramSchmidt_def'' ℝ (f x) i).symm
    simp_rw [hrec]
    apply (hf i).sub
    apply continuous_finsetSum
    intro j hj
    have hc := ih j (Finset.mem_Iio.mp hj)
    exact ((hc.inner (hf i)).div (hc.norm.pow 2) (fun x =>
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero j (hli x))))).smul hc

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.GramSchmidtContinuity.Construction
