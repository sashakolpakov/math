import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Finset.NoncommProd

/-! # Product Curve Derivative -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ProductCurveDerivative

noncomputable section

/-! The derivative at the identity of an ordered finite product is
the sum of the derivatives. Commutativity of the ambient algebra is
not needed. -/

open scoped Classical

variable {K A ι : Type*} [NontriviallyNormedField K] [NormedRing A] [NormedAlgebra K A]

theorem list_curve_prod_hasDerivAt_one (l : List ι) (f : ι → K → A) (d : ι → A) (x : K)
    (hf : ∀ i ∈ l, HasDerivAt (f i) (d i) x) (h₁ : ∀ i ∈ l, f i x = 1) :
    HasDerivAt (fun t => (l.map (fun i => f i t)).prod) (l.map d).sum x := by
  induction l with
  | nil => simpa only [List.map_nil, List.prod_nil, List.sum_nil] using hasDerivAt_const x (1 : A)
  | cons i l ih =>
    have hd := (hf i (by simp)).fun_mul (ih (fun j hj => hf j (by simp [hj]))
      (fun j hj => h₁ j (by simp [hj])))
    have hp : (l.map (fun j => f j x)).prod = 1 := by
      apply List.prod_eq_one
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact h₁ j (by simp [hj])
    simpa only [List.map_cons, List.prod_cons, List.sum_cons, h₁ i (by simp), hp,
      mul_one, one_mul] using hd

variable {M : Type*} [Monoid M]

theorem list_prod_eq_noncommProd {l : List ι} (s : Finset ι) (hl : (l : Multiset ι) = s.val)
    (f : ι → M) (hc : ∀ i j, Commute (f i) (f j)) :
    (l.map f).prod = s.noncommProd f (fun _ _ _ _ _ => hc _ _) := by
  unfold Finset.noncommProd
  simp only [← hl, Multiset.map_coe, Multiset.noncommProd_coe]

end

end OAI.NumberTheory.Quaternion.Arithmetic.ProductCurveDerivative
