import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Data.Finset.Lattice.Fold

/-! # Tensor Sequence Lifts -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.TensorSequenceLifts

noncomputable section

/-! # Tensor elements and finite families lift to one stage of an algebra sequence -/

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A : ℕ → Type*) [∀ k, CommRing (A k)] [∀ k, Algebra R (A k)]
  (f : ∀ k, A k →ₐ[R] S) (g : ∀ i j, i ≤ j → A i →ₐ[R] A j)
  (hg : ∀ i j h x, f j (g i j h x) = f i x)

def tensorMap (k : ℕ) : A k ⊗[R] A k →ₐ[R] S ⊗[R] S :=
  Algebra.TensorProduct.map (f k) (f k)

include hg in
theorem tensor_transition (i j : ℕ) (h : i ≤ j) (x : A i ⊗[R] A i) :
    tensorMap A f j (Algebra.TensorProduct.map (g i j h) (g i j h) x) = tensorMap A f i x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp only [tensorMap, Algebra.TensorProduct.map_tmul, hg]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (hs : ∀ x : S, ∃ k, ∃ y : A k, f k y = x)

include hg hs in
theorem tensor_exists (x : S ⊗[R] S) : ∃ k, ∃ y : A k ⊗[R] A k, tensorMap A f k y = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      obtain ⟨i, a', ha⟩ := hs a
      obtain ⟨j, b', hb⟩ := hs b
      refine ⟨max i j, g i (max i j) (le_max_left _ _) a' ⊗ₜ[R]
        g j (max i j) (le_max_right _ _) b', ?_⟩
      simp only [tensorMap, Algebra.TensorProduct.map_tmul, hg, ha, hb]
  | add x y hx hy =>
      obtain ⟨i, x', hx'⟩ := hx
      obtain ⟨j, y', hy'⟩ := hy
      refine ⟨max i j,
        Algebra.TensorProduct.map (g i (max i j) (le_max_left _ _)) (g i (max i j) (le_max_left _ _)) x' +
        Algebra.TensorProduct.map (g j (max i j) (le_max_right _ _)) (g j (max i j) (le_max_right _ _)) y', ?_⟩
      rw [map_add, tensor_transition A f g hg, tensor_transition A f g hg, hx', hy']

include hg hs in
theorem simultaneous {ι : Type*} [Fintype ι] (r : ι → S ⊗[R] S) (x : ι → S) :
    ∃ k, ∃ r' : ι → A k ⊗[R] A k, ∃ x' : ι → A k,
      (∀ j, tensorMap A f k (r' j) = r j) ∧ (∀ j, f k (x' j) = x j) := by
  classical
  choose n a ha using fun j => tensor_exists A f g hg hs (r j)
  choose m b hb using fun j => hs (x j)
  let N := max (Finset.univ.sup n) (Finset.univ.sup m)
  have hn : ∀ j, n j ≤ N := fun j => (Finset.le_sup (Finset.mem_univ j)).trans (le_max_left _ _)
  have hm : ∀ j, m j ≤ N := fun j => (Finset.le_sup (Finset.mem_univ j)).trans (le_max_right _ _)
  refine ⟨N, fun j => Algebra.TensorProduct.map (g (n j) N (hn j)) (g (n j) N (hn j)) (a j),
    fun j => g (m j) N (hm j) (b j), ?_, ?_⟩
  · intro j
    exact (tensor_transition A f g hg _ _ _ (a j)).trans (ha j)
  · intro j
    exact (hg _ _ _ (b j)).trans (hb j)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.TensorSequenceLifts
