import OAI.NumberTheory.PadicHodge.PeriodInvariants.FlatRingUnion
import OAI.NumberTheory.PadicHodge.PeriodInvariants.TensorSequenceLifts
import Mathlib.RingTheory.Etale.Weakly

/-! # Weakly Etale Union -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleUnion

noncomputable section

/-! # An embedded sequence of weakly etale algebras has flat multiplication -/

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A : ℕ → Type*) [∀ k, CommRing (A k)] [∀ k, Algebra R (A k)]
  (f : ∀ k, A k →ₐ[R] S) (g : ∀ i j, i ≤ j → A i →ₐ[R] A j)
  (hg : ∀ i j h x, f j (g i j h x) = f i x)
  (hs : ∀ x : S, ∃ k, ∃ y : A k, f k y = x)
  (hf : ∀ k, Function.Injective (f k))

theorem multiplication_natural (k : ℕ) (x : A k ⊗[R] A k) :
    f k (Algebra.TensorProduct.lmul' R x) =
      Algebra.TensorProduct.lmul' R (TensorSequenceLifts.tensorMap A f k x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [TensorSequenceLifts.tensorMap, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

include hg hs hf in
theorem multiplication_flat [∀ k, Algebra.WeaklyEtale R (A k)] :
    (Algebra.TensorProduct.lmul' R (S := S)).toRingHom.Flat := by
  apply FlatRingUnion.flat (Algebra.TensorProduct.lmul' R (S := S)).toRingHom
    (fun k => A k ⊗[R] A k) A
    (fun k => (TensorSequenceLifts.tensorMap A f k).toRingHom)
    (fun k => (f k).toRingHom) (fun k => (Algebra.TensorProduct.lmul' R (S := A k)).toRingHom)
  · intro k
    exact Algebra.WeaklyEtale.flat_lmul' R (A k)
  · exact multiplication_natural A f
  · exact hf
  · intro n r x
    exact TensorSequenceLifts.simultaneous A f g hg hs r x

include hg hs hf in
theorem weaklyEtale [Module.Flat R S] [∀ k, Algebra.WeaklyEtale R (A k)] :
    Algebra.WeaklyEtale R S where
  flat_lmul' := multiplication_flat A f g hg hs hf

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleUnion
