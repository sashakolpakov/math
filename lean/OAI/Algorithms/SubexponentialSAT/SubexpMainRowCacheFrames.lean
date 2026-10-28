import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowCache

namespace OAI.Algorithms

/-! Transport the executed source-cache package across an exact frame of
ordinary ports 128 through 137, retaining the same values and encodings. -/

namespace SubexponentialSAT.SubexpMainRowCache.CacheFacts

open SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary)

variable {er es p : ℕ} [Fact p.Prime] {alloc : Allocation es}
  {a b : MainState er es} (h : CacheFacts alloc a p)
  (frame : ∀ i : Fin 10,
    b.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) =
      a.stacks (ordinary alloc ⟨128 + i.val, by omega⟩))

/-- An intervening program that preserves the ten source-cache words also
preserves the exact typed cache package. -/
def transport : CacheFacts alloc b p where
  source := h.source
  source_eq := h.source_eq
  inverse := h.inverse
  negative := h.negative
  difference := h.difference
  inverseCode := h.inverseCode
  negativeCode := h.negativeCode
  differenceCode := h.differenceCode
  inverseEncoded := h.inverseEncoded
  negativeEncoded := h.negativeEncoded
  differenceEncoded := h.differenceEncoded
  inverseValue := h.inverseValue
  negativeValue := h.negativeValue
  differenceValue := h.differenceValue
  modulus := (frame 0).trans h.modulus
  canonicalModulus := h.canonicalModulus
  reduction := (frame 2).trans h.reduction
  width := (congrArg List.length (frame 1)).trans h.width
  zero := (frame 3).trans h.zero
  zeroBits := h.zeroBits
  one := (frame 4).trans h.one
  minusWidth := (congrArg List.length (frame 5)).trans h.minusWidth
  minusValue := (congrArg BinaryArithmetic.toNat (frame 5)).trans h.minusValue
  nodeArray := (frame 6).trans h.nodeArray
  inverseArray := (frame 7).trans h.inverseArray
  negativeArray := (frame 8).trans h.negativeArray
  differenceArray := (frame 9).trans h.differenceArray
  nodeWidth := (congrArg List.length (frame 6)).trans h.nodeWidth
  inverseWidth := h.inverseWidth
  negativeWidth := h.negativeWidth
  differenceWidth := h.differenceWidth

@[simp] theorem transport_source : (h.transport frame).source = h.source := rfl
@[simp] theorem transport_inverse : (h.transport frame).inverse = h.inverse := rfl
@[simp] theorem transport_negative : (h.transport frame).negative = h.negative := rfl
@[simp] theorem transport_difference : (h.transport frame).difference = h.difference := rfl
@[simp] theorem transport_inverseCode : (h.transport frame).inverseCode = h.inverseCode := rfl
@[simp] theorem transport_negativeCode : (h.transport frame).negativeCode = h.negativeCode := rfl
@[simp] theorem transport_differenceCode : (h.transport frame).differenceCode = h.differenceCode := rfl

end SubexponentialSAT.SubexpMainRowCache.CacheFacts

end OAI.Algorithms
