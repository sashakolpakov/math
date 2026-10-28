import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainCRTBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainSystemReadback

namespace OAI.Algorithms

/-!
# CRT cost bounds for the physically ordered factor system

Only the readback record changes from the leaf-specific bounds. The actual
CRT program, selected storage, padding costs, and fixed polynomial remain
the same. No factor reindexing or new execution premise is introduced.
-/

namespace SubexponentialSAT.SubexpMainSystemCRTBounds

open SubexpMainProgram SubexpMainCRT SubexpMainCRTBounds SubexpLayoutSpec SubexpLiftRing

variable {er es D p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {F : Type*} [Fintype F] [DecidableEq F]
  {S : Factor.System (Fin D) F (ZMod p)} {c : Parameters p k Δ r tau}
  {layout : Layout (E := SubexpActualRing.E p) S.toPattern c}
  {alloc : Allocation es} {a : MainState er es}

local notation "N" => Fintype.card (Fin D)
local notation "B" => baseWidth p (N+1)

private theorem flatMap_length_eq {α : Type*} (xs : List α) (f : α → List Bool) (width : ℕ)
    (h : ∀ x ∈ xs, (f x).length = width) : (xs.flatMap f).length = xs.length*width := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, hx, ht, List.length_cons]
    ring

omit [DecidableEq F] in
theorem readback_selectedBits_le (input : SubexpMainSystemReadback.Readback S layout alloc a) :
    selectedBits alloc a ≤ auxiliaryBits alloc a + 11*B +
      (a.stacks (persistent es 29)).length + (a.stacks (persistent es 19)).length +
      4*B*c.Q*(N+1)+1 := by
  have hnodes : (a.stacks (ordinary alloc 256)).length = c.Q*(4*B) := by
    rw [input.node_words]
    simpa only [List.length_finRange] using flatMap_length_eq (List.finRange c.Q)
      (fun i => SubexpFlatAdd.encode (input.nodes i)) (4*B)
      (by intro i hi; exact SubexpFlatAdd.encode_length _)
  have hjets : (a.stacks (ordinary alloc 265)).length = c.Q*(N*(4*B)) := by
    rw [input.jet_words]
    simpa only [List.length_finRange] using flatMap_length_eq (List.finRange c.Q)
      (fun i => SubexpPolynomialPowerProgram.encode p (N+1) (input.jets i)) (N*(4*B))
      (by intro i hi; exact SubexpPolynomialPowerProgram.encode_length p (N+1) _)
  have hm := input.modulus.length_le
  have hminus := input.minusOne.property
  rw [selectedBits_eq]
  unfold readBits auxiliaryBits
  rw [input.modulus_word, input.width_word, input.width_length, input.reduction_word,
    input.one_word, input.minusOne_word, SubexpFlatAdd.encode_length, SubexpFlatAdd.encode_length,
    hminus, hnodes, hjets]
  nlinarith only [hm]

omit [DecidableEq F] in
theorem readback_bound_le_selected (input : SubexpMainSystemReadback.Readback S layout alloc a) :
    input.bound ≤ 1000000000*(p^4+B+N+c.Q+selectedBits alloc a+1)^8 :=
  runtimeBound_le_selected (p := p) (V := Fin D) alloc a c.Q input.exponent
    input.dimension_word input.exponent_word input.exponent_value

omit [DecidableEq F] in
theorem readback_bound_le_common (input : SubexpMainSystemReadback.Readback S layout alloc a)
    (W : ℕ) (hp : p ≤ W) (hd : N ≤ W) (hq : c.Q ≤ W) (hb : B ≤ W)
    (hs : selectedBits alloc a ≤ W) : input.bound ≤ 2000000000000000*(W+1)^32 :=
  runtimeBound_le_common (p := p) (V := Fin D) alloc a c.Q W input.exponent
    input.dimension_word input.exponent_word input.exponent_value hp hd hq hb hs

omit [DecidableEq F] in
theorem readback_bound_le_polynomial (input : SubexpMainSystemReadback.Readback S layout alloc a) :
    input.bound ≤ 10000000000000000000*(inputSize alloc a p N c.Q)^32 := by
  let A := inputSize alloc a p N c.Q
  have hA : 1 ≤ A := by dsimp [A, inputSize]; omega
  have hp : p ≤ A := by dsimp [A, inputSize]; omega
  have hB : B ≤ A := by dsimp [A, inputSize]; omega
  have hQ : c.Q ≤ A := by dsimp [A, inputSize]; omega
  have hD : N+1 ≤ A := by dsimp [A, inputSize]; omega
  have h13 : A ≤ A^3 := by simpa using Nat.pow_le_pow_right hA (show 1 ≤ 3 by decide)
  have h14 : A ≤ A^4 := by simpa using Nat.pow_le_pow_right hA (show 1 ≤ 4 by decide)
  have h34 : A^3 ≤ A^4 := Nat.pow_le_pow_right hA (by decide)
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul hB hQ) hD
  have hs := readback_selectedBits_le input
  have hlinear : auxiliaryBits alloc a + 11*B + (a.stacks (persistent es 29)).length +
      (a.stacks (persistent es 19)).length+1 ≤ 11*A := by
    dsimp [A, inputSize]
    omega
  have hs' : selectedBits alloc a ≤ 15*A^3 := by nlinarith only [hs, hlinear, hprod, h13]
  have hp4 := Nat.pow_le_pow_left hp 4
  have hrest : B+N+c.Q+1 ≤ A := by dsimp [A, inputSize]; omega
  have hbase : p^4+B+N+c.Q+selectedBits alloc a+1 ≤ 17*A^4 := by omega
  have h := (readback_bound_le_selected input).trans
    (Nat.mul_le_mul_left 1000000000 (Nat.pow_le_pow_left hbase 8))
  change input.bound ≤ 10000000000000000000*A^32
  norm_num [mul_pow, ← pow_mul] at h
  nlinarith only [h]

omit [DecidableEq F] in
theorem readback_bound_le_dimension (input : SubexpMainSystemReadback.Readback S layout alloc a) :
    input.bound ≤ 10000000000000000000*(inputSize alloc a p D c.Q)^32 := by
  simpa only [Fintype.card_fin] using readback_bound_le_polynomial input

omit [DecidableEq F] in
theorem readback_bound_le_ready (input : SubexpMainSystemReadback.Readback S layout alloc a)
    (hready : Ready alloc a) :
    input.bound ≤ 10000000000000000000*(p+D+c.Q+baseWidth p (D+1)+
      (a.stacks (persistent es 29)).length+(a.stacks (persistent es 19)).length+1)^32 := by
  simpa only [inputSize, hready.auxiliaryBits_eq_zero, Nat.add_zero] using
    readback_bound_le_dimension input

end SubexponentialSAT.SubexpMainSystemCRTBounds

end OAI.Algorithms
