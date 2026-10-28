import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainReconstruction
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterCost

namespace OAI.Algorithms

/-!
# Selected-storage bounds for the actual Main CRT phase

The size terms below count only the CRT bank, the five decoder scratch
words, and the retained inputs used by preparation. The pending leaf stream
is never part of the bound. Numeric dimension and exponent values come from
the actual readback, while their possibly padded binary lengths remain charged.
-/

namespace SubexponentialSAT.SubexpMainCRTBounds

open scoped BigOperators
open SubexpMainProgram SubexpMainCRT SubexpLiftRing

def preparationBits {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  BitProgram.stackBits ((preparation er alloc).project a).stacks

def selectedBits {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  preparationBits alloc a + scratchBits alloc a

def bankPort {es : ℕ} (alloc : Allocation es) (i : Fin 320) : Fin (totalStacks es) :=
  ordinary alloc ⟨320+i.val, by omega⟩

def bankBits {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  ∑ i : Fin 320, (a.stacks (bankPort alloc i)).length

def readBits {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  (a.stacks (persistent es 12)).length + (a.stacks (persistent es 13)).length +
    (a.stacks (persistent es 14)).length + (a.stacks (persistent es 29)).length +
    (a.stacks (persistent es 30)).length + (a.stacks (persistent es 31)).length +
    (a.stacks (persistent es 19)).length + (a.stacks (ordinary alloc 256)).length +
    (a.stacks (ordinary alloc 265)).length + (a.stacks (persistent es 10)).length

/-- Exactly the selected preparation words, before any clearing or copying. -/
theorem preparationBits_eq {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    preparationBits alloc a = bankBits alloc a + readBits alloc a := by
  have hp := permutation.sum_comp (fun i : Fin 330 => (a.stacks (baseMap alloc i)).length)
  change (∑ i : Fin 330, (a.stacks (stackMap alloc i)).length) = _
  rw [show (∑ i : Fin 330, (a.stacks (stackMap alloc i)).length) =
      ∑ i : Fin 330, (a.stacks (baseMap alloc i)).length from hp]
  change (∑ i : Fin (320+10), (a.stacks (baseMap alloc i)).length) = _
  rw [Fin.sum_univ_add (a := 320) (b := 10)]
  have hbank : (∑ i : Fin 320, (a.stacks (baseMap alloc (i.castAdd 10))).length) =
      bankBits alloc a := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [baseMap, Fin.val_castAdd, dite_eq_left i.isLt, bankPort]
  have hread : (∑ i : Fin 10, (a.stacks (baseMap alloc (i.natAdd 320))).length) =
      readBits alloc a := by
    have hm (i : Fin 10) : baseMap alloc (i.natAdd 320) = highPort alloc i := by
      simp only [baseMap, Fin.val_natAdd, dite_eq_right (by omega : ¬320+i.val < 320)]
      apply congrArg (highPort alloc)
      apply Fin.ext
      simp
    simp only [hm]
    simp [Fin.sum_univ_succ, highPort, readBits, Nat.add_assoc]
  rw [hbank, hread]

theorem selectedBits_eq {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    selectedBits alloc a = bankBits alloc a + readBits alloc a + scratchBits alloc a := by
  rw [selectedBits, preparationBits_eq]

theorem input_length_le {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 7) : (a.stacks (persistent es (inputIndex i))).length ≤ selectedBits alloc a := by
  have h : (((preparation er alloc).project a).stacks
      (SubexpCRTPreparation.inputPort i)).length ≤ preparationBits alloc a := by
    change _ ≤ ∑ j : Fin 330, (((preparation er alloc).project a).stacks j).length
    exact Finset.single_le_sum (fun (j : Fin 330) _ =>
      Nat.zero_le (((preparation er alloc).project a).stacks j).length)
      (Finset.mem_univ _)
  change (a.stacks (stackMap alloc (SubexpCRTPreparation.inputPort i))).length ≤ _ at h
  rw [stackMap_input] at h
  exact h.trans (Nat.le_add_right _ _)

theorem runtimeBound_le_selected {p er es : ℕ} [Fact p.Prime]
    {V : Type*} [Fintype V] (alloc : Allocation es) (a : MainState er es)
    (Q : ℕ) (exponent : List Bool)
    (hD : CounterPrograms.value (a.stacks (persistent es 19)) = Fintype.card V)
    (hE : a.stacks (persistent es 29) = exponent)
    (hvalue : BinaryArithmetic.toNat exponent = p^4-2) :
    SubexpMainCRTSelected.runtimeBound (p := p) (V := V) alloc a Q exponent ≤
      1000000000 * (p^4 + baseWidth p (Fintype.card V+1) + Fintype.card V + Q +
        selectedBits alloc a + 1)^8 := by
  let D := Fintype.card V
  let B := baseWidth p (D+1)
  let S := selectedBits alloc a
  let A := p^4+B+D+Q+S+1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hDlen : (a.stacks (persistent es 19)).length ≤ S := input_length_le alloc a 6
  have hElen : exponent.length ≤ S := by
    have h := input_length_le alloc a 3
    change (a.stacks (persistent es 29)).length ≤ S at h
    simpa only [hE] using h
  have hp := preparationBound_le alloc a
  change preparationBound alloc a ≤ 1100*(preparationBits alloc a+1) +
    32*(CounterPrograms.value (a.stacks (persistent es 19))+1)*
      ((a.stacks (persistent es 19)).length+1) at hp
  rw [hD] at hp
  have hs : preparationBits alloc a ≤ S := Nat.le_add_right _ _
  have hl : scratchBits alloc a ≤ S := Nat.le_add_left _ _
  have hmul : (D+1)*((a.stacks (persistent es 19)).length+1) ≤ A^2 := by
    have h := Nat.mul_le_mul (show D+1 ≤ A by dsimp [A]; omega)
      (show (a.stacks (persistent es 19)).length+1 ≤ A by dsimp [A]; omega)
    simpa only [pow_two] using h
  have hc := SubexpCRTOuterCost.commandBudget_le_inputs p D Q exponent
  have hbase : B+D+Q+exponent.length+BinaryArithmetic.toNat exponent+1 ≤ A := by
    rw [hvalue]
    dsimp [A]
    omega
  have hc' := hc.trans (Nat.mul_le_mul_left 800000000 (Nat.pow_le_pow_left hbase 8))
  have h18 : A ≤ A^8 := by simpa using Nat.pow_le_pow_right hA (show 1 ≤ 8 by decide)
  have h28 : A^2 ≤ A^8 := Nat.pow_le_pow_right hA (by decide)
  have hS : S+1 ≤ A := by dsimp [A]; omega
  change SubexpMainCRTSelected.runtimeBound (p := p) (V := V) alloc a Q exponent ≤ 1000000000*A^8
  unfold SubexpMainCRTSelected.runtimeBound
  change SubexpCRTOuterExecution.commandBudget p D Q exponent+1 ≤ 800000000*A^8 at hc'
  nlinarith only [hp, hs, hl, hmul, hc', h18, h28, hA, hS]

/-- A common cap on actual selected bytes yields a fixed-degree polynomial
in p, dimension, node count, and scalar width. -/
theorem runtimeBound_le_common {p er es : ℕ} [Fact p.Prime]
    {V : Type*} [Fintype V] (alloc : Allocation es) (a : MainState er es)
    (Q W : ℕ) (exponent : List Bool)
    (hD : CounterPrograms.value (a.stacks (persistent es 19)) = Fintype.card V)
    (hE : a.stacks (persistent es 29) = exponent)
    (hvalue : BinaryArithmetic.toNat exponent = p^4-2)
    (hp : p ≤ W) (hd : Fintype.card V ≤ W) (hq : Q ≤ W)
    (hb : baseWidth p (Fintype.card V+1) ≤ W) (hs : selectedBits alloc a ≤ W) :
    SubexpMainCRTSelected.runtimeBound (p := p) (V := V) alloc a Q exponent ≤
      2000000000000000*(W+1)^32 := by
  let A := W+1
  have hA : 1 ≤ A := by dsimp [A]; omega
  have h14 : A ≤ A^4 := by simpa using Nat.pow_le_pow_right hA (show 1 ≤ 4 by decide)
  have hp4 := Nat.pow_le_pow_left (show p ≤ A by dsimp [A]; omega) 4
  have hbase : p^4+baseWidth p (Fintype.card V+1)+Fintype.card V+Q+selectedBits alloc a+1 ≤ 6*A^4 := by
    dsimp [A] at h14 hp4 ⊢
    omega
  have h := (runtimeBound_le_selected alloc a Q exponent hD hE hvalue).trans
    (Nat.mul_le_mul_left 1000000000 (Nat.pow_le_pow_left hbase 8))
  change SubexpMainCRTSelected.runtimeBound (p := p) (V := V) alloc a Q exponent ≤ 2000000000000000*A^32
  norm_num [mul_pow, ← pow_mul] at h
  nlinarith only [h]

private theorem flatMap_length_eq {α : Type*} (xs : List α) (f : α → List Bool) (B : ℕ)
    (h : ∀ x ∈ xs, (f x).length = B) : (xs.flatMap f).length = xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, hx, ht, List.length_cons]
    ring

def auxiliaryBits {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  bankBits alloc a + scratchBits alloc a + (a.stacks (persistent es 10)).length

def inputSize {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (p D Q : ℕ) : ℕ :=
  p+D+Q+baseWidth p (D+1)+auxiliaryBits alloc a+
    (a.stacks (persistent es 29)).length+(a.stacks (persistent es 19)).length+1

/-- Physical post-moments emptiness, independent of any cost conclusion. -/
structure Ready {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : Prop where
  bank : ∀ i : Fin 320, a.stacks (bankPort alloc i) = []
  scratch : ∀ i : Fin 5, a.stacks (decoderScratch alloc i) = []
  answer : a.stacks (persistent es 10) = []

theorem Ready.auxiliaryBits_eq_zero {er es : ℕ} {alloc : Allocation es} {a : MainState er es}
    (h : Ready alloc a) : auxiliaryBits alloc a = 0 := by
  have hb : bankBits alloc a = 0 := by simp only [bankBits, h.bank, List.length_nil, Finset.sum_const_zero]
  have hs : scratchBits alloc a = 0 := by
    have h0 := h.scratch 0
    have h1 := h.scratch 1
    have h2 := h.scratch 2
    have h3 := h.scratch 3
    have h4 := h.scratch 4
    change a.stacks (ordinary alloc 1) = [] at h0
    change a.stacks (ordinary alloc 2) = [] at h1
    change a.stacks (ordinary alloc 3) = [] at h2
    change a.stacks (ordinary alloc 4) = [] at h3
    change a.stacks (ordinary alloc 6) = [] at h4
    simp only [scratchBits, h0, h1, h2, h3, h4, List.length_nil, Nat.add_zero]
  simp only [auxiliaryBits, hb, hs, h.answer, List.length_nil, Nat.add_zero]

section Readback

open SubexpSetupProgram SubexpLayoutSpec SubexpLeafSemantics

variable {cfg : Config} {er n ell p k Δ r : ℕ} {tau : ℚ} [Fact p.Prime]
  {G : Leaf n} {hell : 0 < ell} {hcap : 2^ell ≤ p} {c : Parameters p k Δ r tau}
  {layout : Layout (E := SubexpActualRing.E p)
    (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)).toPattern c}
  {alloc : Allocation (mainExtraStacks cfg)} {a : MainState er (mainExtraStacks cfg)}

local notation "D" => SubexpLeafContract.dimension n ell
local notation "B" => SubexpLeafContract.wordWidth n ell p

theorem readback_selectedBits_le (input : SubexpMainReconstruction.Readback G hell hcap layout alloc a) :
    selectedBits alloc a ≤ auxiliaryBits alloc a + 11*B +
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 29)).length +
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 19)).length +
      4*B*c.Q*(D+1)+1 := by
  have hnodes : (a.stacks (ordinary alloc 256)).length = c.Q*(4*B) := by
    rw [input.node_words]
    simpa only [List.length_finRange] using flatMap_length_eq (List.finRange c.Q)
      (fun i => SubexpFlatAdd.encode (input.nodes i)) (4*B)
      (by intro i hi; exact SubexpFlatAdd.encode_length _)
  have hjets : (a.stacks (ordinary alloc 265)).length = c.Q*(D*(4*B)) := by
    rw [input.jet_words]
    simpa only [List.length_finRange] using flatMap_length_eq (List.finRange c.Q)
      (fun i => SubexpPolynomialPowerProgram.encode p (D+1) (input.jets i)) (D*(4*B))
      (by intro i hi; exact SubexpPolynomialPowerProgram.encode_length p (D+1) _)
  have hm := input.modulus.length_le
  have hminus := input.minusOne.property
  rw [selectedBits_eq]
  unfold readBits auxiliaryBits
  rw [input.modulus_word, input.width_word, input.width_length, input.reduction_word,
    input.one_word, input.minusOne_word, SubexpFlatAdd.encode_length, SubexpFlatAdd.encode_length,
    hminus, hnodes, hjets]
  nlinarith only [hm]

theorem readback_bound_le_selected (input : SubexpMainReconstruction.Readback G hell hcap layout alloc a) :
    input.bound ≤ 1000000000*(p^4+B+D+c.Q+selectedBits alloc a+1)^8 :=
  runtimeBound_le_selected (p := p) (V := Fin (ChunkPartition.count n ell))
    alloc a c.Q input.exponent input.dimension_word
    input.exponent_word input.exponent_value

theorem readback_bound_le_polynomial (input : SubexpMainReconstruction.Readback G hell hcap layout alloc a) :
    input.bound ≤ 10000000000000000000*(inputSize alloc a p D c.Q)^32 := by
  let A := inputSize alloc a p D c.Q
  have hwidth : B = baseWidth p (D+1) := rfl
  have hA : 1 ≤ A := by dsimp [A, inputSize]; omega
  have hp : p ≤ A := by dsimp [A, inputSize]; omega
  have hB : B ≤ A := by rw [hwidth]; dsimp [A, inputSize]; omega
  have hQ : c.Q ≤ A := by dsimp [A, inputSize]; omega
  have hD : D+1 ≤ A := by dsimp [A, inputSize]; omega
  have h13 : A ≤ A^3 := by simpa using Nat.pow_le_pow_right hA (show 1 ≤ 3 by decide)
  have h14 : A ≤ A^4 := by simpa using Nat.pow_le_pow_right hA (show 1 ≤ 4 by decide)
  have h34 : A^3 ≤ A^4 := Nat.pow_le_pow_right hA (by decide)
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul hB hQ) hD
  have hs := readback_selectedBits_le input
  have hlinear : auxiliaryBits alloc a + 11*B +
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 29)).length +
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 19)).length+1 ≤ 11*A := by
    rw [hwidth]
    dsimp [A, inputSize]
    omega
  have hs' : selectedBits alloc a ≤ 15*A^3 := by nlinarith only [hs, hlinear, hprod, h13]
  have hp4 := Nat.pow_le_pow_left hp 4
  have hrest : B+D+c.Q+1 ≤ A := by rw [hwidth]; dsimp [A, inputSize]; omega
  have hbase : p^4+B+D+c.Q+selectedBits alloc a+1 ≤ 17*A^4 := by
    omega
  have h := (readback_bound_le_selected input).trans
    (Nat.mul_le_mul_left 1000000000 (Nat.pow_le_pow_left hbase 8))
  change input.bound ≤ 10000000000000000000*A^32
  norm_num [mul_pow, ← pow_mul] at h
  nlinarith only [h]

theorem readback_bound_le_ready (input : SubexpMainReconstruction.Readback G hell hcap layout alloc a)
    (hready : Ready alloc a) :
    input.bound ≤ 10000000000000000000*(p+D+c.Q+B+
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 29)).length+
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 19)).length+1)^32 := by
  simpa only [inputSize, hready.auxiliaryBits_eq_zero, Nat.add_zero] using
    readback_bound_le_polynomial input

end Readback

end SubexponentialSAT.SubexpMainCRTBounds

end OAI.Algorithms
