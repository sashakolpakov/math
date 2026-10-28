import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainCacheSetup
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding

namespace OAI.Algorithms

/-!
# Source-ring cache facts for Main's row producer

The record below is extracted from the actual cache setup result. Inverse
and inverse-difference functions index the lists emitted by that execution;
their byte arrays and field meanings are proved together. Selecting those
proof witnesses does not add an operation to the executed program.
-/

namespace SubexponentialSAT.SubexpMainRowCache

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary)
open SubexpLiftRing SubexpQuarticRing

abbrev Code (p : ℕ) := Quad (Word (baseWidth p 1))

def sourceData (p : ℕ) [Fact p.Prime] : SubexpSelectedConversions.Prepared p 0 :=
  SubexpPreparedQuarticSetup.preparedData p 0
    (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p)

def nodeCode (p : ℕ) [Fact p.Prime] (i : Fin (p^4 - 1)) : Code p :=
  SubexpNodeLiftData.sourceQuad p (SubexpMachineNodeOrder.nodeCoefficients p i)

theorem flat_eq_encode {B : ℕ} (a : Quad (Word B)) :
    SubexpQuarticFlatMul.flat a = SubexpFlatAdd.encode a := by
  cases a
  simp [SubexpQuarticFlatMul.flat, SubexpQuarticFlatMul.wordLists,
    FourWordPrograms.flatWords, SubexpFlatAdd.encode, SubexpFlatAdd.flatten,
    SubexpFlatAdd.quadWords, Quad.toFn]

theorem setup_flat_eq_flat {B : ℕ} (a : Quad (Word B)) :
    SubexpPreparedQuarticSetup.flat a = SubexpQuarticFlatMul.flat a := rfl

theorem decode_eq_fieldValue {p : ℕ} [Fact p.Prime]
    (source : SubexpSelectedConversions.Prepared p 0) (a : Code p) :
    source.residueRing.decode a = SubexpFieldCacheInterpretation.fieldValue p a := rfl

theorem source_modulus (p : ℕ) [Fact p.Prime] :
    (sourceData p).modulus.bits = Subexp.MatrixWordEncoding.modulus p := by
  change fixedBits (baseWidth p 1 + 1) (p^1) = fixedBits (baseWidth p 1 + 1) p
  rw [pow_one]

theorem source_zero_bits (p : ℕ) [Fact p.Prime] :
    SubexpFlatAdd.encode (sourceData p).zero =
      List.replicate (4 * baseWidth p 1) false := by
  have h := SubexpPreparedRingStaging.bankWords_zero p 0
    (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p)
  change SubexpPreparedQuarticSetup.flat (sourceData p).zero = _ at h
  rw [setup_flat_eq_flat, flat_eq_encode] at h
  exact h

theorem source_minusOne_value (p : ℕ) [Fact p.Prime] :
    BinaryArithmetic.toNat (SubexpPreparedQuarticSetup.minusOne p 1).val = p - 1 := by
  have hm : BinaryArithmetic.toNat (SubexpPreparedQuarticPrelude.modulusWord p 1) = p := by
    change BinaryArithmetic.toNat (SubexpPreparedQuarticSetup.modulus p 1).bits = p
    simpa only [pow_one] using (SubexpPreparedQuarticSetup.modulus p 1).value
  change BinaryArithmetic.toNat (SubexpNegationSetup.preparedConstant
    (SubexpPreparedQuarticPrelude.widthWord p 1)
    (SubexpPreparedQuarticPrelude.modulusWord p 1)) = _
  rw [SubexpNegationSetup.preparedConstant_value, hm]
  · rw [hm]
    exact (Fact.out : p.Prime).pos
  · rw [hm, SubexpPreparedQuarticPrelude.widthWord_length]
    simpa only [pow_one] using modulus_le_width p 1

def indexed {α : Type*} (xs : List α) {n : ℕ} (h : xs.length = n) (i : Fin n) : α :=
  xs.get ⟨i.val, by rw [h]; exact i.isLt⟩

theorem ofFn_indexed {α : Type*} (xs : List α) {n : ℕ} (h : xs.length = n) :
    List.ofFn (indexed xs h) = xs := by
  subst n
  exact List.ofFn_get xs

theorem indexed_flatMap {α β : Type*} (xs : List α) {n : ℕ} (h : xs.length = n)
    (f : α → List β) :
    (List.ofFn (fun i => f (indexed xs h i))).flatten = xs.flatMap f := by
  change (List.ofFn (f ∘ indexed xs h)).flatten = _
  rw [← List.map_ofFn, ofFn_indexed, List.flatMap_def]

theorem flatten_map_flatMap {α β : Type*} (rows : List (List α)) (f : α → List β) :
    (rows.map (fun row => row.flatMap f)).flatten = rows.flatten.flatMap f := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_append, ih]

theorem indexed_matrix_flatMap {α β : Type*} (rows : List (List α)) {n : ℕ}
    (hr : rows.length = n) (hc : ∀ i, (indexed rows hr i).length = n) (f : α → List β) :
    (List.ofFn (fun i =>
      (List.ofFn (fun j => f (indexed (indexed rows hr i) (hc i) j))).flatten)).flatten =
      rows.flatten.flatMap f := by
  simp_rw [indexed_flatMap]
  exact flatten_map_flatMap rows f

/-- Exactly the retained source cache required by the row producer, plus
typed witnesses that connect its byte functions to the selected field. -/
structure CacheFacts {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p : ℕ) [Fact p.Prime] where
  source : SubexpSelectedConversions.Prepared p 0
  source_eq : source = sourceData p
  inverse : Fin (p^4 - 1) → List Bool
  negative : Fin (p^4 - 1) → List Bool
  difference : Fin (p^4 - 1) → Fin (p^4 - 1) → List Bool
  inverseCode : Fin (p^4 - 1) → Code p
  negativeCode : Fin (p^4 - 1) → Code p
  differenceCode : Fin (p^4 - 1) → Fin (p^4 - 1) → Code p
  inverseEncoded : ∀ i, inverse i = SubexpQuarticFlatMul.flat (inverseCode i)
  negativeEncoded : ∀ i, negative i = SubexpQuarticFlatMul.flat (negativeCode i)
  differenceEncoded : ∀ i j, difference i j = SubexpQuarticFlatMul.flat (differenceCode i j)
  inverseValue : ∀ i, source.residueRing.decode (inverseCode i) =
    ((SubexpMachineNodeOrder.nodeEquiv p i).val)⁻¹
  negativeValue : ∀ i, source.residueRing.decode (negativeCode i) =
    -(SubexpMachineNodeOrder.nodeEquiv p i).val
  differenceValue : ∀ i j, source.residueRing.decode (differenceCode i j) =
    ((SubexpMachineNodeOrder.nodeEquiv p i).val - (SubexpMachineNodeOrder.nodeEquiv p j).val)⁻¹
  modulus : a.stacks (ordinary alloc 128) = source.modulus.bits
  canonicalModulus : source.modulus.bits = Subexp.MatrixWordEncoding.modulus p
  reduction : a.stacks (ordinary alloc 130) = SubexpQuarticFlatMul.flat source.reduction
  width : (a.stacks (ordinary alloc 129)).length = baseWidth p 1
  zero : a.stacks (ordinary alloc 131) = SubexpFlatAdd.encode source.zero
  zeroBits : SubexpFlatAdd.encode source.zero = List.replicate (4 * baseWidth p 1) false
  one : a.stacks (ordinary alloc 132) = SubexpFlatAdd.encode source.one
  minusWidth : (a.stacks (ordinary alloc 133)).length = baseWidth p 1
  minusValue : BinaryArithmetic.toNat (a.stacks (ordinary alloc 133)) = p - 1
  nodeArray : a.stacks (ordinary alloc 134) =
    (List.ofFn (fun i => SubexpQuarticFlatMul.flat (nodeCode p i))).flatten
  inverseArray : a.stacks (ordinary alloc 135) = (List.ofFn inverse).flatten
  negativeArray : a.stacks (ordinary alloc 136) = (List.ofFn negative).flatten
  differenceArray : a.stacks (ordinary alloc 137) =
    (List.ofFn (fun i => (List.ofFn (difference i)).flatten)).flatten
  nodeWidth : (a.stacks (ordinary alloc 134)).length = (p^4 - 1) * (4 * baseWidth p 1)
  inverseWidth : ∀ i, (inverse i).length = 4 * baseWidth p 1
  negativeWidth : ∀ i, (negative i).length = 4 * baseWidth p 1
  differenceWidth : ∀ i j, (difference i j).length = 4 * baseWidth p 1

theorem exists_cacheFacts {er es p D : ℕ} [Fact p.Prime]
    {alloc : Allocation es} {before after : MainState er es}
    (h : SubexpMainCacheSetup.Result alloc before after p D) :
    Nonempty (CacheFacts alloc after p) := by
  obtain ⟨middle, hf⟩ := h.field_cache
  obtain ⟨ys, rows, hv, hnode, hinverse, hnegative, hdifference⟩ := hf.arrays
  change after.stacks (ordinary alloc 134) = _ at hnode
  change after.stacks (ordinary alloc 136) = _ at hnegative
  have hy : ys.length = p^4 - 1 :=
    hv.inverses.length_eq.symm.trans (SubexpFieldCacheInterpretation.nodeQuads_length p)
  have hr : rows.length = p^4 - 1 :=
    hv.differences.length_eq.symm.trans (SubexpFieldCacheInterpretation.nodeQuads_length p)
  have hrow (i : Fin (p^4 - 1)) :
      List.Forall₂ (fun b inverse => SubexpFieldCacheInterpretation.fieldValue p inverse =
        (SubexpFieldCacheInterpretation.fieldValue p (nodeCode p i) -
          SubexpFieldCacheInterpretation.fieldValue p b)⁻¹)
        (SubexpNodeLiftData.nodeQuads p) (indexed rows hr i) := by
    have hh := hv.differences.get
      (by rw [SubexpFieldCacheInterpretation.nodeQuads_length]; exact i.isLt)
      (show i.val < rows.length by rw [hr]; exact i.isLt)
    rw [SubexpFieldCacheInterpretation.nodeQuads_get p i] at hh
    exact hh
  have hc (i : Fin (p^4 - 1)) : (indexed rows hr i).length = p^4 - 1 :=
    (hrow i).length_eq.symm.trans (SubexpFieldCacheInterpretation.nodeQuads_length p)
  let inv : Fin (p^4 - 1) → Code p := indexed ys hy
  let neg : Fin (p^4 - 1) → Code p := fun i =>
    SubexpQuarticNegMachine.negateWords p 1 (SubexpPreparedQuarticSetup.modulus p 1)
      (SubexpPreparedQuarticSetup.minusOne p 1) (nodeCode p i)
  let diff : Fin (p^4 - 1) → Fin (p^4 - 1) → Code p := fun i =>
    indexed (indexed rows hr i) (hc i)
  have hinv (i : Fin (p^4 - 1)) :
      (sourceData p).residueRing.decode (inv i) =
        ((SubexpMachineNodeOrder.nodeEquiv p i).val)⁻¹ := by
    have hh := hv.inverses.get
      (by rw [SubexpFieldCacheInterpretation.nodeQuads_length]; exact i.isLt)
      (show i.val < ys.length by rw [hy]; exact i.isLt)
    rw [SubexpFieldCacheInterpretation.nodeQuads_get p i,
      SubexpFieldCacheInterpretation.node_value p i] at hh
    exact hh
  have hneg (i : Fin (p^4 - 1)) :
      (sourceData p).residueRing.decode (neg i) =
        -(SubexpMachineNodeOrder.nodeEquiv p i).val := by
    change SubexpFieldCacheInterpretation.fieldValue p (neg i) = _
    rw [SubexpFieldCacheInterpretation.negative_value p _ _
      (SubexpPreparedQuarticSetup.minusOne_value p 1)]
    exact congrArg Neg.neg (SubexpFieldCacheInterpretation.node_value p i)
  have hdiff (i j : Fin (p^4 - 1)) :
      (sourceData p).residueRing.decode (diff i j) =
        ((SubexpMachineNodeOrder.nodeEquiv p i).val -
          (SubexpMachineNodeOrder.nodeEquiv p j).val)⁻¹ := by
    have hh := (hrow i).get
      (by rw [SubexpFieldCacheInterpretation.nodeQuads_length]; exact j.isLt)
      (show j.val < (indexed rows hr i).length by rw [hc]; exact j.isLt)
    rw [SubexpFieldCacheInterpretation.nodeQuads_get p j] at hh
    change SubexpFieldCacheInterpretation.fieldValue p (diff i j) = _
    simpa only [diff, indexed, nodeCode,
      SubexpFieldCacheInterpretation.node_value] using hh
  have hs (i : Fin 6) :
      after.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) =
        SubexpPreparedRingStaging.bankWords p 0
          (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
          (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p) i := h.source i
  have hm := hs 0
  have hw := hs 1
  have hred := hs 2
  have hz := hs 3
  have ho := hs 4
  have hminus := hs 5
  change after.stacks (ordinary alloc 128) = (sourceData p).modulus.bits at hm
  change after.stacks (ordinary alloc 129) = SubexpPreparedQuarticPrelude.widthWord p 1 at hw
  change after.stacks (ordinary alloc 130) = SubexpPreparedQuarticSetup.flat (sourceData p).reduction at hred
  change after.stacks (ordinary alloc 131) = SubexpPreparedQuarticSetup.flat (sourceData p).zero at hz
  change after.stacks (ordinary alloc 132) = SubexpPreparedQuarticSetup.flat (sourceData p).one at ho
  change after.stacks (ordinary alloc 133) = (SubexpPreparedQuarticSetup.minusOne p 1).val at hminus
  rw [setup_flat_eq_flat] at hred
  rw [setup_flat_eq_flat, flat_eq_encode] at hz ho
  refine ⟨{
    source := sourceData p, source_eq := rfl
    inverse := fun i => SubexpQuarticFlatMul.flat (inv i)
    negative := fun i => SubexpQuarticFlatMul.flat (neg i)
    difference := fun i j => SubexpQuarticFlatMul.flat (diff i j)
    inverseCode := inv, negativeCode := neg, differenceCode := diff
    inverseEncoded := fun _ => rfl, negativeEncoded := fun _ => rfl
    differenceEncoded := fun _ _ => rfl
    inverseValue := hinv, negativeValue := hneg, differenceValue := hdiff
    modulus := hm, canonicalModulus := source_modulus p, reduction := hred
    width := (congrArg List.length hw).trans (SubexpPreparedQuarticPrelude.widthWord_length p 1)
    zero := hz, zeroBits := source_zero_bits p, one := ho
    minusWidth := (congrArg List.length hminus).trans (SubexpPreparedQuarticSetup.minusOne p 1).property
    minusValue := (congrArg BinaryArithmetic.toNat hminus).trans (source_minusOne_value p)
    nodeArray := ?_, inverseArray := ?_, negativeArray := ?_, differenceArray := ?_
    nodeWidth := ?_, inverseWidth := ?_, negativeWidth := ?_, differenceWidth := ?_
  }⟩
  · rw [hnode, ← SubexpFieldCacheInterpretation.nodeQuads_flat_encoded]
    simp only [SubexpNodeLiftData.nodeQuads, List.map_ofFn, nodeCode, Function.comp_def]
  · exact hinverse.trans (indexed_flatMap ys hy SubexpQuarticFlatMul.flat).symm
  · rw [hnegative]
    simp only [SubexpFieldCacheNodeLoop.negativeBytes, SubexpNodeLiftData.nodeQuads,
      List.flatMap_def, List.map_ofFn, nodeCode, neg, Function.comp_def]
  · exact hdifference.trans
      (indexed_matrix_flatMap rows hr hc SubexpQuarticFlatMul.flat).symm
  · have hport :
        SubexpMainFieldCache.ordinary (SubexpMainCacheSetup.cacheAllocation alloc) 134 =
          ordinary alloc 134 := Fin.ext rfl
    rw [← hport]
    simpa only [Nat.mul_comm] using hf.cache_lengths.1
  · intro i
    exact SubexpQuarticFlatMul.flat_length (inv i)
  · intro i
    exact SubexpQuarticFlatMul.flat_length (neg i)
  · intro i j
    exact SubexpQuarticFlatMul.flat_length (diff i j)

/-- Readback package from the actual executed cache producer. -/
noncomputable def of_result {er es p D : ℕ} [Fact p.Prime]
    {alloc : Allocation es} {before after : MainState er es}
    (h : SubexpMainCacheSetup.Result alloc before after p D) : CacheFacts alloc after p :=
  Classical.choice (exists_cacheFacts h)

end SubexponentialSAT.SubexpMainRowCache

end OAI.Algorithms
