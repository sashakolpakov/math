import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPointBankStream
import OAI.Algorithms.SubexponentialSAT.DensePolynomialPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpSelectedConversions

namespace OAI.Algorithms

/-!
# Physical construction of a point bank over the prime field

The masters are flat base and own-color increment vectors at source width.
The fixed program copies both masters, adds modulo p, preserves the resulting
canonical scalar bank, and marshals its coordinates into the beta input list.
No arithmetic is performed modulo the lifted coefficient modulus here.
-/

namespace SubexponentialSAT.SubexpPointBank

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing BinaryArithmetic

abbrev Data := State 8 32

/-- Public preserved ports: p=5, width=10, base=22, increment=23, D=24. -/
def frame (modulus width base increment dimensions : List Bool) (j : Fin 32) : List Bool :=
  if j = 5 then modulus else if j = 10 then width else if j = 22 then base
  else if j = 23 then increment else if j = 24 then dimensions else []

/-- Private inputs 8/9; public outputs scalar bank20 and quartet stream21. -/
def state (regs : Fin 8 → Bool) (modulus width base increment dimensions
    left right bank output : List Bool) : Data :=
  ⟨regs, fun j => if j = 8 then left else if j = 9 then right
    else if j = 20 then bank else if j = 21 then output
    else frame modulus width base increment dimensions j⟩

def ready (regs : Fin 8 → Bool) (modulus width base increment dimensions
    bank output : List Bool) : Data :=
  state regs modulus width base increment dimensions [] [] bank output

abbrev copy (src dst : Fin 32) : Cmd 8 32 :=
  .call (StackRoutines.copyProgram src dst 25 0 1)

def addPorts : Fin 20 → Fin 32 := Fin.castAdd 12
def streamPorts : Fin 8 → Fin 32 := ![8, 10, 0, 1, 2, 3, 4, 21]

theorem addPorts_injective : Function.Injective addPorts := Fin.castAdd_injective _ _
theorem streamPorts_injective : Function.Injective streamPorts := by decide

abbrev add : Cmd 8 32 := .call (ProgramLinking.liftProgram DensePolynomialPrograms.program id addPorts)
abbrev stream : Cmd 8 32 := .call (ProgramLinking.liftProgram SubexpPointBankStream.program id streamPorts)

abbrev command : Cmd 8 32 :=
  .seq (copy 22 8) (.seq (copy 23 9) (.seq add (.seq (copy 8 20) stream)))

def program := compiled command 22 21

theorem program_labels : size command + 1 = 294 := rfl

theorem copy_base (regs : Fin 8 → Bool) (m w x y d : List Bool) :
    Eval (copy 22 8) (7 * x.length + 5)
      (ready regs m w x y d [] [])
      (state (readRegs regs 0 1 none) m w x y d x [] [] []) := by
  have h := copy_eval (ready regs m w x y d [] []) 22 8 25 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have he : afterCopy (ready regs m w x y d [] []) 22 8 0 1 =
      state (readRegs regs 0 1 none) m w x y d x [] [] [] := by
    apply state_ext
    · rfl
    · funext j
      by_cases h8 : j = 8
      · subst j; simp [afterCopy, StackRoutines.copyStacks, ready, state, frame]
      · simp [afterCopy, StackRoutines.copyStacks, ready, state, h8]
  have hlen : ((ready regs m w x y d [] []).stacks 22).length = x.length := rfl
  simpa only [copy, hlen, he] using h

theorem copy_increment (regs : Fin 8 → Bool) (m w x y d : List Bool) :
    Eval (copy 23 9) (7 * y.length + 5)
      (state regs m w x y d x [] [] [])
      (state (readRegs regs 0 1 none) m w x y d x y [] []) := by
  have h := copy_eval (state regs m w x y d x [] [] []) 23 9 25 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have he : afterCopy (state regs m w x y d x [] [] []) 23 9 0 1 =
      state (readRegs regs 0 1 none) m w x y d x y [] [] := by
    apply state_ext
    · rfl
    · funext j
      by_cases h9 : j = 9
      · subst j; simp [afterCopy, StackRoutines.copyStacks, state, frame]
      · simp [afterCopy, StackRoutines.copyStacks, state, h9]
  have hlen : ((state regs m w x y d x [] [] []).stacks 23).length = y.length := rfl
  simpa only [copy, hlen, he] using h

theorem copy_bank (regs : Fin 8 → Bool) (m w x y d sum : List Bool) :
    Eval (copy 8 20) (7 * sum.length + 5)
      (state regs m w x y d sum [] [] [])
      (state (readRegs regs 0 1 none) m w x y d sum [] sum []) := by
  have h := copy_eval (state regs m w x y d sum [] [] []) 8 20 25 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have he : afterCopy (state regs m w x y d sum [] [] []) 8 20 0 1 =
      state (readRegs regs 0 1 none) m w x y d sum [] sum [] := by
    apply state_ext
    · rfl
    · funext j
      by_cases h20 : j = 20
      · subst j; simp [afterCopy, StackRoutines.copyStacks, state, frame]
      · simp [afterCopy, StackRoutines.copyStacks, state, h20]
  have hlen : ((state regs m w x y d sum [] [] []).stacks 8).length = sum.length := rfl
  simpa only [copy, hlen, he] using h

private theorem embed_add (regs oldRegs : Fin 8 → Bool)
    (m w x y d left right oldLeft oldRight : List Bool) :
    embedState id addPorts (state oldRegs m w x y d oldLeft oldRight [] [])
      (DensePolynomialLoop.ready regs m left right w [] (fun _ => [])) =
      state regs m w x y d left right [] [] := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id addPorts_injective
  · intros; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> rfl
  · intro j hj
    have h20 : ¬j.val < 20 := by
      intro h; exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    have h8 : j ≠ 8 := by intro h; subst j; omega
    have h9 : j ≠ 9 := by intro h; subst j; omega
    simp [state, h8, h9]

private theorem embed_stream (regs oldRegs : Fin 8 → Bool)
    (m w x y d source bank output oldSource oldOutput : List Bool) :
    embedState id streamPorts (state oldRegs m w x y d oldSource [] bank oldOutput)
      (SubexpPointBankStream.ready regs source w [] output) =
      state regs m w x y d source [] bank output := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id streamPorts_injective
  · intros; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro j hj
    have h8 : j ≠ 8 := fun h => hj ⟨0, h.symm⟩
    have h21 : j ≠ 21 := fun h => hj ⟨7, h.symm⟩
    simp [state, h8, h21]

variable (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)

def pointWords (xs ys : List (Word (baseWidth p 1))) : List (Word (baseWidth p 1)) :=
  DensePolynomialPrograms.addWordsTotal p 1 M xs ys

theorem pointWords_length (xs ys : List (Word (baseWidth p 1))) (hlen : xs.length = ys.length) :
    (pointWords p M xs ys).length = xs.length := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp at hlen
  | cons x xs ih => cases ys with
    | nil => simp at hlen
    | cons y ys =>
      change (_ :: pointWords p M xs ys).length = (x :: xs).length
      simp only [List.length_cons]
      rw [ih ys (by simpa using hlen)]

theorem pointWords_canonical (xs ys : List (Word (baseWidth p 1)))
    (hlen : xs.length = ys.length) :
    ∀ w ∈ pointWords p M xs ys, BinaryArithmetic.toNat w.val < p := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => simp [pointWords, DensePolynomialPrograms.addWordsTotal, DensePolynomialLoop.addWordsTotal]
    | cons y ys => simp at hlen
  | cons x xs ih => cases ys with
    | nil => simp at hlen
    | cons y ys =>
      change ∀ w ∈ (SubexpPreparedQuartic.wordAdd p 1 M x y).1 :: pointWords p M xs ys, _
      intro w hw
      rcases List.mem_cons.mp hw with h | h
      · subst w
        simpa only [pow_one] using SubexpPreparedQuartic.wordAdd_canonical p 1 M x y
      · exact ih ys (by simpa using hlen) w h

theorem pointWord_value (x y : Word (baseWidth p 1)) :
    BinaryArithmetic.toNat (SubexpPreparedQuartic.wordAdd p 1 M x y).1.val = (BinaryArithmetic.toNat x.val + BinaryArithmetic.toNat y.val) % p := by
  change BinaryArithmetic.toNat (addBaseRun _ _ _ _).1 = _
  rw [addBaseRun_value _ _ _ _ (by simpa only [M.value, pow_one] using (Fact.out : p.Prime).pos)
    (by rw [M.value]; exact modulus_le_width p 1), M.value, pow_one]

theorem pointWord_canonical_label (x y : Word (baseWidth p 1)) :
    BinaryArithmetic.toNat (SubexpPreparedQuartic.wordAdd p 1 M x y).1.val =
      ((BinaryArithmetic.toNat x.val : ZMod p) + (BinaryArithmetic.toNat y.val : ZMod p)).val := by
  rw [pointWord_value]
  simpa only [Nat.cast_add] using (ZMod.val_natCast p (BinaryArithmetic.toNat x.val + BinaryArithmetic.toNat y.val)).symm

theorem pointWords_values (xs ys : List (Word (baseWidth p 1)))
    (hlen : xs.length = ys.length) :
    (pointWords p M xs ys).map (fun w => BinaryArithmetic.toNat w.val) =
      List.zipWith (fun x y : Word (baseWidth p 1) => (BinaryArithmetic.toNat x.val + BinaryArithmetic.toNat y.val) % p) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons y ys => simp at hlen
  | cons x xs ih => cases ys with
    | nil => simp at hlen
    | cons y ys =>
      change BinaryArithmetic.toNat (SubexpPreparedQuartic.wordAdd p 1 M x y).1.val ::
        (pointWords p M xs ys).map (fun w => BinaryArithmetic.toNat w.val) =
        ((BinaryArithmetic.toNat x.val + BinaryArithmetic.toNat y.val) % p) :: _
      rw [pointWord_value, ih ys (by simpa using hlen)]

theorem pointWords_map {ι : Type*} (is : List ι)
    (x y : ι → Word (baseWidth p 1)) :
    pointWords p M (is.map x) (is.map y) =
      is.map (fun i => (SubexpPreparedQuartic.wordAdd p 1 M (x i) (y i)).1) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change (SubexpPreparedQuartic.wordAdd p 1 M (x i) (y i)).1 ::
      pointWords p M (is.map x) (is.map y) = _
    rw [ih]
    rfl

def constant (w : Word (baseWidth p 1)) : Quad (Word (baseWidth p 1)) :=
  ⟨w, SubexpPreparedQuartic.zeroWord p 1, SubexpPreparedQuartic.zeroWord p 1,
    SubexpPreparedQuartic.zeroWord p 1⟩

theorem constant_decode (source : SubexpSelectedConversions.Prepared p 0)
    (w : Word (baseWidth p 1)) :
    source.residueRing.decode (constant p w) =
      algebraMap (ZMod p) (SubexpActualRing.E p) (SubexpWordLift.sourceValue p w) := by
  have hz : SubexpWordLift.sourceValue p (SubexpPreparedQuartic.zeroWord p 1) = 0 := by
    have h := congrArg (LiftRing.baseReduction p 1 (by decide))
      (SubexpPreparedQuartic.zeroWord_value p 1)
    simpa only [SubexpWordLift.sourceValue, wordValue, map_natCast, map_zero] using h
  rw [SubexpSelectedConversions.Prepared.residueRing_decode]
  simp only [constant, Quad.map, hz, quotientDenote_const]
  rfl

theorem point_constant_decode (source : SubexpSelectedConversions.Prepared p 0)
    (x y : Word (baseWidth p 1)) :
    source.residueRing.decode (constant p (SubexpPreparedQuartic.wordAdd p 1 M x y).1) =
      algebraMap (ZMod p) (SubexpActualRing.E p)
        (SubexpWordLift.sourceValue p x + SubexpWordLift.sourceValue p y) := by
  rw [constant_decode]
  congr 1
  unfold SubexpWordLift.sourceValue
  rw [pointWord_value]
  simp

def quartetStream (xs : List (Word (baseWidth p 1))) : List Bool :=
  Encoding.encodeList (fun w => SubexpFlatAdd.encode (constant p w)) xs

omit [Fact p.Prime] in
theorem quartetStream_map (xs : List (Word (baseWidth p 1))) :
    quartetStream p xs = Encoding.encodeList SubexpFlatAdd.encode (xs.map (constant p)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [quartetStream, Encoding.encodeList, List.map_cons] at ih ⊢; rw [ih]

omit [Fact p.Prime] in
theorem quartetStream_eq (xs : List (Word (baseWidth p 1))) (width : List Bool)
    (hw : width.length = baseWidth p 1) :
    Encoding.encodeList (fun w : Word (baseWidth p 1) =>
      SubexpQuarticMarshal.marshalBits w.val width) xs = quartetStream p xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [quartetStream, Encoding.encodeList] at ih ⊢
    rw [SubexpFlatAdd.marshalBits_eq_encode_constant p 1 x.val width x.property hw, ih]
    rfl

/-- All growing parameters remain in the explicit transition bound. -/
def steps (D b : ℕ) : ℕ := 7000 * (2 * D + 1) * (b + 1)^2 + D * (133 * b + 53) + 28

omit [Fact p.Prime] in
theorem steps_polynomial (D b : ℕ) : steps D b ≤ 15000 * (D + 1) * (b + 1)^2 := by
  have hb : 133 * b + 53 ≤ 1000 * (b + 1)^2 := by nlinarith
  have h28 : 28 ≤ 8000 * (b + 1)^2 := by nlinarith
  unfold steps
  nlinarith [Nat.mul_le_mul_left D hb]

theorem program_runs (xs ys : List (Word (baseWidth p 1))) (hlen : xs.length = ys.length)
    (regs : Fin 8 → Bool) (width dimensions : List Bool) (hw : width.length = baseWidth p 1) :
    ∃ rf, RunsIn program (steps xs.length (baseWidth p 1))
      ((ready regs M.bits width (DensePolynomialLoop.flatten xs) (DensePolynomialLoop.flatten ys)
        dimensions [] []).withPC (some program.entry))
      ((ready rf M.bits width (DensePolynomialLoop.flatten xs) (DensePolynomialLoop.flatten ys)
        dimensions (DensePolynomialLoop.flatten (pointWords p M xs ys))
        (quartetStream p (pointWords p M xs ys))).withPC none) := by
  let x := DensePolynomialLoop.flatten xs
  let y := DensePolynomialLoop.flatten ys
  let sum := DensePolynomialLoop.flatten (pointWords p M xs ys)
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  have h1 := copy_base regs M.bits width x y dimensions
  have h2 := copy_increment r1 M.bits width x y dimensions
  have hB : 0 < baseWidth p 1 := Nat.mul_pos (by omega) (Nat.zero_lt_succ _)
  obtain ⟨n, hn, ra, ha⟩ := DensePolynomialPrograms.addCmd_eval p 1 M hB r2 xs ys width (fun _ => []) hw
  have hatt := compiled_halt_trace ha 8 8
  have hadd := eval_call_lifted DensePolynomialPrograms.program id addPorts
    (state r2 M.bits width x y dimensions x y [] []) Function.injective_id addPorts_injective hatt
  rw [embed_add, embed_add] at hadd
  let r3 := readRegs ra 0 1 none
  have hcopy := copy_bank ra M.bits width x y dimensions sum
  obtain ⟨rf, hs⟩ := SubexpPointBankStream.program_trace hB (pointWords p M xs ys) r3 width [] hw
  rw [quartetStream_eq p _ width hw, List.append_nil] at hs
  have hstream := eval_call_lifted SubexpPointBankStream.program id streamPorts
    (state r3 M.bits width x y dimensions sum [] sum []) Function.injective_id streamPorts_injective hs
  rw [embed_stream, embed_stream] at hstream
  have h := compiled_halt_trace
    (Eval.seq h1 (Eval.seq h2 (Eval.seq hadd (Eval.seq hcopy hstream)))) 22 21
  refine ⟨rf, _, ?_, h⟩
  have hsum : sum.length = xs.length * baseWidth p 1 := by
    dsimp [sum]
    rw [DensePolynomialLoop.flatten_length, pointWords_length p M xs ys hlen]
  have hx : x.length = xs.length * baseWidth p 1 := DensePolynomialLoop.flatten_length xs
  have hy : y.length = xs.length * baseWidth p 1 := by
    dsimp [y]; rw [DensePolynomialLoop.flatten_length, ← hlen]
  rw [← hlen] at hn
  rw [hx, hy, hsum, pointWords_length p M xs ys hlen]
  unfold steps
  nlinarith

/-- The full concrete trace and the canonicality needed before target-width
padding are provided together, without any additional output premise. -/
theorem program_primitive (xs ys : List (Word (baseWidth p 1))) (hlen : xs.length = ys.length)
    (regs : Fin 8 → Bool) (width dimensions : List Bool) (hw : width.length = baseWidth p 1) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * steps xs.length (baseWidth p 1))
      (primitiveCfg program
        ((ready regs M.bits width (DensePolynomialLoop.flatten xs) (DensePolynomialLoop.flatten ys)
          dimensions [] []).withPC (some program.entry)))
      (primitiveCfg program
        ((ready rf M.bits width (DensePolynomialLoop.flatten xs) (DensePolynomialLoop.flatten ys)
          dimensions (DensePolynomialLoop.flatten (pointWords p M xs ys))
          (quartetStream p (pointWords p M xs ys))).withPC none)) ∧
      (∀ w ∈ pointWords p M xs ys, BinaryArithmetic.toNat w.val < p) ∧
      (pointWords p M xs ys).map (fun w => BinaryArithmetic.toNat w.val) =
        List.zipWith (fun x y : Word (baseWidth p 1) => (BinaryArithmetic.toNat x.val + BinaryArithmetic.toNat y.val) % p) xs ys := by
  obtain ⟨rf, h⟩ := program_runs p M xs ys hlen regs width dimensions hw
  exact ⟨rf, primitive_execution _ h, pointWords_canonical p M xs ys hlen,
    pointWords_values p M xs ys hlen⟩

end SubexponentialSAT.SubexpPointBank

end OAI.Algorithms
