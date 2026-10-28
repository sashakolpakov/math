import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableInitial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTablePowers

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def initialStore {B d : ℕ} (s : Store) (c : List.Vector (Word B) d)
    (oneWord zeroWord minusOne : Word B) : Store :=
  {s with left := oneWord.val, source := [], saved := [], count := [], vector := [], coefficients := [], minusOne := minusOne.val, tail := [], newTail := [], output := [], polynomial := wordBits c.val, zero := zeroWord.val, powers := [], rounds := []}

abbrev initializeVector : Cmd 8 27 := .seq (copy 22 11) (.seq literalScan finishVector)

def initializationBudget (B d : ℕ) : ℕ := d*(40*B+30)+20*B+40

theorem initialize_eval {B d : ℕ} (hd : 0 < d)
    (c : List.Vector (Word B) d) (oneWord zeroWord minusOne : Word B)
    (s : Store) (regs : Fin 8 → Bool) (hdegree : s.degree.length = d) :
    ∃ n ≤ initializationBudget B d, ∃ rf, Eval initializeVector n
      (state regs (initialStore s c oneWord zeroWord minusOne))
      (state rf (ready {s with powers := (wordBits (initialData d oneWord zeroWord).coefficients.val).reverse, rounds := []}
        c (initialData d oneWord zeroWord) zeroWord minusOne)) := by
  let a := initialStore s c oneWord zeroWord minusOne
  let ai := {a with count := s.degree}
  have hp := copy_store_eval a ai regs 22 11 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, ai, a, initialStore])
  obtain ⟨n, hn, rf, hs⟩ := literalScan_eval d oneWord zeroWord a
    (readRegs regs 1 3 none) s.degree hdegree (by simp [a, initialStore])
  have hb : literalBits d oneWord zeroWord = wordBits (initialData d oneWord zeroWord).coefficients.val :=
    (literalWords_bits d oneWord zeroWord).symm
  have ht : literalLast d oneWord zeroWord [] = (initialData d oneWord zeroWord).last.val := by
    rw [literalLast_independent d hd oneWord zeroWord [] zeroWord.val]
    exact literalLast_word d oneWord zeroWord zeroWord
  let b := {a with left := (literalEnd d oneWord zeroWord).val, count := [], newTail := (initialData d oneWord zeroWord).last.val, output := (wordBits (initialData d oneWord zeroWord).coefficients.val).reverse}
  have hs' : Eval literalScan n (state (readRegs regs 1 3 none) ai) (state rf b) := by
    simpa only [ai, b, a, initialStore, hb, ht, List.append_nil] using hs
  have hf := finishVector_eval b rf rfl rfl
  have hendLength : (literalEnd d oneWord zeroWord).val.length = B :=
    (literalEnd d oneWord zeroWord).property
  have hlastLength : (initialData d oneWord zeroWord).last.val.length = B :=
    (initialData d oneWord zeroWord).last.property
  refine ⟨(7*(tapes a 22).length+5) +
    (n + (2*b.left.length+13*b.output.length+2*b.tail.length+9*b.newTail.length+25)),
    ?_, readRegs rf 1 3 none, ?_⟩
  · simp [a, b, initialStore, tapes, hdegree, initializationBudget,
      hendLength, hlastLength]
    nlinarith
  · simpa only [initializeVector, ready, a, ai, b, initialStore, List.reverse_reverse, List.append_nil] using
      hp.seq (hs'.seq hf)

abbrev prepareRounds : Cmd 8 27 :=
  .seq (copy 22 26) (.seq (copy 22 26) (.seq popRound popRound))

def roundCounter (degree : List Bool) : List Bool := (degree ++ degree).tail.tail

@[simp] theorem roundCounter_length (degree : List Bool) :
    (roundCounter degree).length = 2*degree.length-2 := by
  simp [roundCounter]
  omega

theorem prepareRounds_eval (s : Store) (regs : Fin 8 → Bool) (hempty : s.rounds = []) :
    Eval prepareRounds (14*s.degree.length+12) (state regs s)
      (state (readRegs (readRegs (readRegs regs 1 3 none) 1 3 (s.degree ++ s.degree).head?) 1 3 (s.degree ++ s.degree).tail.head?)
        {s with rounds := roundCounter s.degree}) := by
  let s1 := {s with rounds := s.degree}
  let s2 := {s with rounds := s.degree ++ s.degree}
  let rr := readRegs regs 1 3 none
  have h1 := copy_store_eval s s1 regs 22 26 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s1, hempty])
  have h2 := copy_store_eval s1 s2 rr 22 26 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s2, s1])
  have h3 := popRound_eval s2 rr
  have h4 := popRound_eval {s2 with rounds := s2.rounds.tail} (readRegs rr 1 3 s2.rounds.head?)
  simp only [rr, readRegs_reset] at h2
  convert h1.seq (h2.seq (h3.seq h4)) using 1 <;>
    simp [s1, s2, tapes, roundCounter] <;>
    first | ring

/-- Put the accumulated power vectors back in forward order on port25. -/
abbrev finishPowers : Cmd 8 27 := .seq (transfer 25 9) (.seq (copy 9 25) (clear 9))

theorem finishPowers_eval (s : Store) (regs : Fin 8 → Bool) (hempty : s.source = []) :
    Eval finishPowers (12*s.powers.length+11) (state regs s)
      (state (readRegs regs 1 3 none) {s with powers := s.powers.reverse}) := by
  let s1 := {s with source := s.powers.reverse, powers := []}
  let s2 := {s1 with powers := s.powers.reverse}
  let s3 := {s2 with source := []}
  let rr := readRegs regs 1 3 none
  have h1 := transfer_store_eval s s1 regs 25 9 (by decide) (by
    funext i; fin_cases i <;> simp [transferStacks, tapes, s1, hempty])
  have h2 := copy_store_eval s1 s2 rr 9 25 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s2, s1])
  have h3 := clear_store_eval s2 s3 rr 9 (by
    funext i; fin_cases i <;> simp [clearStacks, tapes, s3])
  simp only [rr, readRegs_reset] at h2 h3
  convert h1.seq (h2.seq h3) using 1
  · simp [s1, s2, tapes]; omega
  · simp [s1, s2, s3, hempty]

abbrev preparePowers : Cmd 8 27 :=
  .seq initializeVector (.seq prepareRounds (.seq powerScan finishPowers))


def preparationBudget (B d : ℕ) : ℕ :=
  initializationBudget B d + 14*d+12 + 2*d*(roundBudget B d+2)+2 + 24*d*d*B+11

theorem preparationBudget_polynomial (B d : ℕ) :
    preparationBudget B d ≤ 50000*(d+1)^2*(B+1)^2 := by
  unfold preparationBudget initializationBudget roundBudget
  nlinarith [Nat.zero_le (d^2*B^2), Nat.zero_le (d^2*B), Nat.zero_le (d*B^2),
    Nat.zero_le (d*B), Nat.zero_le (d^2), Nat.zero_le (B^2)]

def allPowerBits (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    {d : ℕ} (c : List.Vector (Word (baseWidth p t)) d)
    (oneWord zeroWord minusOne : Word (baseWidth p t)) : List Bool :=
  wordBits (initialData d oneWord zeroWord).coefficients.val ++
    generatedBits p t M zeroWord minusOne c (2*d-2) (initialData d oneWord zeroWord)

theorem preparePowers_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (c : List.Vector (Word (baseWidth p t)) d) (oneWord zeroWord minusOne : Word (baseWidth p t))
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ n ≤ preparationBudget (baseWidth p t) d, ∃ rf, Eval preparePowers n
      (state regs (initialStore s c oneWord zeroWord minusOne))
      (state rf (ready {s with powers := allPowerBits p t M c oneWord zeroWord minusOne, rounds := []}
        c (iterData p t M zeroWord minusOne c (2*d-2) (initialData d oneWord zeroWord)) zeroWord minusOne)) := by
  let v := initialData d oneWord zeroWord
  let a := {s with powers := (wordBits v.coefficients.val).reverse, rounds := []}
  obtain ⟨ni, hni, ri, hi⟩ := initialize_eval hd c oneWord zeroWord minusOne s regs hdegree
  have hp := prepareRounds_eval (ready a c v zeroWord minusOne) ri rfl
  let rr := readRegs (readRegs (readRegs ri 1 3 none) 1 3 (s.degree ++ s.degree).head?) 1 3 (s.degree ++ s.degree).tail.head?
  obtain ⟨np, hnp, rp, hs⟩ := powerScan_eval p t M hd zeroWord minusOne c (2*d-2)
    v a rr (roundCounter s.degree) (by simp [hdegree]) hmod hw hdegree
  let b := ready {a with rounds := [], powers := (generatedBits p t M zeroWord minusOne c (2*d-2) v).reverse ++ a.powers}
    c (iterData p t M zeroWord minusOne c (2*d-2) v) zeroWord minusOne
  have hf := finishPowers_eval b rp rfl
  have hn : 2*d-2 ≤ 2*d := Nat.sub_le _ _
  have hn' : (2*d-2)+1 ≤ 2*d := by omega
  have hlength : b.powers.length ≤ 2*d*d*baseWidth p t := by
    simp only [b, ready, a, List.length_append, List.length_reverse, generatedBits_length,
      wordBits_length, List.Vector.length_val]
    calc
      (2*d-2)*d*baseWidth p t+d*baseWidth p t = ((2*d-2)+1)*(d*baseWidth p t) := by ring
      _ ≤ (2*d)*(d*baseWidth p t) := Nat.mul_le_mul_right _ hn'
      _ = 2*d*d*baseWidth p t := by ring
  have hfinish : 12*b.powers.length ≤ 24*d*d*baseWidth p t := by
    calc
      _ ≤ 12*(2*d*d*baseWidth p t) := Nat.mul_le_mul_left 12 hlength
      _ = _ := by ring
  refine ⟨ni + (14*s.degree.length+12 + (np + (12*b.powers.length+11))),
    ?_, readRegs rp 1 3 none, ?_⟩
  · have hmul := Nat.mul_le_mul_right (roundBudget (baseWidth p t) d+2) hn
    simp only [ready] at hp
    change ni + (14*s.degree.length+12 + (np + (12*b.powers.length+11))) ≤ _
    rw [hdegree]
    unfold preparationBudget
    omega
  · simpa only [preparePowers, a, b, v, rr, ready, allPowerBits, List.reverse_append,
      List.reverse_reverse] using hi.seq (hp.seq (hs.seq hf))

def program := compiled preparePowers 8 0

theorem program_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (c : List.Vector (Word (baseWidth p t)) d) (oneWord zeroWord minusOne : Word (baseWidth p t))
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ rf, RunsIn program (preparationBudget (baseWidth p t) d+1)
      ((state regs (initialStore s c oneWord zeroWord minusOne)).withPC (some program.entry))
      ((state rf (ready {s with powers := allPowerBits p t M c oneWord zeroWord minusOne, rounds := []}
        c (iterData p t M zeroWord minusOne c (2*d-2) (initialData d oneWord zeroWord)) zeroWord minusOne)).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := preparePowers_eval p t M hd c oneWord zeroWord minusOne s regs hmod hw hdegree
  exact ⟨rf, n+1, Nat.add_le_add_right hn 1, compiled_halt_trace he 8 0⟩

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
