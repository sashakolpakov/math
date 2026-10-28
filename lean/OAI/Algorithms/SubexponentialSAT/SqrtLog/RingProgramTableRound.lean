import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableData
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableFinish

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev prepareRound : Cmd 8 27 :=
  .seq (copy 21 16) (.seq (copy 22 11) (copy 24 0))

theorem prepareRound_eval (s : Store) (regs : Fin 8 → Bool)
    (hl : s.left = []) (hc : s.coefficients = []) (hn : s.count = []) :
    Eval prepareRound (7*s.polynomial.length+7*s.degree.length+7*s.zero.length+15)
      (state regs s)
      (state (readRegs regs 1 3 none) {s with left := s.zero, coefficients := s.polynomial, count := s.degree}) := by
  let s1 := {s with coefficients := s.polynomial}
  let s2 := {s1 with count := s.degree}
  let s3 := {s2 with left := s.zero}
  let rr := readRegs regs 1 3 none
  have h1 := copy_store_eval s s1 regs 21 16 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s1, hc])
  have h2 := copy_store_eval s1 s2 rr 22 11 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s2, s1, hn])
  have h3 := copy_store_eval s2 s3 rr 24 0 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s3, s2, s1, hl])
  simp only [rr, readRegs_reset] at h2 h3
  convert h1.seq (h2.seq h3) using 1
  simp [s1, s2, tapes]
  omega

def ready {B d : ℕ} (s : Store) (c : List.Vector (Word B) d) (v : VectorData B d)
    (zeroWord minusOne : Word B) : Store :=
  {s with left := [], source := [], saved := [], count := [], vector := wordBits v.coefficients.val, coefficients := [], minusOne := minusOne.val, tail := v.last.val, newTail := [], output := [], polynomial := wordBits c.val, zero := zeroWord.val}

abbrev round : Cmd 8 27 := .seq prepareRound (.seq coefficientScan finishVector)

def roundBudget (B d : ℕ) : ℕ := d*(18000*(B+1)^2+130*B+140)+30*B+50

private theorem roundBudget_covers (B d n : ℕ) (hd : 0 < d)
    (hn : n ≤ d * (18000 * (B + 1) ^ 2 + 102 * B + 90) + 2) :
    7 * (d * B) + 7 * d + 7 * B + 15 +
        (n + (2 * B + 13 * (d * B) + 2 * B + 9 * B + 25)) ≤
      d * (18000 * (B + 1) ^ 2 + 130 * B + 140) + 30 * B + 50 := by
  ring_nf at hn ⊢
  omega

theorem round_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (zeroWord minusOne : Word (baseWidth p t))
    (c : List.Vector (Word (baseWidth p t)) d) (v : VectorData (baseWidth p t) d)
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ n ≤ roundBudget (baseWidth p t) d, ∃ rf, Eval round n
      (state regs (ready s c v zeroWord minusOne))
      (state rf (ready {s with powers := (wordBits (advance p t M zeroWord minusOne c v).coefficients.val).reverse ++ s.powers}
        c (advance p t M zeroWord minusOne c v) zeroWord minusOne)) := by
  let pairs := c.val.zip v.coefficients.val
  let next := advance p t M zeroWord minusOne c v
  let a := ready s c v zeroWord minusOne
  have hp := prepareRound_eval a regs rfl rfl rfl
  obtain ⟨n, hn, rf, hs⟩ := coefficientScan_eval p t M v.last minusOne pairs zeroWord
    a (readRegs regs 1 3 none) s.degree (by simpa [pairs] using hdegree) hmod hw (by simp [a, ready])
  have hbits : outputBits p t M v.last minusOne pairs zeroWord = wordBits next.coefficients.val := by
    exact (outputWords_bits p t M v.last minusOne pairs zeroWord).symm
  have hlast : lastProduced p t M v.last minusOne pairs zeroWord [] = next.last.val := by
    rw [lastProduced_independent p t M v.last minusOne pairs zeroWord (by
      intro he
      have hlen : pairs.length = d := by simp [pairs]
      rw [he] at hlen
      simp at hlen
      omega) [] zeroWord.val]
    exact lastProduced_word p t M v.last minusOne pairs zeroWord zeroWord
  let b := {a with left := (lastPrevious pairs zeroWord).val, source := [], saved := [], vector := [], coefficients := [], tail := v.last.val, minusOne := minusOne.val, count := [], newTail := next.last.val, output := (wordBits next.coefficients.val).reverse}
  have hs' : Eval coefficientScan n
      (state (readRegs regs 1 3 none) {a with left := a.zero, coefficients := a.polynomial, count := a.degree})
      (state rf b) := by
    simpa only [a, ready, b, pairs, leftBits_zip, rightBits_zip, hbits, hlast, List.append_nil] using hs
  have hf := finishVector_eval b rf rfl rfl
  refine ⟨(7*a.polynomial.length+7*a.degree.length+7*a.zero.length+15) +
    (n + (2*b.left.length+13*b.output.length+2*b.tail.length+9*b.newTail.length+25)),
    ?_, readRegs rf 1 3 none, ?_⟩
  · have hlen : (wordBits next.coefficients.val).length = d*baseWidth p t := by simp
    have hprev : ((lastPrevious pairs zeroWord).val).length = baseWidth p t :=
      (lastPrevious pairs zeroWord).property
    have hvlast : v.last.val.length = baseWidth p t := v.last.property
    have hnlast : next.last.val.length = baseWidth p t := next.last.property
    have hz : zeroWord.val.length = baseWidth p t := zeroWord.property
    simp [a, ready, b, hdegree, hlen, roundBudget, hprev, hvlast, hnlast, hz,
      pairs] at hn ⊢
    apply roundBudget_covers (baseWidth p t) d n hd
    simpa [pairs] using hn
  · simpa only [round, a, b, ready, List.reverse_reverse, List.append_nil] using hp.seq (hs'.seq hf)

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
