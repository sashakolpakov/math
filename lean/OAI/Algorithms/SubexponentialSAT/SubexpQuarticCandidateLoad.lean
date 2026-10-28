import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticScanInvariant

namespace OAI.Algorithms

/-! # Saving and loading an actual quartic candidate record -/

namespace SubexponentialSAT.SubexpQuarticCandidateLoad

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpQuarticProducerControl SubexpQuarticCallback SubexpQuarticScanInvariant
open SubexpScanPrimitives SubexpEnumerationPayload SubexpTupleRefinement

def saved (d : Data) (bits : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update (Function.update d.stacks 33 bits) 24 bits.reverse) 29 []⟩

theorem saved_stack_frame (d : Data) (bits : List Bool) (j : Fin 35)
    (h24 : j ≠ 24) (h29 : j ≠ 29) (h33 : j ≠ 33) :
    (saved d bits).stacks j = d.stacks j := by
  simp [saved, h24, h29, h33]

theorem saved_register_frame (d : Data) (bits : List Bool) (j : Fin 14)
    (h0 : j ≠ 0) (h1 : j ≠ 1) : (saved d bits).regs j = d.regs j :=
  StackRoutines.readRegs_frame d.regs 0 1 j none h0 h1

/-- The reversed parser payload is duplicated before being consumed. The
saved output word is in forward coefficient order. -/
theorem save_eval (d : Data) (bits : List Bool)
    (hinput : d.stacks 29 = bits.reverse) (h24 : d.stacks 24 = [])
    (h27 : d.stacks 27 = []) :
    Eval (.seq (clear 33) (.seq (copy 29 24) (transfer 29 33)))
      (2 * (d.stacks 33).length + 10 * bits.length + 11) d (saved d bits) := by
  let a : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 33 d.stacks⟩
  let b := afterCopy a 29 24 0 1
  have hclear := Subexp.TupleProgram.clear_eval (33 : Fin 35) (0 : Fin 14) 1 d
  have hcopy := SubexpScanPrimitives.copy_eval a 29 24 27 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simpa [a, StackRoutines.clearStacks] using h27)
  have htransfer := SubexpScanPrimitives.transfer_eval b 29 33 0 1 (by decide) (by decide)
  have ha29 : a.stacks 29 = bits.reverse := by simpa [a, StackRoutines.clearStacks] using hinput
  have hb29 : b.stacks 29 = bits.reverse := by
    simpa [b, afterCopy, StackRoutines.copyStacks] using ha29
  have hend : afterTransfer b 29 33 0 1 = saved d bits := by
    apply state_ext
    · simp [a, b, afterCopy, afterTransfer, saved, StackRoutines.readRegs_reset]
    · funext j
      by_cases hj29 : j = 29
      · subst j
        simp [saved, afterTransfer, StackRoutines.transferStacks]
      · by_cases hj24 : j = 24
        · subst j
          simp [a, b, afterCopy, afterTransfer, saved, StackRoutines.clearStacks,
            StackRoutines.copyStacks, StackRoutines.transferStacks, h24, hinput]
        · by_cases hj33 : j = 33
          · subst j
            simp [a, b, afterCopy, afterTransfer, saved, StackRoutines.clearStacks,
              StackRoutines.copyStacks, StackRoutines.transferStacks, hinput]
          · simp [a, b, afterCopy, afterTransfer, saved, StackRoutines.clearStacks,
              StackRoutines.copyStacks, StackRoutines.transferStacks, hj29, hj24, hj33]
  have he := Eval.seq hclear (Eval.seq hcopy htransfer)
  rw [hend] at he
  simpa only [clear, copy, transfer, ha29, hb29, List.length_reverse,
    show 2 * (d.stacks 33).length + 3 +
      (7 * bits.length + 5 + (3 * bits.length + 3)) =
      2 * (d.stacks 33).length + 10 * bits.length + 11 by omega] using he

theorem saved_represents (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (d : Data) (bits : List Bool)
    (bank : Fin 14 → Word (baseWidth p 1)) (h : Represents p 1 M d bank) :
    Represents p 1 M (saved d bits) bank := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (saved_stack_frame d bits (bankPort i)
      (bankPort_ne_large i 24 (by decide)) (bankPort_ne_large i 29 (by decide))
      (bankPort_ne_large i 33 (by decide))).trans (h.1 i)
  · intro i
    have hi := workPort_range i
    have h24 : workPort i ≠ 24 := by intro he; have := congrArg Fin.val he; omega
    have h29 : workPort i ≠ 29 := by intro he; have := congrArg Fin.val he; omega
    have h33 : workPort i ≠ 33 := by intro he; have := congrArg Fin.val he; omega
    exact (saved_stack_frame d bits (workPort i) h24 h29 h33).trans (h.2.1 i)
  · exact (saved_stack_frame d bits 22 (by decide) (by decide) (by decide)).trans h.2.2

def coefficientWords (p : ℕ) [Fact p.Prime] (c : Fin 4 → ZMod p) :
    List (Fin 14 × Word (baseWidth p 1)) :=
  [(0, sourceWord p (c 0)), (1, sourceWord p (c 1)),
    (2, sourceWord p (c 2)), (3, sourceWord p (c 3))]

theorem coefficientWords_payload (p : ℕ) [Fact p.Prime] (c : Fin 4 → ZMod p) :
    SubexpQuarticRecordLoad.payload (wordAssignments p 1 (coefficientWords p c)) =
      encodeTuple (scalarCode p) c := by
  simp [coefficientWords, wordAssignments, SubexpQuarticRecordLoad.payload, sourceWord,
    encodeTuple, List.ofFn_succ, StackEncoding.encodeDataStack]

theorem coefficientWords_length (p : ℕ) [Fact p.Prime] (c : Fin 4 → ZMod p) :
    (encodeTuple (scalarCode p) c).length = 4 * baseWidth p 1 := by
  simp [encodeTuple, scalarCode, baseWidth, scalarWidth]
  omega

/-- The incoming candidate is saved exactly and all four coefficients are
physically loaded into the scalar bank. No candidate data is supplied by the
proof: it is consumed from the parser's reversed payload on stack 29. -/
theorem load_eval (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (c old : Fin 4 → ZMod p)
    (d : Data) (hd : Ready p M old d)
    (hinput : d.stacks 29 = (encodeTuple (scalarCode p) c).reverse)
    (h24 : d.stacks 24 = []) (h27 : d.stacks 27 = [])
    (h33 : (d.stacks 33).length ≤ 4 * baseWidth p 1) :
    ∃ n next,
      n ≤ 124 * baseWidth p 1 + 70 ∧ Eval loadCandidate n d next ∧ Ready p M c next ∧
      next.stacks 24 = [] ∧ next.stacks 29 = [] ∧
      next.stacks 33 = encodeTuple (scalarCode p) c ∧
      (∀ j : Fin 35, 23 ≤ j.val → j ≠ 24 → j ≠ 29 → j ≠ 30 → j ≠ 33 →
        next.stacks j = d.stacks j) ∧
      (∀ j : Fin 14, j ≠ 0 → j ≠ 1 → next.regs j = d.regs j) := by
  obtain ⟨bank, hbank, hminus, _, h30, h32, h31⟩ := hd
  let bits := encodeTuple (scalarCode p) c
  let a := saved d bits
  have ha : Represents p 1 M a bank := saved_represents p M d bits bank hbank
  have ha24 : a.stacks 24 =
      (SubexpQuarticRecordLoad.payload (wordAssignments p 1 (coefficientWords p c))).reverse := by
    simp [a, saved, coefficientWords_payload, bits]
  have ha30 : a.stacks 30 = [] :=
    (saved_stack_frame d bits 30 (by decide) (by decide) (by decide)).trans h30
  have ha32 : a.stacks 32 = [] :=
    (saved_stack_frame d bits 32 (by decide) (by decide) (by decide)).trans h32
  have ha31 : (a.stacks 31).length = baseWidth p 1 := by
    rw [saved_stack_frame d bits 31 (by decide) (by decide) (by decide)]
    exact h31
  obtain ⟨next, nextBank, he, hrep, hn24, hn30, hvalues, hkeep, hsf, hrf⟩ :=
    load_call p 1 M a bank ha (coefficientWords p c) (by simp [coefficientWords])
      ha24 ha30 ha32 ha31
  have hnext6 : nextBank 6 = bank 6 := by
    apply Subtype.ext
    exact (hrep.1 6).symm.trans
      ((hkeep 6 (by simp [coefficientWords])).trans (ha.1 6))
  have hcoeff : coefficientValue p nextBank = c := by
    funext i
    have hw : nextBank (Fin.castAdd 10 i) = sourceWord p (c i) := by
      apply Subtype.ext
      rw [← hrep.1]
      apply hvalues (Fin.castAdd 10 i, sourceWord p (c i))
      fin_cases i <;> simp [coefficientWords]
    change baseValue p (nextBank (Fin.castAdd 10 i)) = c i
    rw [hw, sourceWord_value]
  have hr : Ready p M c next := by
    refine ⟨nextBank, hrep, ?_, hcoeff, hn30, ?_, ?_⟩
    · simpa only [hnext6] using hminus
    · exact (hsf 32 (by decide) (by decide) (by decide)).trans ha32
    · simpa only [hsf 31 (by decide) (by decide) (by decide)] using ha31
  have hsave := save_eval d bits hinput h24 h27
  have hlen := coefficientWords_length p c
  refine ⟨(2 * (d.stacks 33).length + 10 * bits.length + 11) +
      (4 * (19 * baseWidth p 1 + 14) + 3), next, ?_, ?_, hr, hn24, ?_, ?_, ?_, ?_⟩
  · change bits.length = 4 * baseWidth p 1 at hlen
    omega
  · have hload : Eval (SubexpQuarticRecordLoad.readRecord 31 32 22 30 24 0 1 [0, 1, 2, 3])
        (4 * (19 * baseWidth p 1 + 14) + 3) a next := by
      simpa [coefficientWords, wordAssignments, bankPort] using he
    exact Eval.seq hsave hload
  · rw [hsf 29 (by decide) (by decide) (by decide)]
    simp [a, saved]
  · rw [hsf 33 (by decide) (by decide) (by decide)]
    simp [a, saved, bits]
  · intro j hj hj24 hj29 hj30 hj33
    exact (hsf j (by omega) hj24 hj30).trans
      (saved_stack_frame d bits j hj24 hj29 hj33)
  · intro j hj0 hj1
    exact (hrf j hj0 hj1).trans (saved_register_frame d bits j hj0 hj1)

end SubexponentialSAT.SubexpQuarticCandidateLoad

end OAI.Algorithms
