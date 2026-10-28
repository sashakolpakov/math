import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowGuard

namespace OAI.Algorithms

/-! Assemble a complete raw row from runtime scalar/cache tables. -/

namespace SubexponentialSAT.Subexp.UniversalRowDataProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)
open UniversalRowLoop (Tables Valid ready)
open UniversalRowFactorLoop (indexWord)

private theorem ready_same_stacks (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    {a b : Data} (h : ready t width rowWidth positions a) (hs : b.stacks = a.stacks) :
    ready t width rowWidth positions b := by
  rcases h with ⟨hv, hi, hn, hr, hp, hw, hwr, hidx, he⟩
  exact ⟨by simpa only [hs] using hv, by simpa only [hs] using hi,
    by simpa only [hs] using hn, by simpa only [hs] using hr,
    by simpa only [hs] using hp, by simpa only [hs] using hw,
    by simpa only [hs] using hwr, by simpa only [hs] using hidx,
    fun j hj => by simpa only [hs] using he j hj⟩

private theorem ready_update (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    {a b : Data} (h : ready t width rowWidth positions a) (port : Fin 32)
    (hp : port = 17 ∨ port = 31) (word : Word)
    (hs : b.stacks = Function.update a.stacks port word) : ready t width rowWidth positions b := by
  rcases hp with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hs] using h.values
    · simpa [hs] using h.inverses
    · simpa [hs] using h.negatives
    · simpa [hs] using h.rows
    · simpa [hs] using h.indices
    · simpa [hs] using h.width
    · simpa [hs] using h.rowWidth
    · simpa [hs] using h.index
    · intro j hj
      have he := h.empty j hj
      fin_cases j <;> simp_all []

abbrev active : Cmd 8 32 :=
  .seq (.call (copyProgram 28 17 15 (0 : Fin 8) 1)) UniversalRowLoop.loop

def activeCost (t : Tables) (width rowWidth : Word) (positions : List ℕ) : ℕ :=
  7 * (UniversalRowTermProgram.indices positions).length + 8 +
    RecordPrograms.budget (UniversalRowLoop.cost t width rowWidth positions)
      (positions.reverse.map indexWord)

theorem active_eval (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (valid : Valid t width rowWidth positions) (a : Data)
    (ha : ready t width rowWidth positions a) (h17 : a.stacks 17 = [])
    (h31 : a.stacks 31 = [false]) :
    ∃ n ≤ activeCost t width rowWidth positions, ∃ b : Data, Eval active n a b ∧
      b.stacks = Function.update a.stacks 31
        (Encoding.encodeList UniversalRowProgram.encodeTerm
          (positions.map (UniversalRowLoop.term t positions))) := by
  let a1 : Data := ⟨readRegs a.regs 0 1 none, copyStacks 28 17 a.stacks⟩
  have hc := TupleProgram.copy_eval 28 17 15 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a (ha.empty 15 (by simp))
  have hready : ready t width rowWidth positions a1 :=
    ready_update t width rowWidth positions ha 17 (Or.inl rfl) (a.stacks 28 ++ a.stacks 17) rfl
  obtain ⟨nl, hnl, next, hl, hn, ho, hf⟩ := UniversalRowLoop.loop_eval t width rowWidth positions
    valid a1 hready (by simpa [a1, copyStacks] using h31) (a1.regs 5) (a1.regs 6) (a1.regs 7)
  have hstart : RecordPrograms.state UniversalRowLoop.ports a1
      (a1.regs 5) (a1.regs 6) (a1.regs 7) (UniversalRowTermProgram.indices positions) [] = a1 := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a1, copyStacks, UniversalRowLoop.ports, h17] using ha.indices
    · simpa [a1, copyStacks, UniversalRowLoop.ports,
        UniversalRowFactorLoop.indexWord] using ha.index
  rw [hstart] at hl
  let b := RecordPrograms.state UniversalRowLoop.ports next false true false [] []
  refine ⟨7 * (a.stacks 28).length + 5 + nl, ?_, b, hc.seq hl, ?_⟩
  · rw [ha.indices]
    unfold activeCost
    omega
  · funext j
    by_cases hj31 : j = 31
    · subst j
      simpa [b, RecordPrograms.state, UniversalRowLoop.ports] using ho
    by_cases hj17 : j = 17
    · subst j
      simp [b, RecordPrograms.state, UniversalRowLoop.ports, h17]
    by_cases hj16 : j = 16
    · subst j
      simpa [b, RecordPrograms.state, UniversalRowLoop.ports,
        UniversalRowFactorLoop.indexWord] using ha.index
    · simp [b, RecordPrograms.state, UniversalRowLoop.ports, hj31, hj17, hj16,
        hf j hj31, a1, copyStacks]

def row (t : Tables) (positions : List ℕ) (delta limit : Word) : UniversalRowProgram.Row Word :=
  ⟨delta, if positions.length ≤ limit.length then positions.map (UniversalRowLoop.term t positions) else []⟩

abbrev command : Cmd 8 32 :=
  .seq UniversalRowGuard.command
    (.seq (TupleProgram.pushConst 31 0 false)
      (.seq (.ite 7 active (.base .skip)) UniversalRowTermFraming.row))

def cost (t : Tables) (width rowWidth : Word) (positions : List ℕ) (delta limit : Word) : ℕ :=
  10 * (UniversalRowTermProgram.indices positions).length + 13 * limit.length +
    6 * positions.length + 40 + activeCost t width rowWidth positions + 8 * delta.length + 11

theorem command_eval (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (valid : Valid t width rowWidth positions) (delta limit : Word) (a : Data)
    (ha : ready t width rowWidth positions a)
    (hd : a.stacks 18 = delta) (hlimit : a.stacks 13 = limit)
    (h14 : a.stacks 14 = []) (h17 : a.stacks 17 = []) (h31 : a.stacks 31 = []) :
    ∃ n ≤ cost t width rowWidth positions delta limit, ∃ b : Data,
      Eval command n a b ∧
      b.stacks = Function.update (Function.update a.stacks 18 []) 31
        (UniversalRowProgram.encodeRow (row t positions delta limit)) := by
  obtain ⟨ng, hng, a1, hg, hanswer, h1⟩ := UniversalRowGuard.command_eval
    (positions.reverse.map indexWord) limit a ha.indices hlimit
    (ha.empty 11 (by simp)) h14 (ha.empty 15 (by simp)) h17
  have ha1 := ready_same_stacks t width rowWidth positions ha h1
  let a2 := TupleProgram.pushedState (31 : Fin 32) (0 : Fin 8) false a1
  have hp := TupleProgram.pushConst_eval (31 : Fin 32) (0 : Fin 8) false a1
  have ha2 := ready_update t width rowWidth positions ha1 31 (Or.inr rfl)
    (false :: a1.stacks 31) (show a2.stacks = _ from rfl)
  have h2 : a2.stacks = Function.update a.stacks 31 [false] := by
    simp [a2, h1, h31]
  have hbranch : ∃ nb ≤ activeCost t width rowWidth positions + 1, ∃ a3 : Data,
      Eval (.ite 7 active (.base .skip)) nb a2 a3 ∧
      a3.stacks = Function.update a.stacks 31
        (Encoding.encodeList UniversalRowProgram.encodeTerm (row t positions delta limit).terms) := by
    by_cases h : positions.length ≤ limit.length
    · obtain ⟨na, hna, a3, he, hs⟩ := active_eval t width rowWidth positions valid a2 ha2
        (by simpa [h2] using h17) (by simp [h2])
      refine ⟨na + 1, by omega, a3, .ite_true ?_ he, ?_⟩
      · simpa [a2, TupleProgram.pushedState, h] using hanswer
      · simpa [row, h, h2] using hs
    · refine ⟨1, by omega, a2, .ite_false ?_ (.base (.skip _)), ?_⟩
      · simpa [a2, TupleProgram.pushedState, h] using hanswer
      · simpa [row, h, Encoding.encodeList] using h2
  obtain ⟨nb, hnb, a3, hb, h3⟩ := hbranch
  obtain ⟨b, hr, hbs⟩ := UniversalRowTermFraming.row_eval a3 delta
    (row t positions delta limit).terms (by simpa [h3] using hd) (by simp [h3])
    (by simpa [h3] using ha.empty 23 (by simp))
  refine ⟨ng + (2 + (nb + (8 * delta.length + 8))), ?_, b,
    hg.seq (hp.seq (hb.seq hr)), ?_⟩
  · simp only [List.length_map, List.length_reverse] at hng
    unfold cost
    change ng ≤ 10 * (UniversalRowTermProgram.indices positions).length +
      13 * limit.length + 6 * positions.length + 40 at hng
    omega
  · rw [hbs, h3]
    funext j
    by_cases hj18 : j = 18 <;> by_cases hj31 : j = 31 <;>
      simp_all [row, Function.update_apply]

end SubexponentialSAT.Subexp.UniversalRowDataProgram

end OAI.Algorithms
