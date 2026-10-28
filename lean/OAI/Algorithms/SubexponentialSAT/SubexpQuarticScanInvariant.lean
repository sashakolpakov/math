import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticCallback
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticByteSpec

namespace OAI.Algorithms

/-! # The invariant carried by the actual quartic divisor scans -/

namespace SubexponentialSAT.SubexpQuarticScanInvariant

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpQuarticCallback SubexpQuarticProducerControl

def baseValue (p : ℕ) (word : Word (baseWidth p 1)) : ZMod p :=
  SubexpQuarticByteSpec.readWord p word.val

def coefficientValue (p : ℕ) (bank : Fin 14 → Word (baseWidth p 1)) : Fin 4 → ZMod p :=
  fun i => baseValue p (bank (Fin.castAdd 10 i))

def sourceWord (p : ℕ) [Fact p.Prime] (a : ZMod p) : Word (baseWidth p 1) :=
  ⟨(SubexpEnumerationPayload.scalarCode p).block a, by
    simp [SubexpEnumerationPayload.scalarCode, SubexpLiftRing.baseWidth,
      SubexpEnumerationPayload.scalarWidth]⟩

@[simp] theorem sourceWord_value (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    baseValue p (sourceWord p a) = a :=
  SubexpQuarticByteSpec.readWord_block p a

theorem coefficientValue_eq_vector (p : ℕ) (bank : Fin 14 → Word (baseWidth p 1)) :
    coefficientValue p bank =
      (fun i => baseValue p (![bank 0, bank 1, bank 2, bank 3] i)) := by
  funext i
  fin_cases i <;> rfl

def Ready (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
    (c : Fin 4 → ZMod p) (d : Data) : Prop :=
  ∃ bank : Fin 14 → Word (baseWidth p 1),
    Represents p 1 M d bank ∧ baseValue p (bank 6) = -1 ∧ coefficientValue p bank = c ∧
    d.stacks 30 = [] ∧ d.stacks 32 = [] ∧ (d.stacks 31).length = baseWidth p 1

theorem ready_of_stacks_eq (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (c : Fin 4 → ZMod p)
    (a b : Data) (ha : Ready p M c a) (h : b.stacks = a.stacks) : Ready p M c b := by
  obtain ⟨bank, hb, hm, hc, h30, h32, h31⟩ := ha
  refine ⟨bank, ?_, hm, hc, ?_, ?_, ?_⟩
  · simpa only [Represents, h] using hb
  · simpa only [h] using h30
  · simpa only [h] using h32
  · simpa only [h] using h31

theorem inner_state_stack (base : Data) (v pr found : Bool)
    (src out : List Bool) (j : Fin 35) (h23 : j ≠ 23) (h24 : j ≠ 24) :
    (RecordPrograms.state innerPorts base v pr found src out).stacks j = base.stacks j :=
  RecordPrograms.state_stack_frame innerPorts base v pr found src out j h23 h24

theorem ready_inner_state (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (c : Fin 4 → ZMod p)
    (base : Data) (h : Ready p M c base) (v pr found : Bool) (src out : List Bool) :
    Ready p M c (RecordPrograms.state innerPorts base v pr found src out) := by
  obtain ⟨bank, hb, hm, hc, h30, h32, h31⟩ := h
  refine ⟨bank, ?_, hm, hc, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (inner_state_stack base v pr found src out (bankPort i)
        (bankPort_ne_large i 23 (by decide)) (bankPort_ne_large i 24 (by decide))).trans (hb.1 i)
    · intro i
      have hi := workPort_range i
      have h23 : workPort i ≠ 23 := by intro he; have := congrArg Fin.val he; omega
      have h24 : workPort i ≠ 24 := by intro he; have := congrArg Fin.val he; omega
      exact (inner_state_stack base v pr found src out (workPort i) h23 h24).trans (hb.2.1 i)
    · exact (inner_state_stack base v pr found src out 22 (by decide) (by decide)).trans hb.2.2
  · exact (inner_state_stack base v pr found src out 30 (by decide) (by decide)).trans h30
  · exact (inner_state_stack base v pr found src out 32 (by decide) (by decide)).trans h32
  · rw [inner_state_stack base v pr found src out 31 (by decide) (by decide)]
    exact h31

/-- A callback may overwrite divisor words four and five and its arithmetic
scratch words. Preserving the coefficients and minus-one word is sufficient
to reestablish the same candidate invariant. -/
theorem ready_of_transition (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (c : Fin 4 → ZMod p)
    (before after : Data) (hbefore : Ready p M c before)
    (bank : Fin 14 → Word (baseWidth p 1)) (hafter : Represents p 1 M after bank)
    (hkeep : ∀ i : Fin 7, i ≠ 4 → i ≠ 5 →
      after.stacks (bankPort (Fin.castAdd 7 i)) =
        before.stacks (bankPort (Fin.castAdd 7 i)))
    (h30 : after.stacks 30 = []) (h32 : after.stacks 32 = before.stacks 32)
    (h31 : after.stacks 31 = before.stacks 31) : Ready p M c after := by
  obtain ⟨old, hold, hm, hc, _, hc32, hc31⟩ := hbefore
  have heq : ∀ i : Fin 7, i ≠ 4 → i ≠ 5 → bank (Fin.castAdd 7 i) = old (Fin.castAdd 7 i) := by
    intro i hi4 hi5
    apply Subtype.ext
    exact (hafter.1 _).symm.trans ((hkeep i hi4 hi5).trans (hold.1 _))
  have h6 : bank 6 = old 6 := heq 6 (by decide) (by decide)
  have hcoeff : coefficientValue p bank = coefficientValue p old := by
    funext i
    fin_cases i
    · exact congrArg (baseValue p) (heq 0 (by decide) (by decide))
    · exact congrArg (baseValue p) (heq 1 (by decide) (by decide))
    · exact congrArg (baseValue p) (heq 2 (by decide) (by decide))
    · exact congrArg (baseValue p) (heq 3 (by decide) (by decide))
  exact ⟨bank, hafter, by simpa only [h6] using hm, hcoeff.trans hc, h30,
    h32.trans hc32, by simpa only [h31] using hc31⟩

end SubexponentialSAT.SubexpQuarticScanInvariant

end OAI.Algorithms
