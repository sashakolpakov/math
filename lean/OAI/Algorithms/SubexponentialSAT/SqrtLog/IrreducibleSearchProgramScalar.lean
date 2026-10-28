import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramEnumeration
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# Fixed truth-table arithmetic for the irreducible search over F₃

The six input bits select one of 64 *static* leaves. No parameter of the
polynomial search occurs in this instruction table. The two output bits
encode the multiply-add `s + a*b` in the same two-bit scalar format as the
audited tuple generator.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

abbrev writePair {R S : ℕ} (lo hi : Fin R) (bits : Bool × Bool) : Cmd R S :=
  .seq (.atom (.set lo bits.1)) (.atom (.set hi bits.2))

def writtenPair {R S : ℕ} (lo hi : Fin R) (bits : Bool × Bool)
    (d : State R S) : State R S :=
  (Atom.set hi bits.2).eval ((Atom.set lo bits.1).eval d)

theorem writePair_eval {R S : ℕ} (lo hi : Fin R) (bits : Bool × Bool)
    (d : State R S) : Eval (writePair lo hi bits) 2 d (writtenPair lo hi bits d) :=
  (Eval.atom _ _).seq (Eval.atom _ _)

/-- Finite synthesis from a fixed list of input registers. Only register
branches and constant bit assignments occur in the resulting command. -/
def truthTable {R S : ℕ} (lo hi : Fin R) :
    List (Fin R) → (List Bool → Bool × Bool) → Cmd R S
  | [], f => writePair lo hi (f [])
  | i :: is, f => .ite i
      (truthTable lo hi is (fun bs => f (true :: bs)))
      (truthTable lo hi is (fun bs => f (false :: bs)))

theorem truthTable_eval {R S : ℕ} (lo hi : Fin R)
    (inputs : List (Fin R)) (f : List Bool → Bool × Bool) (d : State R S) :
    Eval (truthTable lo hi inputs f) (inputs.length + 2) d
      (writtenPair lo hi (f (inputs.map d.regs)) d) := by
  induction inputs generalizing f with
  | nil => exact writePair_eval lo hi (f []) d
  | cons i is ih =>
      cases h : d.regs i with
      | false =>
          have he := Eval.ite_false (yes := truthTable lo hi is (fun bs => f (true :: bs)))
            h (ih (fun bs => f (false :: bs)))
          simpa [truthTable, h, Nat.add_assoc] using he
      | true =>
          have he := Eval.ite_true (no := truthTable lo hi is (fun bs => f (false :: bs)))
            h (ih (fun bs => f (true :: bs)))
          simpa [truthTable, h, Nat.add_assoc] using he

def scalarBits (a : IrreducibleSearch.F) : Bool × Bool :=
  (a.val == 1, a.val == 2)

def scalarValue (a b : Bool) : IrreducibleSearch.F :=
  (if a then 1 else 0) + (if b then 2 else 0)

@[simp] theorem scalarValue_bits (a : IrreducibleSearch.F) :
    scalarValue (scalarBits a).1 (scalarBits a).2 = a := by
  apply ZMod.val_injective
  have ha : a.val < 3 := a.val_lt
  interval_cases h : a.val <;>
    simp [scalarValue, scalarBits, h, ZMod.val_ofNat, ZMod.val_one 3]

theorem scalarBits_encoding (a : IrreducibleSearch.F) :
    [(scalarBits a).1, (scalarBits a).2] =
      SubexpEnumerationPayload.scalarBits a :=
  by
    have hw : SubexpEnumerationPayload.scalarWidth 3 = 2 := by
      have hl : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
      simp only [SubexpEnumerationPayload.scalarWidth, hl]
    unfold SubexpEnumerationPayload.scalarBits
    rw [hw]
    fin_cases a <;> decide

def multiplyAddBits (bits : List Bool) : Bool × Bool :=
  scalarBits
    (scalarValue (bits[4]?.getD false) (bits[5]?.getD false) +
      scalarValue (bits[0]?.getD false) (bits[1]?.getD false) *
      scalarValue (bits[2]?.getD false) (bits[3]?.getD false))

abbrev multiplyAddCommand : Cmd 8 1 := truthTable 6 7 [0, 1, 2, 3, 4, 5] multiplyAddBits

abbrev multiplyAddProgram : Program 8 1 (size multiplyAddCommand + 1) :=
  compiled multiplyAddCommand 0 0

theorem multiplyAdd_controlSize : size multiplyAddCommand + 1 = 192 := by decide

theorem multiplyAdd_eval (a b s : IrreducibleSearch.F) (d : State 8 1)
    (ha0 : d.regs 0 = (scalarBits a).1) (ha1 : d.regs 1 = (scalarBits a).2)
    (hb0 : d.regs 2 = (scalarBits b).1) (hb1 : d.regs 3 = (scalarBits b).2)
    (hs0 : d.regs 4 = (scalarBits s).1) (hs1 : d.regs 5 = (scalarBits s).2) :
    Eval multiplyAddCommand 8 d (writtenPair 6 7 (scalarBits (s + a * b)) d) := by
  have he := truthTable_eval (S := 1) (6 : Fin 8) 7 [0, 1, 2, 3, 4, 5]
    multiplyAddBits d
  convert he using 1 ;
    simp only [ List.map_cons, List.map_nil, ha0, ha1,
      hb0, hb1, hs0, hs1, multiplyAddBits, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, scalarValue_bits]

theorem multiplyAdd_stacks (a b s : IrreducibleSearch.F) (d : State 8 1) :
    (writtenPair 6 7 (scalarBits (s + a * b)) d).stacks = d.stacks := rfl

theorem multiplyAdd_output (a b s : IrreducibleSearch.F) (d : State 8 1) :
    (writtenPair 6 7 (scalarBits (s + a * b)) d).regs 6 =
        (scalarBits (s + a * b)).1 ∧
    (writtenPair 6 7 (scalarBits (s + a * b)) d).regs 7 =
        (scalarBits (s + a * b)).2 := by
  simp [writtenPair, Atom.eval, Atom.instr, State.ofCfg, execInstr]

theorem multiplyAdd_run (a b s : IrreducibleSearch.F) (d : State 8 1)
    (ha0 : d.regs 0 = (scalarBits a).1) (ha1 : d.regs 1 = (scalarBits a).2)
    (hb0 : d.regs 2 = (scalarBits b).1) (hb1 : d.regs 3 = (scalarBits b).2)
    (hs0 : d.regs 4 = (scalarBits s).1) (hs1 : d.regs 5 = (scalarBits s).2) :
    Trace multiplyAddProgram 9
      (d.withPC (some multiplyAddProgram.entry))
      ((writtenPair 6 7 (scalarBits (s + a * b)) d).withPC none) :=
  compiled_halt_trace (multiplyAdd_eval a b s d ha0 ha1 hb0 hb1 hs0 hs1) 0 0

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
