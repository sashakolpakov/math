import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-! A fixed seven-label routine reads a runtime-indexed bit and clears its
two inputs. An out-of-range read returns false, as `List.getD` does. -/

namespace SubexponentialSAT.Subexp.TypeBitProgram

open BitProgram

abbrev program : Program 3 2 7 where
  inputStack := 1
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 3, .pop 1 0 1 0,
    .pop 1 2 1 4, .pop 1 0 1 5, .branch 1 4 6, .halt]

abbrev cfg (pc : Option (Fin 7)) (regs : Fin 3 → Bool) (index bits : List Bool) : Cfg 3 2 7 :=
  ⟨pc, regs, ParserProgram.pair index bits⟩

def resultRegs (b : Bool) : Fin 3 → Bool := ![false,false,b]

def cost : List Bool → List Bool → ℕ
  | [], bits => 2 * bits.tail.length + 6
  | _ :: rest, bits => 3 + cost rest bits.tail

theorem cost_le (index bits : List Bool) : cost index bits ≤ 3 * index.length + 2 * bits.length + 6 := by
  induction index generalizing bits with
  | nil => simp only [cost,List.length_nil,Nat.mul_zero,Nat.zero_add,List.length_tail]; omega
  | cons b index ih =>
      have h := ih bits.tail
      have ht : bits.tail.length ≤ bits.length := by simp only [List.length_tail]; omega
      simp only [cost,List.length_cons]
      omega

theorem trace (index bits : List Bool) (regs : Fin 3 → Bool) :
    Trace program (cost index bits) (cfg (some 0) regs index bits)
      (cfg none (resultRegs (bits.getD index.length false)) [] []) := by
  induction index generalizing bits regs with
  | nil =>
      let r1 := readRegs regs 0 1 none
      let r2 := readRegs r1 2 1 bits.head?
      have ht := StackRoutines.clear_trace program 1 0 1 4 5 6 rfl rfl r2
        (ParserProgram.pair [] bits.tail)
      have hh := StackRoutines.halt_after_trace program ht 6 rfl rfl
      have hf : ⟨none, readRegs r2 0 1 none,
          StackRoutines.clearStacks 1 (ParserProgram.pair [] bits.tail)⟩ =
          cfg none (resultRegs (bits.getD 0 false)) [] [] := by
        apply congrArg₂ (fun (rs : Fin 3 → Bool) (ss : Fin 2 → List Bool) => (⟨none,rs,ss⟩ : Cfg 3 2 7))
        · funext i
          fin_cases i <;> simp [r2,r1,readRegs,resultRegs,List.getD_eq_getElem?_getD]
          cases bits <;> rfl
        · funext i
          fin_cases i <;> simp [StackRoutines.clearStacks,ParserProgram.pair]
      have hh' : Trace program (2 * bits.tail.length + 3) (cfg (some 4) r2 [] bits.tail)
          (cfg none (resultRegs (bits.getD 0 false)) [] []) := by
        simpa only [cfg,StackRoutines.clearResult,ParserProgram.pair,Matrix.cons_val_one,
          Matrix.head_cons, hf, ite_eq_right (by decide : (1 : Fin 2) ≠ 0), Nat.add_assoc] using hh
      have hs : Trace program 3 (cfg (some 0) regs [] bits) (cfg (some 4) r2 [] bits.tail) := by
        refine .cons (b := cfg (some 1) r1 [] bits) ?_ ?_
        · simp [step,cfg,execInstr,r1,ParserProgram.pair]
        refine .cons (b := cfg (some 3) r1 [] bits) ?_ ?_
        · simp [step,cfg,execInstr,r1,readRegs]
        refine .cons ?_ (.refl _)
        simp [step,cfg,execInstr,r2,ParserProgram.pair]
      simpa [cost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs.trans hh'
  | cons b index ih =>
      let r1 := readRegs regs 0 1 (some b)
      let r2 := readRegs r1 0 1 bits.head?
      have hs : Trace program 3 (cfg (some 0) regs (b :: index) bits)
          (cfg (some 0) r2 index bits.tail) := by
        refine .cons (b := cfg (some 1) r1 index bits) ?_ ?_
        · simp [step,cfg,execInstr,r1,ParserProgram.pair]
        refine .cons (b := cfg (some 2) r1 index bits) ?_ ?_
        · simp [step,cfg,execInstr,r1,readRegs]
        refine .cons ?_ (.refl _)
        simp [step,cfg,execInstr,r2,ParserProgram.pair]
      have hg : bits.tail.getD index.length false = bits.getD (b :: index).length false := by
        cases bits <;> simp
      simpa only [cost,hg] using hs.trans (ih bits.tail r2)

theorem runsIn (index bits : List Bool) (regs : Fin 3 → Bool) :
    RunsIn program (3 * index.length + 2 * bits.length + 6)
      (cfg (some program.entry) regs index bits)
      (cfg none (resultRegs (bits.getD index.length false)) [] []) :=
  ⟨cost index bits, cost_le index bits, trace index bits regs⟩

end SubexponentialSAT.Subexp.TypeBitProgram

end OAI.Algorithms
