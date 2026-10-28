import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramRegisterBase

namespace OAI.Algorithms

/-! Structural register frames for the concrete assignment callback.  These
lemmas concern arbitrary executions and impose no data or readiness invariant. -/
namespace SubexponentialSAT.SqrtLog.LeafAssignmentRegisterFrame
open SubexponentialSAT BitProgram StructuredCalls
open MomentsAssembly.RegisterFrame

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

private theorem ne_low (i j : Fin 40) (hi : 16 ≤ i.val) (hj : j.val < 16) :
    i ≠ j := by
  intro h
  have := congrArg Fin.val h
  omega

theorem branch {c d : Code} (test i : Fin 40)
    (hc : Preserves c i) (hd : Preserves d i) :
    Preserves (.ite test c d) i := by
  intro n a b h
  cases h with
  | ite_true _ ht => exact hc ht
  | ite_false _ ht => exact hd ht

theorem skip (i : Fin 40) : Preserves (.base .skip) i := by
  intro n a b h
  cases h with
  | base hb => cases hb; rfl

theorem setReg (j i : Fin 40) (v : Bool) (hi : 16 ≤ i.val) (hj : j.val < 16) :
    Preserves (.base (.atom (.set j v))) i := by
  have hij := ne_low i j hi hj
  intro n a b h
  cases h with
  | base hb =>
    cases hb with
    | atom => simp [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr,hij]

theorem pop (src : Fin 768) (v p i : Fin 40) (hi : 16 ≤ i.val)
    (hv : v.val < 16) (hp : p.val < 16) :
    Preserves (.base (.atom (.pop src v p))) i := by
  have hiv := ne_low i v hi hv
  have hip := ne_low i p hi hp
  intro n a b h
  cases h with
  | base hb =>
    cases hb with
    | atom => simp [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr,readRegs,hiv,hip]

theorem peek (src : Fin 768) (v p i : Fin 40) (hi : 16 ≤ i.val)
    (hv : v.val < 16) (hp : p.val < 16) :
    Preserves (.base (.atom (.peek src v p))) i := by
  have hiv := ne_low i v hi hv
  have hip := ne_low i p hi hp
  intro n a b h
  cases h with
  | base hb =>
    cases hb with
    | atom => simp [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr,readRegs,hiv,hip]

theorem copy (src dst tmp : Fin 768) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (.call (StackRoutines.copyProgram src dst tmp 0 1)) i := by
  have h0 := ne_low i 0 hi (by decide)
  have h1 := ne_low i 1 hi (by decide)
  apply MomentsAssembly.RegisterFrame.call
  intro q c
  fin_cases q <;> simp [execInstr,readRegs,h0,h1]

theorem reverse (src dst tmp : Fin 768) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (.call (StackRoutines.reverseProgram src dst tmp 0 1)) i := by
  have h0 := ne_low i 0 hi (by decide)
  have h1 := ne_low i 1 hi (by decide)
  apply MomentsAssembly.RegisterFrame.call
  intro q c
  fin_cases q <;> simp [execInstr,readRegs,h0,h1]

theorem lowLift {r s l : ℕ} (p : Program r s l)
    (reg : Fin r → Fin 40) (stk : Fin s → Fin 768)
    (hreg : ∀ j, (reg j).val < 16) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (.call (ProgramLinking.liftProgram p reg stk)) i :=
  MomentsAssembly.RegisterFrame.lifted p reg stk i (fun j => ne_low i (reg j) hi (hreg j))

theorem records (p : RecordPrograms.Ports 40 768) (c : Code)
    (ht : p.tag.val < 16) (hp : p.present.val < 16) (hf : p.found.val < 16)
    (i : Fin 40) (hi : 16 ≤ i.val) (hc : Preserves c i) :
    Preserves (RecordPrograms.iterate p c) i := by
  have hr : Preserves (RecordPrograms.reader p) i := by
    unfold RecordPrograms.reader
    apply lowLift
    · intro j
      unfold RecordPrograms.registerMap
      split <;> assumption
    · exact hi
  unfold RecordPrograms.iterate RecordPrograms.loop RecordPrograms.body RecordPrograms.atom
  exact fun {n} {a} {b} => seq (setReg p.found i false hi hf)
    (seq (pop p.source p.tag p.present i hi ht hp)
      (MomentsAssembly.RegisterFrame.loop p.tag i
        (seq hr (seq hc
          (branch p.found i (setReg p.tag i false hi ht)
            (pop p.source p.tag p.present i hi ht hp))))))

end SubexponentialSAT.SqrtLog.LeafAssignmentRegisterFrame

end OAI.Algorithms
