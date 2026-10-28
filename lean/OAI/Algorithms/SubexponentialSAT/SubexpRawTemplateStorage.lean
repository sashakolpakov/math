import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssembly
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Actual storage operations for the raw template producer

All list construction uses fixed Boolean-stack programs. Port 218 is the
shared parser/framer temporary and 224 is a forward temporary. The ambient
288-stack state allows the node's static banks to remain untouched.
-/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Word := List Bool
abbrev Data := State 16 288
abbrev Code := Cmd 16 288

def transfer (src dst : Fin 288) : Code :=
  .call (StackRoutines.transferProgram src dst 0 1)

def copy (src dst : Fin 288) : Code :=
  .call (StackRoutines.copyProgram src dst 218 0 1)

def clear (src : Fin 288) : Code :=
  .call (StackRoutines.clearProgram src 0 1)

def cleared (src : Fin 288) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem transfer_eval (src dst : Fin 288) (hsd : src ≠ dst) (d : Data) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d
      (afterTransfer d src dst 0 1) :=
  SubexpScanPrimitives.transfer_eval d src dst 0 1 hsd (by decide)

theorem copy_eval (src dst : Fin 288) (hsd : src ≠ dst)
    (hs : src ≠ 218) (hd : (218 : Fin 288) ≠ dst)
    (d : Data) (h218 : d.stacks 218 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d
      (afterCopy d src dst 0 1) :=
  SubexpScanPrimitives.copy_eval d src dst 218 0 1 hsd hs hd (by decide) h218

theorem clear_eval (src : Fin 288) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

def pushBit (dst : Fin 288) (b : Bool) : Code :=
  .seq (.base (.atom (.set 0 b))) (.base (.atom (.push dst 0)))

def pushed (dst : Fin 288) (b : Bool) (d : Data) : Data :=
  ⟨Function.update d.regs 0 b, Function.update d.stacks dst (b :: d.stacks dst)⟩

theorem pushBit_eval (dst : Fin 288) (b : Bool) (d : Data) :
    Eval (pushBit dst b) 2 d (pushed dst b d) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 16) b) d)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push dst (0 : Fin 16)) _))
  simpa [pushBit, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

def parserPorts (src : Fin 288) (hs : src ≠ 218) : RecordPrograms.Ports 16 288 :=
  ⟨0, 1, 2, src, 218, by decide, by decide, by decide, hs⟩

def capture (src dst : Fin 288) (hs : src ≠ 218) : Code :=
  .seq (RecordPrograms.reader (parserPorts src hs)) (transfer 218 dst)

def captured (src dst : Fin 288) (bits tail : Word) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks src tail) dst bits⟩

theorem capture_eval (src dst : Fin 288) (hsd : src ≠ dst)
    (hs : src ≠ 218) (hd : (218 : Fin 288) ≠ dst) (bits tail : Word)
    (d : Data) (hsrc : d.stacks src = Encoding.frame bits ++ tail)
    (hdst : d.stacks dst = []) (h218 : d.stacks 218 = []) :
    Eval (capture src dst hs) (9 * bits.length + 7) d (captured src dst bits tail d) := by
  let p := parserPorts src hs
  let a := RecordPrograms.state p d false true (d.regs 2) tail bits.reverse
  have hin : RecordPrograms.state p d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ tail) [] = d :=
    RecordPrograms.state_eq_self p d _ _ _ _ _ rfl rfl rfl hsrc h218
  have hr := RecordPrograms.reader_eval p d bits tail []
    (d.regs 0) (d.regs 1) (d.regs 2)
  rw [hin] at hr
  simp only [List.append_nil] at hr
  have ht := transfer_eval 218 dst hd a
  have hlen : (a.stacks 218).length = bits.length := by
    simp [a, RecordPrograms.state, p, parserPorts]
  have he : afterTransfer a 218 dst 0 1 = captured src dst bits tail d := by
    apply state_ext
    · funext i
      by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;>
        simp [afterTransfer, a, RecordPrograms.state, p, parserPorts, captured,
          readRegs, h0, h1, h2]
    · funext i
      by_cases hi : i = dst
      · subst i
        simp [afterTransfer, StackRoutines.transferStacks, a, RecordPrograms.state,
          p, parserPorts, captured, hdst, hd.symm, hsd.symm]
      by_cases hi' : i = 218
      · subst i
        simp [afterTransfer, StackRoutines.transferStacks, a, RecordPrograms.state,
          p, parserPorts, captured, h218, hd, hs.symm]
      · simp [afterTransfer, StackRoutines.transferStacks, a, RecordPrograms.state,
          p, parserPorts, captured, hi, hi']
  have hh := hr.seq ht
  rw [he] at hh
  rw [hlen] at hh
  have hcost : (6 * bits.length + 4) + (3 * bits.length + 3) =
      9 * bits.length + 7 := by
    omega
  rw [hcost] at hh
  exact hh

def frameRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def framePorts (src dst : Fin 288) : Fin 3 → Fin 288 := ![src, dst, 218]

theorem frameRegs_injective : Function.Injective frameRegs := Fin.castAdd_injective _ _

theorem framePorts_injective (src dst : Fin 288)
    (hsd : src ≠ dst) (hs : src ≠ 218) (hd : dst ≠ 218) :
    Function.Injective (framePorts src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [framePorts]

def appendFrame (src dst : Fin 288) : Code :=
  .seq (.base (.atom (.set 2 true)))
    (.call (ProgramLinking.liftProgram SubexpBlockAssembly.frameBody frameRegs (framePorts src dst)))

def afterFrameRegs (regs : Fin 16 → Bool) : Fin 16 → Bool :=
  Function.update (Function.update (Function.update regs 0 false) 1 false) 2 true

def framed (src dst : Fin 288) (d : Data) : Data :=
  ⟨afterFrameRegs d.regs,
    Function.update d.stacks dst ((Encoding.frame (d.stacks src)).reverse ++ d.stacks dst)⟩

private def frameData (v p : Bool) (payload output : Word) : State 3 3 :=
  ⟨SubexpHornerProgram.triple v p true, SubexpHornerProgram.triple payload output []⟩

theorem appendFrame_eval (src dst : Fin 288)
    (hsd : src ≠ dst) (hs : src ≠ 218) (hd : dst ≠ 218)
    (d : Data) (h218 : d.stacks 218 = []) :
    Eval (appendFrame src dst) (8 * (d.stacks src).length + 7) d (framed src dst d) := by
  let set := (StructuredProgram.Atom.set (s := 288) 2 true).eval d
  have hset := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.set (s := 288) 2 true) d)
  have hp := framePorts_injective src dst hsd hs hd
  have hstart : embedState frameRegs (framePorts src dst) set
      (frameData (d.regs 0) (d.regs 1) (d.stacks src) (d.stacks dst)) = set := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegs_injective hp
    · intro i
      fin_cases i <;> simp [set, frameData, frameRegs, SubexpHornerProgram.triple,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
    · intros; rfl
    · intro i
      fin_cases i <;> simp [set, frameData, framePorts, SubexpHornerProgram.triple, h218,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
    · intros; rfl
  have hend : embedState frameRegs (framePorts src dst) set
      (frameData false false (d.stacks src)
        ((Encoding.frame (d.stacks src)).reverse ++ d.stacks dst)) = framed src dst d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameRegs_injective hp
    · intro i
      fin_cases i <;> simp [framed, afterFrameRegs, frameData, frameRegs,
        SubexpHornerProgram.triple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨2, h.symm⟩
      simp [framed, afterFrameRegs, set, h0, h1, h2, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
        execInstr]
    · intro i
      fin_cases i <;> simp [framed, frameData, framePorts, SubexpHornerProgram.triple,
        hsd, hd.symm, h218]
    · intro i hi
      have hdst : i ≠ dst := fun h => hi ⟨1, h.symm⟩
      simp [framed, set, hdst, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
  have h := eval_call_lifted SubexpBlockAssembly.frameBody frameRegs (framePorts src dst) set
    frameRegs_injective hp
    (a := frameData (d.regs 0) (d.regs 1) (d.stacks src) (d.stacks dst))
    (b := frameData false false (d.stacks src)
      ((Encoding.frame (d.stacks src)).reverse ++ d.stacks dst))
    (SubexpBlockAssembly.frameBody_trace (d.stacks src) (d.stacks dst) (d.regs 0) (d.regs 1))
  rw [hstart, hend] at h
  have htotal := Eval.seq hset h
  have hcost : 1 + (8 * (d.stacks src).length + 6) =
      8 * (d.stacks src).length + 7 := by
    omega
  rw [hcost] at htotal
  exact htotal

@[simp] theorem afterFrameRegs_update_zero (regs : Fin 16 → Bool) (b : Bool) :
    afterFrameRegs (Function.update regs 0 b) = afterFrameRegs regs := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;>
    simp [afterFrameRegs, h0, h1, h2]

def record (bits : Word) : Word := true :: Encoding.frame bits
def appendRecord (src dst : Fin 288) : Code :=
  .seq (pushBit dst true) (appendFrame src dst)

def recorded (src dst : Fin 288) (d : Data) : Data :=
  ⟨afterFrameRegs d.regs,
    Function.update d.stacks dst ((record (d.stacks src)).reverse ++ d.stacks dst)⟩

theorem appendRecord_eval (src dst : Fin 288)
    (hsd : src ≠ dst) (hs : src ≠ 218) (hd : dst ≠ 218)
    (d : Data) (h218 : d.stacks 218 = []) :
    Eval (appendRecord src dst) (8 * (d.stacks src).length + 9) d (recorded src dst d) := by
  have hp := pushBit_eval dst true d
  have htmp : (pushed dst true d).stacks 218 = [] := by simp [pushed, hd.symm, h218]
  have hf := appendFrame_eval src dst hsd hs hd (pushed dst true d) htmp
  have hlen : ((pushed dst true d).stacks src).length = (d.stacks src).length := by
    simp [pushed, hsd]
  have he : framed src dst (pushed dst true d) = recorded src dst d := by
    apply state_ext
    · simp [framed, pushed, recorded]
    · funext i
      by_cases hi : i = dst
      · subst i
        simp [framed, pushed, recorded, record, hsd, List.reverse_cons, List.append_assoc]
      · simp [framed, pushed, recorded, hi]
  have ht := hp.seq hf
  rw [he] at ht
  rw [hlen] at ht
  have hcost : 2 + (8 * (d.stacks src).length + 7) =
      8 * (d.stacks src).length + 9 := by
    omega
  rw [hcost] at ht
  exact ht

/-- Preserve the raw source while appending its bits to a reversed buffer. -/
def appendBits (src dst : Fin 288) : Code := .seq (copy src 224) (transfer 224 dst)

def appended (src dst : Fin 288) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update d.stacks dst ((d.stacks src).reverse ++ d.stacks dst)⟩

theorem appendBits_eval (src dst : Fin 288) (_hsd : src ≠ dst)
    (hs218 : src ≠ 218) (hs224 : src ≠ 224) (hd224 : (224 : Fin 288) ≠ dst)
    (d : Data) (h218 : d.stacks 218 = []) (h224 : d.stacks 224 = []) :
    Eval (appendBits src dst) (10 * (d.stacks src).length + 8) d (appended src dst d) := by
  have hc := copy_eval src 224 hs224 hs218 (by decide) d h218
  let a := afterCopy d src 224 0 1
  have ht := transfer_eval 224 dst hd224 a
  have hlen : (a.stacks 224).length = (d.stacks src).length := by
    simp [a, afterCopy, StackRoutines.copyStacks, h224]
  have he : afterTransfer a 224 dst 0 1 = appended src dst d := by
    apply state_ext
    · simp [a, afterCopy, afterTransfer, appended, StackRoutines.readRegs_reset]
    · funext i
      by_cases hi : i = dst
      · subst i
        simp [a, afterCopy, afterTransfer, appended, StackRoutines.copyStacks,
          StackRoutines.transferStacks, h224, hd224.symm]
      by_cases hi224 : i = 224
      · subst i
        simp [a, afterCopy, afterTransfer, appended, StackRoutines.copyStacks,
          StackRoutines.transferStacks, h224, hd224]
      · simp [a, afterCopy, afterTransfer, appended, StackRoutines.copyStacks,
          StackRoutines.transferStacks, hi, hi224]
  have hh := hc.seq ht
  rw [he] at hh
  rw [hlen] at hh
  have hcost : (7 * (d.stacks src).length + 5) +
      (3 * (d.stacks src).length + 3) = 10 * (d.stacks src).length + 8 := by
    omega
  rw [hcost] at hh
  exact hh

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
