import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgramFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgramABI
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialConstructor

namespace OAI.Algorithms

/-! Native beta evaluation.  The caller supplies actual coefficient arrays,
not evaluated row values.  Masters205..212 are preserved;220 is the result.
Work230/231/232 holds the framed row scan, choice scan and reverse buffer. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives

abbrev Store := Fin 256 → List Bool
abbrev Data := State 16 256
abbrev Code := Cmd 16 256

def popRow : Code := .base (.atom (.pop 230 0 1))
def popChoice : Code := .base (.atom (.pop 231 0 1))
def peekRow : Code := .base (.atom (.peek 230 0 1))

/-- Consume the outer list tag and physically decode one coefficient array. -/
def readRow : Code := .seq popRow
  (.seq (PerturbationBetaFrames.readFrame 230 232 (by decide))
    (PerturbationBetaFrames.transfer 232 246))

theorem popRow_run (s : Store) (b : Bool) (rest : List Bool)
    (hs : s 230=b::rest) :
    ExecutesIn popRow 1 s (Function.update s 230 rest) := by
  intro regs
  refine ⟨1,readRegs regs 0 1 (some b),by omega,?_⟩
  simpa [popRow,hs,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using
    (Eval.base (StructuredProgram.Eval.atom (.pop (230 : Fin 256) (0 : Fin 16) 1)
      (⟨regs,s⟩ : Data)))

theorem readRow_run (s : Store) (bits rest : List Bool)
    (hs : s 230=true::(Encoding.frame bits++rest))
    (h232 : s 232=[]) (h246 : s 246=[]) :
    ExecutesIn readRow (9*bits.length+8) s
      (Function.update (Function.update s 230 rest) 246 bits) := by
  have hp := popRow_run s true (Encoding.frame bits++rest) hs
  intro regs
  obtain ⟨np,rp,hnp,hep⟩ := hp regs
  let a : Data := ⟨rp,Function.update s 230 (Encoding.frame bits++rest)⟩
  have hr := PerturbationBetaFrames.readFrame_eval a 230 232 (by decide) bits rest (by simp [a])
  have ht := PerturbationBetaFrames.transfer_eval
    (PerturbationBetaFrames.afterFrame a 230 232 bits rest) 232 246 (by decide)
  have he : PerturbationBetaFrames.afterTransfer
      (PerturbationBetaFrames.afterFrame a 230 232 bits rest) 232 246 =
      (⟨readRegs (PerturbationBetaFrames.afterFrame a 230 232 bits rest).regs 0 1 none,
        Function.update (Function.update s 230 rest) 246 bits⟩ : Data) := by
    apply state_ext
    · rfl
    · funext i
      by_cases h0 : i=230 <;> by_cases h1 : i=232 <;> by_cases h2 : i=246 <;>
        simp [a,
          StackRoutines.transferStacks,h0,h1,h2,h232,h246]
  rw [he] at ht
  refine ⟨np+((6*bits.length+4)+(3*bits.length+3)),
    readRegs (PerturbationBetaFrames.afterFrame a 230 232 bits rest).regs 0 1 none,by omega,?_⟩
  have ht' : Eval (PerturbationBetaFrames.transfer 232 246) (3*bits.length+3)
      (PerturbationBetaFrames.afterFrame a 230 232 bits rest)
      (⟨readRegs (PerturbationBetaFrames.afterFrame a 230 232 bits rest).regs 0 1 none,
        Function.update (Function.update s 230 rest) 246 bits⟩ : Data) := by
    simpa [PerturbationBetaFrames.afterFrame,a,h232] using ht
  exact hep.seq (hr.seq ht')

/-- All changed ports are above the persistent native arithmetic region. -/
def lowFrame (base s : Store) : Prop := CRTLocalProgram.LowFrame base s

/-- Evaluate the current actual row, then add it to the existing beta. -/
def selected : Code :=
  .seq (copy 207 240) (.seq (copy 210 248)
    (.seq HornerProgram.modelCommand (.seq (copy 220 241)
      (.seq (CRTLocalProgram.binaryStep HornerProgram.Services.add)
        (.seq (clear 241) (.seq (clear 220)
          (SubexpPolynomialConstructor.move 240 220)))))))

def skip : Code := clear 246

def step : Code := .seq readRow (.seq popChoice (.ite 0 selected skip))
def body : Code := .seq step peekRow
def loop : Code := .while 0 body

def prepareInput : Code := .seq (copy 205 230) (.seq (copy 206 231)
  (.seq (copy 207 220) (.seq (copy 209 247) (copy 211 250))))
def finish : Code := .seq (clear 230) (.seq (clear 231)
  (.seq (clear 247) (clear 250)))

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
