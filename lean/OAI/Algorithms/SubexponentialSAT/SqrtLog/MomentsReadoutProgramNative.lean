import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramState

namespace OAI.Algorithms

/-! End-to-end finite readout machine. Runtime words supply both loop counts,
the ambient shape, and the already constructed coefficient zero vector. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def inputHigh (zero t J shape : List Bool) : High :=
  {zero:=zero,t:=t,J:=J,shape:=shape}

def prepare : WideCode := .seq makeMask (wcopy 29 33 23)

theorem prepare_eval (regs : Fin 8 → Bool) (a : D) (zero t J shape : List Bool) :
    ∃ rr, Eval prepare (11*shape.length+7*J.length+12)
      (wideState regs a (inputHigh zero t J shape))
      (wideState rr a (outerHigh {inputHigh zero t J shape with mask:=List.replicate shape.length false} 0 J [])) := by
  obtain ⟨r1,h1⟩ := makeMask_eval regs a (inputHigh zero t J shape) rfl rfl
  let h := {inputHigh zero t J shape with mask:=List.replicate shape.length false}
  let d := wideState r1 a h
  have h2 := wcopy_eval d 29 33 23 (by decide) (by decide) (by decide) rfl
  have hd29 : (d.stacks 29).length = J.length := by
    simp [d, h, inputHigh, wideState, wideTapes ]
  rw [hd29] at h2
  have hend : wcopied d 29 33=wideState (readRegs r1 0 1 none) a (outerHigh h 0 J []) := by
    apply congrArg (StructuredProgram.State.mk (readRegs r1 0 1 none))
    funext i
    fin_cases i <;> simp [d,h,wideState,wideTapes,copyStacks,
      outerHigh,inputHigh,unary]
  rw [hend] at h2
  refine ⟨readRegs r1 0 1 none,?_⟩
  have hcost : (11 * shape.length + 7) + (7 * J.length + 5) =
      11 * shape.length + 7 * J.length + 12 := by omega
  simpa only [prepare, hcost, d, h, inputHigh] using h1.seq h2

def finish : WideCode := .seq (wtransfer 35 0) (.seq (wclear 31) (wclear 34))

theorem finish_eval (regs : Fin 8 → Bool) (a : D) (zero t J shape bits : List Bool)
    (ho : a.out=[]) :
    ∃ rr, Eval finish (3*bits.length+2*J.length+2*shape.length+9)
      (wideState regs a (outerHigh {inputHigh zero t J shape with mask:=List.replicate shape.length false}
        J.length [] bits.reverse))
      (wideState rr {a with out:=bits} (inputHigh zero t J shape)) := by
  let h := outerHigh {inputHigh zero t J shape with mask:=List.replicate shape.length false}
    J.length [] bits.reverse
  let d := wideState regs a h
  let d1 := wtransferred d 35 0
  let d2 := wcleared d1 31
  let d3 := wcleared d2 34
  have h1 := wtransfer_eval d 35 0 (by decide)
  have h2 := wclear_eval d1 31
  have h3 := wclear_eval d2 34
  have hend : d3=wideState d3.regs {a with out:=bits} (inputHigh zero t J shape) := by
    apply congrArg (StructuredProgram.State.mk d3.regs)
    funext i
    fin_cases i <;> simp [d2,d1,d,h,wtransferred,wcleared,wideState,wideTapes,
      outerHigh,inputHigh,unary,transferStacks,clearStacks,ho]
  have he := h1.seq (h2.seq h3)
  change Eval finish _ d d3 at he
  rw [hend] at he
  refine ⟨d3.regs,?_⟩
  convert he using 1 ;
    simp [d2,d1,d,h,wtransferred,wcleared,wideState,wideTapes,outerHigh,
      inputHigh,unary,transferStacks,clearStacks] ; omega

def command : WideCode := .seq prepare (.seq outer finish)
def program := compiled command 15 0

def readoutBudget (B d n t J : ℕ) (encoded : List (List Bool × List Bool)) : ℕ :=
  outerBudget B d n t encoded 0 J + 3*(J*(d*B))+9*J+13*n+21

theorem command_eval {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count t J shape : List Bool)
    (hc : count.length=d) (hw : width.length=baseWidth p e) (hs : shape.length=n) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    let bits := outputBits p e M cache entries t.length zero 0 J.length
    ∃ time ≤ readoutBudget (baseWidth p e) d n t.length J.length encoded, ∃ rr,
      Eval command time
        (wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
          (inputHigh (RingProgram.flat zero) t J shape))
        (wideState rr {MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [] with out:=bits}
          (inputHigh (RingProgram.flat zero) t J shape)) := by
  dsimp only
  let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
  let a := MomentsProgram.Dictionary.inputTape M.bits width count encoded [] []
  let h := {inputHigh (RingProgram.flat zero) t J shape with mask:=List.replicate shape.length false}
  obtain ⟨r1,h1⟩ := prepare_eval regs a (RingProgram.flat zero) t J shape
  obtain ⟨tm,htm,r2,h2⟩ := outer_eval p e M cache entries t.length zero width count h 0 J [] r1
    hc hw (by simp [h,hs]) rfl rfl
  let bits := outputBits p e M cache entries t.length zero 0 J.length
  obtain ⟨r3,h3⟩ := finish_eval r2 a (RingProgram.flat zero) t J shape bits rfl
  have h2' : Eval outer tm (wideState r1 a (outerHigh h 0 J []))
      (wideState r2 a (outerHigh h J.length [] bits.reverse)) := by
    simpa [bits] using h2
  refine ⟨_,?_,r3,h1.seq (h2'.seq h3)⟩
  have hl : bits.length=J.length*(d*baseWidth p e) := outputBits_length p e M cache entries t.length zero 0 J.length
  dsimp [readoutBudget]
  omega

theorem program_runsIn {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count t J shape : List Bool)
    (hc : count.length=d) (hw : width.length=baseWidth p e) (hs : shape.length=n) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    let bits := outputBits p e M cache entries t.length zero 0 J.length
    ∃ rr, RunsIn program (readoutBudget (baseWidth p e) d n t.length J.length encoded+1)
      ((wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
        (inputHigh (RingProgram.flat zero) t J shape)).withPC (some program.entry))
      ((wideState rr {MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [] with out:=bits}
        (inputHigh (RingProgram.flat zero) t J shape)).withPC none) := by
  obtain ⟨time,ht,rr,he⟩ := command_eval p e M cache entries zero regs width count t J shape hc hw hs
  exact ⟨rr,⟨time+1,by omega,compiled_halt_trace he 15 0⟩⟩

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
