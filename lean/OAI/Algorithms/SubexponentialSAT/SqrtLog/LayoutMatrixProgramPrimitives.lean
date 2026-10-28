import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Fixed stack and framing adapters for direct construction of all incidence
rows. The adapters expose native instruction counts and exact stack effects. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data (s : ℕ) := State 16 s
abbrev Code (s : ℕ) := Cmd 16 s

abbrev regs8 : Fin 8 → Fin 16 := Fin.castAdd 8
theorem regs8_injective : Function.Injective regs8 := Fin.castAdd_injective _ _

abbrev lift8 {s : ℕ} (c : Cmd 8 s) (input output : Fin s) : Code s :=
  .call (ProgramLinking.liftProgram (compiled c input output) regs8 id)

theorem lift8_eval {s : ℕ} (c : Cmd 8 s) (input output : Fin s) (d : Data s)
    (t : ℕ) (e : State 8 s)
    (he : Eval c t (projectState regs8 id d) e) :
    ∃ rf, Eval (lift8 c input output) (t+1) d ⟨rf,e.stacks⟩ := by
  let z := embedState regs8 id d e
  have hs := embedState_project regs8 (id : Fin s → Fin s) d
    regs8_injective Function.injective_id
  have hz : z = ⟨z.regs,e.stacks⟩ := by
    apply congrArg (StructuredProgram.State.mk z.regs)
    funext i
    exact embedState_stack regs8 id d e Function.injective_id i
  have h := eval_call_lifted (compiled c input output) regs8 id d
    regs8_injective Function.injective_id (compiled_halt_trace he input output)
  rw [hs] at h
  change Eval (lift8 c input output) (t+1) d z at h
  rw [hz] at h
  exact ⟨z.regs,h⟩

abbrev frame {s : ℕ} (src dst tmp : Fin s) (htd : tmp ≠ dst) : Code s :=
  lift8 (Subexp.MatrixProgramSupport.emitFrame src dst tmp htd) src dst

theorem frame_eval {s : ℕ} (src dst tmp : Fin s) (hsd : src ≠ dst)
    (hst : src ≠ tmp) (htd : tmp ≠ dst) (d : Data s) (ht : d.stacks tmp=[]) :
    ∃ e, Eval (frame src dst tmp htd) (8*(d.stacks src).length+9) d e ∧
      e.stacks=Function.update (Function.update d.stacks src []) dst
        (Encoding.frame (d.stacks src)++d.stacks dst) := by
  obtain ⟨e,he,hs⟩ := Subexp.MatrixProgramSupport.emitFrame_eval src dst tmp hsd hst htd
    (projectState regs8 id d) ht
  obtain ⟨rf,hf⟩ := lift8_eval _ src dst d _ e he
  refine ⟨⟨rf,e.stacks⟩,?_,hs⟩
  convert hf using 1 ; simp [projectState]

abbrev readerPorts {s : ℕ} (src dst : Fin s) (h : src ≠ dst) : RecordPrograms.Ports 16 s :=
  ⟨0,1,2,src,dst,by decide,by decide,by decide,h⟩

abbrev parse {s : ℕ} (src dst : Fin s) (h : src ≠ dst) : Code s :=
  .seq (.base (.atom (.pop src 2 3)))
    (.ite 2 (RecordPrograms.reader (readerPorts src dst h)) (.base .skip))

abbrev parsed {s : ℕ} (src dst : Fin s) (d : Data s) (rf : Fin 16 → Bool)
    (tail bits : List Bool) : Data s :=
  ⟨rf,Function.update (Function.update d.stacks src tail) dst bits⟩

theorem parse_nil {s : ℕ} (src dst : Fin s) (h : src ≠ dst)
    (d : Data s) (tail : List Bool) (hs : d.stacks src=false::tail)
    (hd : d.stacks dst=[]) :
    ∃ rf, rf 2=false ∧ Eval (parse src dst h) 2 d (parsed src dst d rf tail []) := by
  let a := (StructuredProgram.Atom.pop src 2 3).eval d
  have ha : a.regs 2=false := by
    simp [a,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr,hs,readRegs]
  have heq : a=parsed src dst d a.regs tail [] := by
    apply congrArg (StructuredProgram.State.mk a.regs)
    funext i
    by_cases hi : i=dst
    · subst i
      simp [StructuredProgram.Atom.instr,execInstr,hs,hd,Ne.symm h]
    · simp [StructuredProgram.Atom.instr,execInstr,hs,hi]
  refine ⟨a.regs,ha,?_⟩
  rw [←heq]
  exact (Eval.base (StructuredProgram.Eval.atom (.pop src 2 3) d)).seq
    (.ite_false ha (.base (.skip a)))

theorem parse_cons {s : ℕ} (src dst : Fin s) (h : src ≠ dst)
    (d : Data s) (bits tail : List Bool)
    (hs : d.stacks src=true::(Encoding.frame bits++tail)) (hd : d.stacks dst=[]) :
    ∃ rf, rf 2=true ∧ Eval (parse src dst h) (6*bits.length+6) d
      (parsed src dst d rf tail bits.reverse) := by
  let a := (StructuredProgram.Atom.pop src 2 3).eval d
  have ha : a.regs 2=true := by
    simp [a,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr,hs,readRegs]
  have has : a.stacks src=Encoding.frame bits++tail := by
    simp [a,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr,hs]
  have had : a.stacks dst=[] := by
    simp [a,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr,hd,Ne.symm h]
  let p := readerPorts src dst h
  have hp := RecordPrograms.state_eq_self p a (a.regs 0) (a.regs 1) (a.regs 2)
    _ [] rfl rfl rfl has had
  have hr := RecordPrograms.reader_eval p a bits tail [] (a.regs 0) (a.regs 1) (a.regs 2)
  rw [hp] at hr
  let e := RecordPrograms.state p a false true (a.regs 2) tail bits.reverse
  have hg : e.regs 2=true := by simpa [e,p,readerPorts,RecordPrograms.state] using ha
  have heq : e=parsed src dst d e.regs tail bits.reverse := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    by_cases hi : i=dst
    · subst i; simp [p,readerPorts]
    · by_cases hj : i=src
      · subst i; simp [p,readerPorts,h]
      · simp [p,a,
          StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr,hi,hj]
  refine ⟨e.regs,hg,?_⟩
  rw [←heq]
  have hh := (Eval.base (StructuredProgram.Eval.atom (.pop src 2 3) d)).seq
    (Eval.ite_true (no := .base .skip) ha hr)
  convert hh using 1
  · omega
  · simp [e]

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
