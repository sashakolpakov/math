import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssembly

namespace OAI.Algorithms

/-! Execution proofs for the fixed prepared-block packer. -/

namespace SubexponentialSAT.SubexpBlockAssembly

open BitProgram StructuredCalls
open SubexpKernelControl (Word)

abbrev Executes (c : Code) (a b : Data) : Prop := ∃ n, Eval c n a b

theorem executes_seq {c d : Code} {a b e : Data}
    (hc : Executes c a b) (hd : Executes d b e) : Executes (.seq c d) a e := by
  obtain ⟨n, hn⟩ := hc
  obtain ⟨m, hm⟩ := hd
  exact ⟨n+m, Eval.seq hn hm⟩

def resetFlags (d : Data) : Data := ⟨fun _ => false, d.stacks⟩

theorem reset_eval (d : Data) : Eval reset 3 d (resetFlags d) := by
  let a0 := StructuredProgram.Atom.set (s := 22) (0 : Fin 3) false
  let a1 := StructuredProgram.Atom.set (s := 22) (1 : Fin 3) false
  let a2 := StructuredProgram.Atom.set (s := 22) (2 : Fin 3) false
  have h := Eval.seq (Eval.base (StructuredProgram.Eval.atom a0 d))
    (Eval.seq (Eval.base (StructuredProgram.Eval.atom a1 (a0.eval d)))
      (Eval.base (StructuredProgram.Eval.atom a2 (a1.eval (a0.eval d)))))
  have he : a2.eval (a1.eval (a0.eval d)) = resetFlags d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [a0,a1,a2,StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
        execInstr]
    · rfl
  change Eval (.seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 false))) (.base (.atom (.set 2 false))))) 3 d _
  simpa only [he] using h

theorem reset_exec (d : Data) : Executes reset d (resetFlags d) := ⟨3,reset_eval d⟩

def afterTransfer (src dst : Fin 22) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer_eval (src dst : Fin 22) (hne : src ≠ dst) (d : Data) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (afterTransfer src dst d) :=
  Eval.call _ (ListRegisterProgram.transfer_run src dst 0 1 hne (by decide) d.regs d.stacks)

theorem transfer_exec (src dst : Fin 22) (hne : src ≠ dst) (d : Data) :
    Executes (transfer src dst) d (afterTransfer src dst d) := ⟨_,transfer_eval src dst hne d⟩

def afterClear (src : Fin 22) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩

theorem clear_eval (src : Fin 22) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (afterClear src d) :=
  Eval.call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

theorem clear_exec (src : Fin 22) (d : Data) : Executes (clear src) d (afterClear src d) :=
  ⟨_,clear_eval src d⟩

def afterPush (dst : Fin 22) (bit : Bool) (d : Data) : Data :=
  ⟨Function.update d.regs 0 bit, Function.update d.stacks dst (bit :: d.stacks dst)⟩

theorem pushBit_eval (dst : Fin 22) (bit : Bool) (d : Data) :
    Eval (pushBit dst bit) 2 d (afterPush dst bit d) := by
  have h := Eval.seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set 0 bit) d))
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push dst 0)
      ((StructuredProgram.Atom.set (s := 22) 0 bit).eval d)))
  change Eval (.seq (.base (.atom (.set 0 bit))) (.base (.atom (.push dst 0)))) 2 d _
  simpa [afterPush, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

theorem pushBit_exec (dst : Fin 22) (bit : Bool) (d : Data) :
    Executes (pushBit dst bit) d (afterPush dst bit d) := ⟨2,pushBit_eval dst bit d⟩

def afterFrame (dst : Fin 22) (payload : Word) (d : Data) : Data :=
  ⟨SubexpHornerProgram.triple false false true,
    Function.update d.stacks dst ((Encoding.frame payload).reverse ++ d.stacks dst)⟩

private def literalData (v p c : Bool) (payload output : Word) : State 3 3 :=
  ⟨SubexpHornerProgram.triple v p c, SubexpHornerProgram.triple payload output []⟩

theorem appendFrame_eval (src dst : Fin 22) (hsd : src ≠ dst)
    (hs : src ≠ 20) (hd : dst ≠ 20) (d : Data) (htmp : d.stacks 20 = []) :
    Eval (appendFrame src dst) (8 * (d.stacks src).length + 7)
      d (afterFrame dst (d.stacks src) d) := by
  let ports := triplePorts src dst 20
  have hp : Function.Injective ports := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [ports,triplePorts]
  let middle : Data := ⟨Function.update d.regs 2 true, d.stacks⟩
  let a := literalData (d.regs 0) (d.regs 1) true (d.stacks src) (d.stacks dst)
  let b := literalData false false true (d.stacks src)
    ((Encoding.frame (d.stacks src)).reverse ++ d.stacks dst)
  have ha : embedState id ports middle a = middle := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id hp
    · intro i; fin_cases i <;> simp [middle,a,literalData,SubexpHornerProgram.triple]
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [middle,a,literalData,ports,triplePorts,
        SubexpHornerProgram.triple,htmp]
    · intros; rfl
  have hb : embedState id ports middle b = afterFrame dst (d.stacks src) d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id hp
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [b,literalData,afterFrame,ports,triplePorts,
        SubexpHornerProgram.triple,hsd,hd.symm,htmp]
    · intro i hi
      have hdi : i ≠ dst := fun h => hi ⟨1, by simpa [ports,triplePorts] using h.symm⟩
      simp [afterFrame,middle,hdi]
  have hcall := eval_call_lifted frameBody id ports middle Function.injective_id hp
    (a := a) (b := b) (frameBody_trace (d.stacks src) (d.stacks dst) (d.regs 0) (d.regs 1))
  rw [ha,hb] at hcall
  have hset : Eval (.base (.atom (.set 2 true))) 1 d middle := by
    simpa [middle,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using
      Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (s := 22) 2 true) d)
  have htotal := Eval.seq hset hcall
  have hcost : 1 + (8 * (d.stacks src).length + 6) =
      8 * (d.stacks src).length + 7 := by
    omega
  rw [hcost] at htotal
  exact htotal

theorem appendFrame_exec (src dst : Fin 22) (hsd : src ≠ dst)
    (hs : src ≠ 20) (hd : dst ≠ 20) (d : Data) (htmp : d.stacks 20 = []) :
    Executes (appendFrame src dst) d (afterFrame dst (d.stacks src) d) :=
  ⟨_,appendFrame_eval src dst hsd hs hd d htmp⟩

def record (payload : Word) : Word := true :: Encoding.frame payload

def afterRecord (dst : Fin 22) (payload : Word) (d : Data) : Data :=
  ⟨SubexpHornerProgram.triple false false true,
    Function.update d.stacks dst ((record payload).reverse ++ d.stacks dst)⟩

theorem appendRecord_eval (src dst : Fin 22) (hsd : src ≠ dst)
    (hs : src ≠ 20) (hd : dst ≠ 20) (d : Data) (htmp : d.stacks 20 = []) :
    Eval (appendRecord src dst) (8 * (d.stacks src).length + 9)
      d (afterRecord dst (d.stacks src) d) := by
  have h1 := pushBit_eval dst true d
  have h2 := appendFrame_eval src dst hsd hs hd (afterPush dst true d)
    (by simp [afterPush,hd.symm,htmp])
  have he : afterFrame dst ((afterPush dst true d).stacks src) (afterPush dst true d) =
      afterRecord dst (d.stacks src) d := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i = dst <;>
        simp [afterPush,record,hsd,List.reverse_cons,
          List.append_assoc,Function.update_apply,hi]
  rw [he] at h2
  have hlen : ((afterPush dst true d).stacks src).length = (d.stacks src).length := by
    simp [afterPush, hsd]
  rw [hlen] at h2
  have h := Eval.seq h1 h2
  have hcost : 2 + (8 * (d.stacks src).length + 7) =
      8 * (d.stacks src).length + 9 := by
    omega
  rw [hcost] at h
  exact h

theorem appendRecord_exec (src dst : Fin 22) (hsd : src ≠ dst)
    (hs : src ≠ 20) (hd : dst ≠ 20) (d : Data) (htmp : d.stacks 20 = []) :
    Executes (appendRecord src dst) d (afterRecord dst (d.stacks src) d) :=
  ⟨_,appendRecord_eval src dst hsd hs hd d htmp⟩

end SubexponentialSAT.SubexpBlockAssembly

end OAI.Algorithms
