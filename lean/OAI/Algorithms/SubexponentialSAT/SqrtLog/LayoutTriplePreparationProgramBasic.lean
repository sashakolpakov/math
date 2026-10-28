import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramArrays
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScalarEmitter
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixParityProgram

namespace OAI.Algorithms

/-! Fixed port assignments for cache access and triple serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 9 20
abbrev Code := Cmd 9 20

def smallRegisters : Fin 2 → Fin 9 := Fin.castAdd 7
def workRegisters : Fin 8 → Fin 9 := Fin.castAdd 1

theorem smallRegisters_injective : Function.Injective smallRegisters := Fin.castAdd_injective _ _
theorem workRegisters_injective : Function.Injective workRegisters := Fin.castAdd_injective _ _

def readPorts (binomial : Bool) : Fin 11 → Fin 20 :=
  if binomial then ![2,3,9,10,4,11,12,13,14,15,16]
  else ![0,1,8,10,4,11,12,13,14,15,16]

theorem readPorts_injective (b : Bool) : Function.Injective (readPorts b) := by
  cases b <;> decide

def readCached (binomial : Bool) : Code :=
  liftCommand LayoutProgram.readSignedCommand 0 5 smallRegisters (readPorts binomial)

def readResult (d : Data) (p n : List Bool) : Fin 20 → List Bool :=
  Function.update (Function.update d.stacks 11 (p++d.stacks 11)) 12 (n++d.stacks 12)

/-- Source arrays, master index and width are preserved, including every bit
outside the two output stacks. The index scan and all copying are paid. -/
theorem readCached_eval (binomial : Bool) (d : Data)
    (beforeP beforeN : List (List Bool)) (p n restP restN : List Bool)
    (hp : d.stacks (readPorts binomial 0) = beforeP.flatten++(p++restP))
    (hn : d.stacks (readPorts binomial 1) = beforeN.flatten++(n++restN))
    (hip : (d.stacks (readPorts binomial 2)).length = beforeP.length)
    (hin : (d.stacks (readPorts binomial 2)).length = beforeN.length)
    (hwp : ∀ x ∈ beforeP, x.length = (d.stacks 4).length)
    (hwn : ∀ x ∈ beforeN, x.length = (d.stacks 4).length)
    (hlp : p.length = (d.stacks 4).length) (hln : n.length = (d.stacks 4).length)
    (h10 : d.stacks 10 = []) (hs : ∀ j : Fin 20, 13 ≤ j.val → j.val ≤ 16 → d.stacks j = []) :
    ∃ e, Eval (readCached binomial)
      ((d.stacks (readPorts binomial 2)).length * (28*(d.stacks 4).length+34)+
        30*(d.stacks 4).length+43) d e ∧
      e.stacks = readResult d p n ∧ e.regs 8 = d.regs 8 := by
  let a := projectState smallRegisters (readPorts binomial) d
  have hw : a.stacks 4 = d.stacks 4 := by cases binomial <;> rfl
  have h3 : a.stacks 3 = [] := by cases binomial <;> exact h10
  have hwork : ∀ j : Fin 11, 7 ≤ j.val → a.stacks j = [] := by
    intro j hj
    fin_cases j <;> norm_num at hj
    all_goals cases binomial <;> exact hs _ (by decide) (by decide)
  have he := LayoutProgram.readSignedCommand_eval a beforeP beforeN p n restP restN
    (d.stacks 4) (d.stacks (readPorts binomial 2)) hp hn rfl hw hip hin hwp hwn hlp hln h3 hwork
  let e := embedState smallRegisters (readPorts binomial) d
    ⟨readRegs a.regs 0 1 none,LayoutProgram.readSignedStacks p n a.stacks⟩
  refine ⟨e,?_,?_,?_⟩
  · have hh := eval_liftCommand_from_state LayoutProgram.readSignedCommand 0 5
      smallRegisters (readPorts binomial) d smallRegisters_injective (readPorts_injective binomial) he
    simpa [readCached,a,Nat.add_assoc] using hh
  · change Function.extend (readPorts binomial) _ d.stacks = _
    rw [LayoutProgram.readSignedStacks,
      ProgramLinking.extend_update (readPorts_injective binomial),
      ProgramLinking.extend_update (readPorts_injective binomial)]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project smallRegisters (readPorts binomial) d smallRegisters_injective
        (readPorts_injective binomial))
    change Function.extend (readPorts binomial) a.stacks d.stacks = d.stacks at hb
    rw [hb]
    cases binomial <;> rfl
  · apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val = 8 at hv
    have := j.isLt
    omega

def emitPorts (which : Fin 3) : Fin 7 → Fin 20 :=
  if which = 0 then ![11,12,17,13,14,15,16]
  else if which = 1 then ![12,11,17,13,14,15,16]
  else ![5,6,17,13,14,15,16]

theorem emitPorts_injective (which : Fin 3) : Function.Injective (emitPorts which) := by
  fin_cases which <;> decide

def emitCached (which : Fin 3) : Code :=
  liftCommand LayoutScalarEmitter.emitPair 0 2 workRegisters (emitPorts which)

theorem emitCached_eval (which : Fin 3) (d : Data)
    (hs : ∀ j : Fin 20, 13 ≤ j.val → j.val ≤ 16 → d.stacks j = []) :
    ∃ e, Eval (emitCached which)
      (18*((d.stacks (emitPorts which 0)).length+(d.stacks (emitPorts which 1)).length)+39) d e ∧
      e.stacks = Function.update d.stacks 17
        ((LayoutScalarEmitter.record (d.stacks (emitPorts which 0))
          (d.stacks (emitPorts which 1))).reverse++d.stacks 17) ∧
      e.regs 8 = d.regs 8 := by
  let a := projectState workRegisters (emitPorts which) d
  have ha : LayoutScalarEmitter.Ready a := by
    fin_cases which <;>
      exact ⟨hs _ (by decide) (by decide),hs _ (by decide) (by decide),
        hs _ (by decide) (by decide),hs _ (by decide) (by decide)⟩
  obtain ⟨b,hb,hbs⟩ := LayoutScalarEmitter.emitPair_eval a ha
  let e := embedState workRegisters (emitPorts which) d b
  refine ⟨e,?_,?_,?_⟩
  · have hh := eval_liftCommand_from_state LayoutScalarEmitter.emitPair 0 2
      workRegisters (emitPorts which) d workRegisters_injective (emitPorts_injective which) hb
    simpa [emitCached,a,projectState,Nat.add_assoc] using hh
  · change Function.extend (emitPorts which) b.stacks d.stacks = _
    rw [hbs,ProgramLinking.extend_update (emitPorts_injective which)]
    have hf := congrArg StructuredProgram.State.stacks
      (embedState_project workRegisters (emitPorts which) d workRegisters_injective
        (emitPorts_injective which))
    change Function.extend (emitPorts which) a.stacks d.stacks = d.stacks at hf
    rw [hf]
    fin_cases which <;> rfl
  · apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val = 8 at hv
    have := j.isLt
    omega

def signedPair (negative : Bool) (p n : List Bool) : RowSelectionProgram.WordPair :=
  if negative then (n,p) else (p,n)

def emitSigned : Code := .ite 8 (emitCached 1) (emitCached 0)

theorem emitSigned_eval (d : Data)
    (hs : ∀ j : Fin 20, 13 ≤ j.val → j.val ≤ 16 → d.stacks j = []) :
    ∃ e, Eval emitSigned (18*((d.stacks 11).length+(d.stacks 12).length)+40) d e ∧
      e.stacks = Function.update d.stacks 17
        ((LayoutScalarEmitter.record (signedPair (d.regs 8) (d.stacks 11) (d.stacks 12)).1
          (signedPair (d.regs 8) (d.stacks 11) (d.stacks 12)).2).reverse++d.stacks 17) ∧
      e.regs 8 = d.regs 8 := by
  cases hg : d.regs 8
  · obtain ⟨e,he,hst,hr⟩ := emitCached_eval 0 d hs
    refine ⟨e,?_,?_,by simpa [hg] using hr⟩
    · convert (Eval.ite_false (yes := emitCached 1) hg he) using 1 <;>
        simp [emitSigned,emitPorts]
    · simpa [signedPair,hg,emitPorts] using hst
  · obtain ⟨e,he,hst,hr⟩ := emitCached_eval 1 d hs
    refine ⟨e,?_,?_,by simpa [hg] using hr⟩
    · convert (Eval.ite_true (no := emitCached 0) hg he) using 1 <;>
        simp [emitSigned,emitPorts] ; omega
    · simpa [signedPair,hg,emitPorts] using hst

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
