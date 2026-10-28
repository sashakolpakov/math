import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramFrames

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly.RegisterFrame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- A property of the actual executions, independent of the data invariant. -/
def Preserves (c : Code) (i : Fin 40) : Prop :=
  ∀ {n : ℕ} {a b : Data}, Eval c n a b → b.regs i=a.regs i

theorem seq {c d : Code} {i : Fin 40} (hc : Preserves c i) (hd : Preserves d i) :
    Preserves (.seq c d) i := by
  intro n a b h
  cases h with
  | seq h1 h2 => exact (hd h2).trans (hc h1)

theorem loop {c : Code} (test i : Fin 40) (hc : Preserves c i) :
    Preserves (.while test c) i := by
  intro n a b h
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    cases h with
    | while_false => rfl
    | @while_true _ _ k m a z b _ h1 h2 =>
      exact (ih m (by omega) (a:=z) (b:=b) h2).trans (hc h1)

theorem trace {l : ℕ} (p : Program 40 768 l) (i : Fin 40)
    (hp : ∀ q c, (execInstr (p.code q) c).regs i=c.regs i)
    {n : ℕ} {a b : Cfg 40 768 l} (h : Trace p n a b) : b.regs i=a.regs i := by
  induction h with
  | refl => rfl
  | @cons k a z b hs ht ih =>
    cases hpc : a.pc with
    | none => simp [step,hpc] at hs
    | some q =>
      have hz : execInstr (p.code q) a=z := by simpa [step,hpc] using hs
      exact ih.trans (hz ▸ hp q a)

theorem call {l : ℕ} (p : Program 40 768 l) (i : Fin 40)
    (hp : ∀ q c, (execInstr (p.code q) c).regs i=c.regs i) :
    Preserves (.call p) i := by
  intro n a b h
  cases h with
  | call _ ht => exact trace p i hp ht

theorem lifted {r s l : ℕ} (p : Program r s l) (reg : Fin r → Fin 40)
    (stk : Fin s → Fin 768) (i : Fin 40) (hi : ∀ j, i ≠ reg j) :
    Preserves (.call (ProgramLinking.liftProgram p reg stk)) i := by
  apply call
  intro q c
  change (execInstr (ProgramLinking.relocateInstr reg stk id none (p.code q)) c).regs i=c.regs i
  cases p.code q <;> simp [ProgramLinking.relocateInstr,execInstr,readRegs,hi]

theorem peek (src : Fin 768) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (MomentsAssembly.peek src) i := by
  have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  have h15 : i ≠ 15 := by
    intro h
    subst i
    change 16 ≤ 15 at hi
    omega
  intro n a b h
  cases h with
  | base hb =>
    cases hb with
    | atom => simp [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr,readRegs,h0,h15]

theorem clear (src : Fin 768) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (MomentsAssembly.clear src) i := by
  have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
  apply call
  intro q c
  fin_cases q <;> simp [execInstr,readRegs,h0,h1]

theorem transfer (src dst : Fin 768) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (MomentsAssembly.transfer src dst) i := by
  have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
  apply call
  intro q c
  fin_cases q <;> simp [execInstr,readRegs,h0,h1]

theorem copy (src dst : Fin 768) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (MomentsAssembly.copy src dst) i := by
  have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
  apply call
  intro q c
  fin_cases q <;> simp [execInstr,readRegs,h0,h1]

theorem reader (src dst : Fin 768) (hs : src ≠ dst) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (MomentsAssembly.readFrame src dst hs) i := by
  apply lifted
  intro j
  fin_cases j <;> simp [RecordPrograms.registerMap,framePorts] <;>
    intro h <;> subst i <;> norm_num at hi

theorem takeFrame (src dst : Fin 768) (hs : src ≠ 164) (i : Fin 40) (hi : 16 ≤ i.val) :
    Preserves (MomentsAssembly.takeFrame src dst hs) i :=
  seq (reader src 164 hs i hi) (transfer 164 dst i hi)

end SubexponentialSAT.SqrtLog.MomentsAssembly.RegisterFrame

end OAI.Algorithms
