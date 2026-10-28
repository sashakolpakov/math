import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanLoad
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing

namespace OAI.Algorithms

/-! Fixed-port primitives for dynamic Cartesian triple expansion. All loop
bounds and coefficient widths are words on stacks, not generated code. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

abbrev Data := State 2 16

structure Store where
  x : List Bool
  y : List Bool
  table : List Bool
  out : List Bool
  xs : List Bool
  ys : List Bool
  held : List Bool
  degree : List Bool
  kc : List Bool
  ic : List Bool
  jc : List Bool
  width : List Bool

def tapes (s : Store) : Fin 16 → List Bool :=
  ![s.x, s.y, s.table, s.out, s.xs, s.ys, s.held, [], [],
    s.degree, s.kc, s.ic, s.jc, s.width, [], []]

def state (regs : Fin 2 → Bool) (s : Store) : Data := ⟨regs, tapes s⟩

abbrev clear (dst : Fin 16) : Cmd 2 16 := .call (clearProgram dst 0 1)
abbrev copy (src dst : Fin 16) : Cmd 2 16 := .call (copyProgram src dst 15 0 1)
abbrev transfer (src dst : Fin 16) : Cmd 2 16 := .call (transferProgram src dst 0 1)

def afterClear (d : Data) (dst : Fin 16) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks dst d.stacks⟩
def afterCopy (d : Data) (src dst : Fin 16) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks src dst d.stacks⟩
def afterTransfer (d : Data) (src dst : Fin 16) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

theorem clear_eval (d : Data) (dst : Fin 16) :
    Eval (clear dst) (2 * (d.stacks dst).length + 3) d (afterClear d dst) :=
  .call _ (ListRegisterProgram.clear_run dst 0 1 d.regs d.stacks)

theorem copy_eval (d : Data) (src dst : Fin 16)
    (hsd : src ≠ dst) (hs : src ≠ 15) (hd : (15 : Fin 16) ≠ dst)
    (htmp : d.stacks 15 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (afterCopy d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 15 0 1 hsd hs hd
    (by decide) d.regs d.stacks htmp)

theorem transfer_eval (d : Data) (src dst : Fin 16) (hne : src ≠ dst) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (afterTransfer d src dst) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hne (by decide) d.regs d.stacks)

/-- 0 loads the next y, 1 the next table coefficient, 2 the next x. -/
def loadPorts (which : Fin 3) : Fin 5 → Fin 16 :=
  if which = 0 then ![5, 7, 13, 14, 15]
  else if which = 1 then ![2, 8, 13, 14, 15]
  else ![4, 6, 13, 14, 15]

theorem loadPorts_injective (which : Fin 3) : Function.Injective (loadPorts which) := by
  fin_cases which <;> decide

abbrev load (which : Fin 3) : Cmd 2 16 := .call
  (ProgramLinking.liftProgram RingScan.loadWordProgram id (loadPorts which))

def afterLoad (d : Data) (which : Fin 3) (word tail : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks (loadPorts which 0) tail)
      (loadPorts which 1) (word ++ d.stacks (loadPorts which 1))⟩

theorem load_eval (d : Data) (which : Fin 3) (word tail : List Bool)
    (hsrc : d.stacks (loadPorts which 0) = word ++ tail)
    (h14 : d.stacks 14 = []) (h15 : d.stacks 15 = [])
    (hwidth : (d.stacks 13).length = word.length) :
    Eval (load which) (14 * word.length + 12) d (afterLoad d which word tail) := by
  let a := RingScan.loadState d.regs (word ++ tail)
    (d.stacks (loadPorts which 1)) (d.stacks 13) [] []
  let b := RingScan.loadState (readRegs d.regs 0 1 none) tail
    (word ++ d.stacks (loadPorts which 1)) (d.stacks 13) [] []
  have ha : embedState id (loadPorts which) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (loadPorts_injective which)
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      fin_cases i
      · exact hsrc
      · rfl
      · fin_cases which <;> rfl
      · fin_cases which <;> exact h14
      · fin_cases which <;> exact h15
    · intro i hi; rfl
  have hb : embedState id (loadPorts which) d b = afterLoad d which word tail := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (loadPorts_injective which)
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      fin_cases which <;> fin_cases i <;>
        simp [b, RingScan.loadState, RingScan.loadTapes, afterLoad, loadPorts, h14, h15]
    · intro i hi
      have hs : i ≠ loadPorts which 0 := fun h => hi ⟨0, h.symm⟩
      have hd : i ≠ loadPorts which 1 := fun h => hi ⟨1, h.symm⟩
      simp [afterLoad, hs, hd]
  have ht := RingScan.loadWordProgram_trace d.regs word tail
    (d.stacks (loadPorts which 1)) (d.stacks 13) hwidth
  have he := eval_call_lifted RingScan.loadWordProgram id (loadPorts which) d
    Function.injective_id (loadPorts_injective which) (a := a) (b := b) ht
  simpa only [ha, hb, load] using he

abbrev emitTriple : Cmd 2 16 :=
  .seq (copy 6 8) (.seq (transfer 8 3) (.seq (load 0)
    (.seq (transfer 7 3) (.seq (load 1) (transfer 8 3)))))

theorem emitTriple_eval (B : ℕ) (s : Store) (regs : Fin 2 → Bool)
    (y c yt ct : List Bool) (hx : s.held.length = B)
    (hy : y.length = B) (hc : c.length = B) (hw : s.width.length = B) :
    ∃ regs', Eval emitTriple (44 * B + 38)
      (state regs {s with ys := y ++ yt, table := c ++ ct})
      (state regs' {s with ys := yt, table := ct, out := (s.held ++ y ++ c).reverse ++ s.out}) := by
  let d := state regs {s with ys := y ++ yt, table := c ++ ct}
  let a := afterCopy d 6 8
  let b := afterTransfer a 8 3
  let e := afterLoad b 0 y yt
  let f := afterTransfer e 7 3
  let g := afterLoad f 1 c ct
  have h1 := copy_eval d 6 8 (by decide) (by decide) (by decide) (by rfl)
  have h2 := transfer_eval a 8 3 (by decide)
  have h3 := load_eval b 0 y yt (by rfl) (by rfl) (by rfl) (by simpa [b, a, d,
    afterTransfer, afterCopy, transferStacks, copyStacks, state, tapes] using (hw.trans hy.symm))
  have h4 := transfer_eval e 7 3 (by decide)
  have h5 := load_eval f 1 c ct (by rfl) (by rfl) (by rfl) (by simpa [f, e, b, a, d,
    afterTransfer, afterLoad, afterCopy, transferStacks, copyStacks, loadPorts, state, tapes]
    using (hw.trans hc.symm))
  have h6 := transfer_eval g 8 3 (by decide)
  have heq : afterTransfer g 8 3 =
      state (afterTransfer g 8 3).regs {s with ys := yt, table := ct, out := (s.held ++ y ++ c).reverse ++ s.out} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [g, f, e, b, a, d, afterTransfer, afterLoad, afterCopy,
        transferStacks, copyStacks, loadPorts, state, tapes, List.reverse_append, List.append_assoc]
  refine ⟨(afterTransfer g 8 3).regs, ?_⟩
  rw [← heq]
  convert h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))) using 1
  simp [g, f, e, b, a, d, afterTransfer, afterLoad, afterCopy,
    transferStacks, copyStacks, loadPorts, state, tapes, hx, hy, hc]
  omega

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
