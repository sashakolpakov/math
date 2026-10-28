import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import Mathlib.Tactic.FinCases

/-! Fixed finite control for the pruned pair DFS. Four protected stacks hold
remaining depth, remaining strict budget, and the two current masks. The masks
also encode the DFS phases `00`, `10`, `11`; no completed-pair list is retained.
The callback receives the masks in reverse coordinate order. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram

open OAI.Algorithms.SubexponentialSAT.StructuredProgram (Atom)
open OAI.Algorithms.SubexponentialSAT.StructuredCalls

structure Ports (r s : ℕ) where
  register : Fin 5 ↪ Fin r
  stack : Fin 4 ↪ Fin s

variable {r s : ℕ}

def atoms (code : List (Atom r s)) : Cmd r s :=
  .base (code.foldr (fun a rest => .seq (.atom a) rest) .skip)

theorem atoms_eval (code : List (Atom r s)) (a : State r s) :
    Eval (atoms code) code.length a (code.foldl (fun d op => op.eval d) a) := by
  apply Eval.base
  induction code generalizing a with
  | nil => exact StructuredProgram.Eval.skip a
  | cons op code ih =>
      simpa only [List.foldr_cons, List.foldl_cons, List.length_cons, Nat.add_comm]
        using (StructuredProgram.Eval.atom op a).seq (ih (op.eval a))

def pushBit (p : Ports r s) (i : Fin 4) (b : Bool) : Cmd r s :=
  atoms [.set (p.register 2) b, .push (p.stack i) (p.register 2)]

def pushed (p : Ports r s) (i : Fin 4) (b : Bool) (d : State r s) : State r s :=
  ⟨Function.update d.regs (p.register 2) b,
    Function.update d.stacks (p.stack i) (b :: d.stacks (p.stack i))⟩

theorem pushBit_eval (p : Ports r s) (i : Fin 4) (b : Bool) (d : State r s) :
    Eval (pushBit p i b) 2 d (pushed p i b d) := by
  simpa [pushBit, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, BitProgram.execInstr] using
    atoms_eval [.set (p.register 2) b, .push (p.stack i) (p.register 2)] d

def enter (p : Ports r s) (e u : Bool) : Cmd r s :=
  .seq (pushBit p 2 e) (.seq (pushBit p 3 u) (atoms [.set (p.register 0) true]))

def entered (p : Ports r s) (e u : Bool) (d : State r s) : State r s :=
  (Atom.set (p.register 0) true).eval (pushed p 3 u (pushed p 2 e d))

theorem enter_eval (p : Ports r s) (e u : Bool) (d : State r s) :
    Eval (enter p e u) 5 d (entered p e u d) :=
  (pushBit_eval p 2 e d).seq
    ((pushBit_eval p 3 u _).seq (atoms_eval [.set (p.register 0) true] _))

@[simp] theorem entered_depth (p : Ports r s) (e u : Bool) (d : State r s) :
    (entered p e u d).stacks (p.stack 0) = d.stacks (p.stack 0) := by
  simp [entered, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

@[simp] theorem entered_budget (p : Ports r s) (e u : Bool) (d : State r s) :
    (entered p e u d).stacks (p.stack 1) = d.stacks (p.stack 1) := by
  simp [entered, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

@[simp] theorem entered_outer (p : Ports r s) (e u : Bool) (d : State r s) :
    (entered p e u d).stacks (p.stack 2) = e :: d.stacks (p.stack 2) := by
  simp [entered, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

@[simp] theorem entered_inner (p : Ports r s) (e u : Bool) (d : State r s) :
    (entered p e u d).stacks (p.stack 3) = u :: d.stacks (p.stack 3) := by
  simp [entered, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

@[simp] theorem entered_descending (p : Ports r s) (e u : Bool) (d : State r s) :
    (entered p e u d).regs (p.register 0) = true := by
  simp [entered, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

@[simp] theorem entered_active (p : Ports r s) (e u : Bool) (d : State r s) :
    (entered p e u d).regs (p.register 1) = d.regs (p.register 1) := by
  simp [entered, pushed, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

def finishLevel (p : Ports r s) : Cmd r s := pushBit p 0 true

def nextOutside (p : Ports r s) : Cmd r s :=
  .seq
    (atoms [.pop (p.stack 1) (p.register 2) (p.register 3),
      .peek (p.stack 1) (p.register 2) (p.register 3)])
    (.ite (p.register 3) (enter p true false)
      (.seq (pushBit p 1 true) (finishLevel p)))

def backtrack (p : Ports r s) : Cmd r s :=
  .seq (atoms [.pop (p.stack 2) (p.register 4) (p.register 3)])
    (.ite (p.register 3)
      (.seq (atoms [.pop (p.stack 3) (p.register 2) (p.register 3)])
        (.ite (p.register 4)
          (.ite (p.register 2)
            (.seq (pushBit p 1 true) (finishLevel p)) (enter p true true))
          (nextOutside p)))
      (atoms [.set (p.register 1) false]))

def descend (p : Ports r s) (callback : Cmd r s) : Cmd r s :=
  .seq (atoms [.pop (p.stack 0) (p.register 2) (p.register 3)])
    (.ite (p.register 3) (enter p false false)
      (.seq callback (atoms [.set (p.register 0) false, .set (p.register 1) true])))

def body (p : Ports r s) (callback : Cmd r s) : Cmd r s :=
  .ite (p.register 0) (descend p callback) (backtrack p)

def command (p : Ports r s) (callback : Cmd r s) : Cmd r s :=
  .seq (atoms [.peek (p.stack 1) (p.register 2) (p.register 3),
    .copy (p.register 1) (p.register 3), .set (p.register 0) true])
    (.while (p.register 1) (body p callback))

def program (p : Ports r s) (callback : Cmd r s) :=
  compiled (command p callback) (p.stack 0) (p.stack 2)

def popped (p : Ports r s) (i : Fin 4) (v : Fin 5) (d : State r s) : State r s :=
  (Atom.pop (p.stack i) (p.register v) (p.register 3)).eval d

def descended (p : Ports r s) (d : State r s) : State r s :=
  entered p false false (popped p 0 2 d)

theorem body_descend (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = true) (b : Bool) (rest : List Bool)
    (hn : d.stacks (p.stack 0) = b :: rest) :
    Eval (body p callback) 8 d (descended p d) := by
  have hp : (popped p 0 2 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hn]
  exact .ite_true hd ((atoms_eval [.pop (p.stack 0) (p.register 2) (p.register 3)] d).seq
    (.ite_true hp (enter_eval p false false (popped p 0 2 d))))

def returned (p : Ports r s) (d : State r s) : State r s :=
  (Atom.set (p.register 1) true).eval ((Atom.set (p.register 0) false).eval d)

theorem body_callback (p : Ports r s) (callback : Cmd r s) (d e : State r s)
    (hd : d.regs (p.register 0) = true) (hn : d.stacks (p.stack 0) = [])
    (t : ℕ) (hc : Eval callback t (popped p 0 2 d) e) :
    Eval (body p callback) (t + 5) d (returned p e) := by
  have h := Eval.ite_true (yes := descend p callback) (no := backtrack p) hd
    (Eval.seq (atoms_eval [.pop (p.stack 0) (p.register 2) (p.register 3)] d)
      (Eval.ite_false (yes := enter p false false) (test := p.register 3)
        (by simp [Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
          BitProgram.execInstr, BitProgram.readRegs, hn])
        (hc.seq (atoms_eval [.set (p.register 0) false, .set (p.register 1) true] e))))
  convert h using 1
  · rfl
  · simp only [List.length_cons, List.length_nil]
    omega
  · rfl

@[simp] theorem returned_stacks (p : Ports r s) (d : State r s) :
    (returned p d).stacks = d.stacks := rfl

@[simp] theorem returned_descending (p : Ports r s) (d : State r s) :
    (returned p d).regs (p.register 0) = false := by
  simp [returned, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

@[simp] theorem returned_active (p : Ports r s) (d : State r s) :
    (returned p d).regs (p.register 1) = true := by
  simp [returned, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr]

def backed (p : Ports r s) (d : State r s) : State r s :=
  popped p 3 2 (popped p 2 4 d)

def finished (p : Ports r s) (d : State r s) : State r s :=
  pushed p 0 true (pushed p 1 true (backed p d))

theorem body_finish (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (es us : List Bool)
    (he : d.stacks (p.stack 2) = true :: es)
    (hu : d.stacks (p.stack 3) = true :: us) :
    Eval (body p callback) 10 d (finished p d) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have he' : (backed p d).regs (p.register 4) = true := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have hu' : (backed p d).regs (p.register 2) = true := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hu]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_true hp
        ((atoms_eval [.pop (p.stack 3) (p.register 2) (p.register 3)] _).seq
          (.ite_true he' (.ite_true hu'
            ((pushBit_eval p 1 true _).seq (pushBit_eval p 0 true _)))))))

theorem body_next_inner (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (es us : List Bool)
    (he : d.stacks (p.stack 2) = true :: es)
    (hu : d.stacks (p.stack 3) = false :: us) :
    Eval (body p callback) 11 d (entered p true true (backed p d)) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have he' : (backed p d).regs (p.register 4) = true := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have hu' : (backed p d).regs (p.register 2) = false := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hu]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_true hp
        ((atoms_eval [.pop (p.stack 3) (p.register 2) (p.register 3)] _).seq
          (.ite_true he' (.ite_false hu' (enter_eval p true true _))))))

def testedOutside (p : Ports r s) (d : State r s) : State r s :=
  (Atom.peek (p.stack 1) (p.register 2) (p.register 3)).eval
    (popped p 1 2 (backed p d))

theorem body_next_outer (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (es bs : List Bool) (b c : Bool)
    (he : d.stacks (p.stack 2) = false :: es)
    (hb : d.stacks (p.stack 1) = b :: c :: bs) :
    Eval (body p callback) 13 d (entered p true false (testedOutside p d)) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have he' : (backed p d).regs (p.register 4) = false := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have hb' : (testedOutside p d).regs (p.register 3) = true := by
    simp [testedOutside, backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hb]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_true hp
        ((atoms_eval [.pop (p.stack 3) (p.register 2) (p.register 3)] _).seq
          (.ite_false he'
            ((atoms_eval [.pop (p.stack 1) (p.register 2) (p.register 3),
              .peek (p.stack 1) (p.register 2) (p.register 3)] _).seq
              (.ite_true hb' (enter_eval p true false _)))))))

def pruned (p : Ports r s) (d : State r s) : State r s :=
  pushed p 0 true (pushed p 1 true (testedOutside p d))

theorem body_prune (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (es : List Bool) (b : Bool)
    (he : d.stacks (p.stack 2) = false :: es) (hb : d.stacks (p.stack 1) = [b]) :
    Eval (body p callback) 12 d (pruned p d) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = true := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have he' : (backed p d).regs (p.register 4) = false := by
    simp [backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  have hb' : (testedOutside p d).regs (p.register 3) = false := by
    simp [testedOutside, backed, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hb]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_true hp
        ((atoms_eval [.pop (p.stack 3) (p.register 2) (p.register 3)] _).seq
          (.ite_false he'
            ((atoms_eval [.pop (p.stack 1) (p.register 2) (p.register 3),
              .peek (p.stack 1) (p.register 2) (p.register 3)] _).seq
              (.ite_false hb' ((pushBit_eval p 1 true _).seq (pushBit_eval p 0 true _))))))))

def stopped (p : Ports r s) (d : State r s) : State r s :=
  (Atom.set (p.register 1) false).eval (popped p 2 4 d)

theorem body_stop (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hd : d.regs (p.register 0) = false) (he : d.stacks (p.stack 2) = []) :
    Eval (body p callback) 4 d (stopped p d) := by
  have hp : (popped p 2 4 d).regs (p.register 3) = false := by
    simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, he]
  exact .ite_false hd
    ((atoms_eval [.pop (p.stack 2) (p.register 4) (p.register 3)] d).seq
      (.ite_false hp (atoms_eval [.set (p.register 1) false] _)))

structure Cursor (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (down : Bool) (d : State r s) : Prop where
  depth : d.stacks (p.stack 0) = List.replicate n true
  budget : d.stacks (p.stack 1) = List.replicate J true
  outer : d.stacks (p.stack 2) = (pre.map Option.isSome).reverse
  inner : d.stacks (p.stack 3) = (pre.map (fun a => a.getD false)).reverse
  descending : d.regs (p.register 0) = down
  active : d.regs (p.register 1) = true

theorem cursor_descend (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p (n + 1) J pre true d) :
    Cursor p n J (pre ++ [none]) true (descended p d) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [descended, entered, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, ha, List.replicate_succ]

theorem cursor_next_inner (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p n J (pre ++ [some false]) false d) :
    Cursor p n J (pre ++ [some true]) true (entered p true true (backed p d)) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [entered, backed, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, ha]

theorem cursor_next_outer (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p n (J + 2) (pre ++ [none]) false d) :
    Cursor p n (J + 1) (pre ++ [some false]) true
      (entered p true false (testedOutside p d)) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [entered, testedOutside, backed, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, ha, List.replicate_succ]

theorem cursor_finished (p : Ports r s) (n J : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p n J (pre ++ [some true]) false d) :
    Cursor p (n + 1) (J + 1) pre false (finished p d) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [finished, backed, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, hm, ha, List.replicate_succ]

theorem cursor_pruned (p : Ports r s) (n : ℕ) (pre : List (Option Bool))
    (d : State r s) (h : Cursor p n 1 (pre ++ [none]) false d) :
    Cursor p (n + 1) 1 pre false (pruned p d) := by
  rcases h with ⟨h0, h1, h2, h3, hm, ha⟩
  constructor <;>
    simp [pruned, testedOutside, backed, popped, pushed, Atom.eval, Atom.instr,
      StructuredProgram.State.ofCfg, BitProgram.execInstr,
      BitProgram.readRegs, h0, h1, h2, h3, hm, ha, List.replicate_succ]

inductive BodyTrace (p : Ports r s) (callback : Cmd r s) : ℕ → State r s → State r s → Prop
  | refl (a) : BodyTrace p callback 0 a a
  | cons {n m a b c} : a.regs (p.register 1) = true → Eval (body p callback) n a b →
      BodyTrace p callback m b c → BodyTrace p callback (n + m + 1) a c

theorem BodyTrace.trans {p : Ports r s} {callback : Cmd r s}
    {n m : ℕ} {a b c : State r s}
    (h : BodyTrace p callback n a b) (g : BodyTrace p callback m b c) :
    BodyTrace p callback (n + m) a c := by
  induction h with
  | refl => simpa using g
  | cons ha hab _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        BodyTrace.cons ha hab (ih g)

theorem BodyTrace.while_eval {p : Ports r s} {callback : Cmd r s}
    {n : ℕ} {a b : State r s} (h : BodyTrace p callback n a b)
    (hb : b.regs (p.register 1) = false) :
    Eval (.while (p.register 1) (body p callback)) (n + 1) a b := by
  induction h with
  | refl => exact Eval.while_false hb
  | cons ha hab _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Eval.while_true ha hab (ih hb)

theorem BodyTrace.single {p : Ports r s} {callback : Cmd r s}
    {n : ℕ} {a b : State r s} (ha : a.regs (p.register 1) = true)
    (he : Eval (body p callback) n a b) : BodyTrace p callback (n + 1) a b := by
  simpa using BodyTrace.cons ha he (BodyTrace.refl b)

@[simp] theorem pushed_frame (p : Ports r s) (i : Fin 4) (b : Bool) (d : State r s)
    (o : Fin s) (ho : o ≠ p.stack i) : (pushed p i b d).stacks o = d.stacks o := by
  simp [pushed, ho]

@[simp] theorem popped_frame (p : Ports r s) (i : Fin 4) (v : Fin 5) (d : State r s)
    (o : Fin s) (ho : o ≠ p.stack i) : (popped p i v d).stacks o = d.stacks o := by
  simp [popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr, ho]

@[simp] theorem entered_frame (p : Ports r s) (e u : Bool) (d : State r s)
    (o : Fin s) (h2 : o ≠ p.stack 2) (h3 : o ≠ p.stack 3) :
    (entered p e u d).stacks o = d.stacks o := by
  simp [entered, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr, h2, h3]

@[simp] theorem testedOutside_stacks (p : Ports r s) (d : State r s) :
    (testedOutside p d).stacks = (popped p 1 2 (backed p d)).stacks := rfl

structure CallbackSpec (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (visit : List (Option Bool) → List Bool → List Bool) (C N : ℕ)
    (I : State r s → Prop) : Prop where
  stable : ∀ d e, (∀ o, (∀ i, o ≠ p.stack i) → e.stacks o = d.stacks o) → I d → I e
  run : ∀ J pre d, pre.length = N → Cursor p 0 (J + 1) pre true d → I d →
    ∃ t e, t ≤ C ∧ Eval callback t (popped p 0 2 d) e ∧
      (∀ i, e.stacks (p.stack i) = d.stacks (p.stack i)) ∧
      e.stacks output = visit pre (d.stacks output) ∧ I e

theorem subtree (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (houtput : ∀ i, output ≠ p.stack i)
    (visit : List (Option Bool) → List Bool → List Bool) (C N : ℕ)
    (I : State r s → Prop) (spec : CallbackSpec p callback output visit C N I) (n J : ℕ)
    (pre : List (Option Bool)) (d : State r s) (hsize : n + pre.length = N)
    (h : Cursor p n (J + 1) pre true d) (hi : I d) :
    ∃ t e, BodyTrace p callback t d e ∧ Cursor p n (J + 1) pre false e ∧
      e.stacks output = DifferencePairs.fold visit n (J + 1) pre (d.stacks output) ∧
      t ≤ (C + 46) * DifferencePairs.calls n (J + 1) ∧ I e := by
  induction n generalizing J pre d with
  | zero =>
      obtain ⟨t, e, ht, he, hf, ho, hie⟩ := spec.run J pre d (by simpa using hsize) h hi
      have hr : Cursor p 0 (J + 1) pre false (returned p e) := by
        exact ⟨(hf 0).trans h.depth, (hf 1).trans h.budget, (hf 2).trans h.outer,
          (hf 3).trans h.inner, returned_descending p e, returned_active p e⟩
      refine ⟨t + 6, returned p e, ?_, hr, ?_, ?_,
        spec.stable e (returned p e) (fun _ _ => rfl) hie⟩
      · simpa [Nat.add_assoc] using BodyTrace.single h.active
          (body_callback p callback d e h.descending (by simpa using h.depth) t he)
      · simpa [DifferencePairs.fold] using ho
      · simp only [DifferencePairs.calls]; omega
  | succ n ih =>
      have hs : n + (pre ++ [none]).length = N := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsize
      have hd := cursor_descend p n (J + 1) pre d h
      have hid : I (descended p d) := spec.stable d _ (by
        intro o ho; simp [descended, ho]) hi
      obtain ⟨t₀, e₀, he₀, hc₀, ho₀, ht₀, hi₀⟩ :=
        ih J (pre ++ [none]) (descended p d) hs hd hid
      have hdtrace := BodyTrace.single h.active (body_descend p callback d h.descending true
        (List.replicate n true) (by simpa [List.replicate_succ] using h.depth))
      have hout : (descended p d).stacks output = d.stacks output := by
        simp [descended, houtput]
      cases J with
      | zero =>
          have hb := body_prune p callback e₀ hc₀.descending
            (pre.map Option.isSome).reverse true
            (by simpa using hc₀.outer) (by simpa using hc₀.budget)
          have hr := cursor_pruned p n pre e₀ hc₀
          refine ⟨9 + t₀ + 13, pruned p e₀,
            (hdtrace.trans he₀).trans (BodyTrace.single hc₀.active hb), hr, ?_, ?_, ?_⟩
          · simpa [DifferencePairs.fold, pruned, backed, houtput, hout] using ho₀
          · simp only [DifferencePairs.calls, DifferencePairs.calls_zero]
            nlinarith
          · exact spec.stable e₀ _ (by intro o ho; simp [pruned, backed, ho]) hi₀
      | succ J =>
          have hb₁ := body_next_outer p callback e₀ hc₀.descending
            (pre.map Option.isSome).reverse (List.replicate J true) true true
            (by simpa using hc₀.outer) (by simpa [List.replicate_succ] using hc₀.budget)
          have hc₁ := cursor_next_outer p n J pre e₀ hc₀
          have hi₁ : I (entered p true false (testedOutside p e₀)) :=
            spec.stable e₀ _ (by intro o ho; simp [testedOutside_stacks, backed, ho]) hi₀
          obtain ⟨t₁, e₁, he₁, hc₁', ho₁, ht₁, hi₁'⟩ := ih J (pre ++ [some false])
            (entered p true false (testedOutside p e₀))
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsize) hc₁ hi₁
          have hb₂ := body_next_inner p callback e₁ hc₁'.descending
            (pre.map Option.isSome).reverse (pre.map (fun a => a.getD false)).reverse
            (by simpa using hc₁'.outer) (by simpa using hc₁'.inner)
          have hc₂ := cursor_next_inner p n (J + 1) pre e₁ hc₁'
          have hi₂ : I (entered p true true (backed p e₁)) :=
            spec.stable e₁ _ (by intro o ho; simp [backed, ho]) hi₁'
          obtain ⟨t₂, e₂, he₂, hc₂', ho₂, ht₂, hi₂'⟩ := ih J (pre ++ [some true])
            (entered p true true (backed p e₁))
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsize) hc₂ hi₂
          have hb₃ := body_finish p callback e₂ hc₂'.descending
            (pre.map Option.isSome).reverse (pre.map (fun a => a.getD false)).reverse
            (by simpa using hc₂'.outer) (by simpa using hc₂'.inner)
          have hr := cursor_finished p n (J + 1) pre e₂ hc₂'
          refine ⟨9 + t₀ + 14 + t₁ + 12 + t₂ + 11, finished p e₂,
            (((((hdtrace.trans he₀).trans (BodyTrace.single hc₀.active hb₁)).trans he₁).trans
              (BodyTrace.single hc₁'.active hb₂)).trans he₂).trans
              (BodyTrace.single hc₂'.active hb₃), hr, ?_, ?_, ?_⟩
          · simp only [finished, pushed_frame _ _ _ _ _ (houtput _)]
            simp only [backed, popped_frame _ _ _ _ _ (houtput _)]
            rw [ho₂]
            simp only [entered_frame _ _ _ _ _ (houtput 2) (houtput 3),
              backed, popped_frame _ _ _ _ _ (houtput _)]
            rw [ho₁]
            simp only [entered_frame _ _ _ _ _ (houtput 2) (houtput 3),
              testedOutside_stacks, backed, popped_frame _ _ _ _ _ (houtput _)]
            rw [ho₀, hout]
            rfl
          · simp only [DifferencePairs.calls]
            nlinarith
          · exact spec.stable e₂ _ (by intro o ho; simp [finished, backed, ho]) hi₂'

def initialized (p : Ports r s) (d : State r s) : State r s :=
  (Atom.set (p.register 0) true).eval
    ((Atom.copy (p.register 1) (p.register 3)).eval
      ((Atom.peek (p.stack 1) (p.register 2) (p.register 3)).eval d))

@[simp] theorem initialized_stacks (p : Ports r s) (d : State r s) :
    (initialized p d).stacks = d.stacks := rfl

theorem command_eval (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (houtput : ∀ i, output ≠ p.stack i)
    (visit : List (Option Bool) → List Bool → List Bool) (C n J : ℕ)
    (I : State r s → Prop) (spec : CallbackSpec p callback output visit C n I) (d : State r s)
    (hdepth : d.stacks (p.stack 0) = List.replicate n true)
    (hbudget : d.stacks (p.stack 1) = List.replicate (J + 1) true)
    (he : d.stacks (p.stack 2) = []) (hu : d.stacks (p.stack 3) = []) (hi : I d) :
    ∃ (t : ℕ) (e : State r s), t ≤ (C + 46) * DifferencePairs.calls n (J + 1) + 9 ∧
      Eval (command p callback) t d e ∧
      e.stacks output = DifferencePairs.fold visit n (J + 1) [] (d.stacks output) ∧
      (∀ i, e.stacks (p.stack i) = d.stacks (p.stack i)) ∧ I e := by
  have hcursor : Cursor p n (J + 1) [] true (initialized p d) := by
    constructor
    · exact hdepth
    · exact hbudget
    · exact he
    · exact hu
    · simp [initialized, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
        BitProgram.execInstr]
    · simp [initialized, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
        BitProgram.execInstr, BitProgram.readRegs,
        hbudget, List.replicate_succ]
  have hii : I (initialized p d) := spec.stable d _ (fun _ _ => rfl) hi
  obtain ⟨t, e, ht, hc, ho, hb, hie⟩ := subtree p callback output houtput visit C n I spec
    n J [] (initialized p d) (by simp) hcursor hii
  have hend := body_stop p callback e hc.descending (by simpa using hc.outer)
  have hstop : (stopped p e).regs (p.register 1) = false := by
    simp [stopped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr]
  have hw := (ht.trans (BodyTrace.single hc.active hend)).while_eval hstop
  have hinit := atoms_eval [.peek (p.stack 1) (p.register 2) (p.register 3),
    .copy (p.register 1) (p.register 3), .set (p.register 0) true] d
  have hall : Eval (command p callback) (t + 9) d (stopped p e) := by
    simpa [command, initialized, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hinit.seq hw
  refine ⟨t + 9, stopped p e, by omega, hall, ?_, ?_, ?_⟩
  · simpa [stopped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, popped, houtput] using ho
  · intro i
    fin_cases i <;>
      simp [stopped, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
        BitProgram.execInstr, hc.depth, hc.budget,
        hc.outer, hc.inner, hdepth, hbudget, he, hu]
  · exact spec.stable e _ (by
      intro o ho
      simp [stopped, popped, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
        BitProgram.execInstr, ho]) hie

theorem program_trace (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (houtput : ∀ i, output ≠ p.stack i)
    (visit : List (Option Bool) → List Bool → List Bool) (C n J : ℕ)
    (I : State r s → Prop) (spec : CallbackSpec p callback output visit C n I) (d : State r s)
    (hdepth : d.stacks (p.stack 0) = List.replicate n true)
    (hbudget : d.stacks (p.stack 1) = List.replicate (J + 1) true)
    (he : d.stacks (p.stack 2) = []) (hu : d.stacks (p.stack 3) = []) (hi : I d) :
    ∃ (t : ℕ) (e : State r s), t ≤ (C + 46) * DifferencePairs.calls n (J + 1) + 10 ∧
      BitProgram.Trace (program p callback) t
        (d.withPC (some (program p callback).entry)) (e.withPC none) ∧
      e.stacks output = DifferencePairs.fold visit n (J + 1) [] (d.stacks output) ∧
      (∀ i, e.stacks (p.stack i) = d.stacks (p.stack i)) ∧ I e := by
  obtain ⟨t, e, ht, heval, ho, hf, hie⟩ := command_eval p callback output houtput visit C n J
    I spec d hdepth hbudget he hu hi
  exact ⟨t + 1, e, by omega, compiled_halt_trace heval (p.stack 0) (p.stack 2), ho, hf, hie⟩

theorem command_eval_zero (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hbudget : d.stacks (p.stack 1) = []) :
    Eval (command p callback) 4 d (initialized p d) := by
  have hfalse : (initialized p d).regs (p.register 1) = false := by
    simp [initialized, Atom.eval, Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, hbudget]
  exact (atoms_eval [.peek (p.stack 1) (p.register 2) (p.register 3),
    .copy (p.register 1) (p.register 3), .set (p.register 0) true] d).seq
      (Eval.while_false hfalse)

theorem program_trace_zero (p : Ports r s) (callback : Cmd r s) (d : State r s)
    (hbudget : d.stacks (p.stack 1) = []) :
    BitProgram.Trace (program p callback) 5
      (d.withPC (some (program p callback).entry)) ((initialized p d).withPC none) := by
  exact compiled_halt_trace (command_eval_zero p callback d hbudget) (p.stack 0) (p.stack 2)

def cost (C n J : ℕ) : ℕ := (C + 46) * (3 * n + 1) * DifferencePairs.pairCount n J + 10

theorem program_runsIn (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (houtput : ∀ i, output ≠ p.stack i)
    (visit : List (Option Bool) → List Bool → List Bool) (C n J : ℕ)
    (I : State r s → Prop) (spec : CallbackSpec p callback output visit C n I) (d : State r s)
    (hdepth : d.stacks (p.stack 0) = List.replicate n true)
    (hbudget : d.stacks (p.stack 1) = List.replicate J true)
    (he : d.stacks (p.stack 2) = []) (hu : d.stacks (p.stack 3) = []) (hi : I d) :
    ∃ e : State r s, BitProgram.RunsIn (program p callback) (cost C n J)
        (d.withPC (some (program p callback).entry)) (e.withPC none) ∧
      e.stacks output = DifferencePairs.fold visit n J [] (d.stacks output) ∧
      (∀ i, e.stacks (p.stack i) = d.stacks (p.stack i)) ∧ I e := by
  cases J with
  | zero =>
      exact ⟨initialized p d, ⟨5, by simp [cost],
        program_trace_zero p callback d (by simpa using hbudget)⟩,
        by simp [DifferencePairs.fold], (fun _ => rfl),
        spec.stable d _ (fun _ _ => rfl) hi⟩
  | succ J =>
      obtain ⟨t, e, ht, htrace, ho, hf, hie⟩ := program_trace p callback output houtput visit C n J
        I spec d hdepth hbudget he hu hi
      refine ⟨e, ⟨t, ht.trans ?_, htrace⟩, ho, hf, hie⟩
      have hc := DifferencePairs.calls_le n (J + 1) (Nat.succ_pos J)
      unfold cost
      nlinarith

theorem cost_le_support_square (C n J : ℕ) :
    cost C n J ≤ (C + 46) * (3 * n + 1) *
      (BooleanDifferences.supportFamily n J).card ^ 2 + 10 := by
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (DifferencePairs.pairCount_le_square n J)) 10

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram
