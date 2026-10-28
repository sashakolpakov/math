import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BitProgram

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

abbrev Stacks (S : Type u) := S → List Bool

/-- Specification of emptying one stack. -/
abbrev clearStacks {S : Type u} [DecidableEq S] (src : S) (stk : Stacks S) : Stacks S :=
  Function.update stk src []

/-- Specification of popping a source onto a destination. -/
abbrev transferStacks {S : Type u} [DecidableEq S] (src dst : S)
    (stk : Stacks S) : Stacks S :=
  Function.update (Function.update stk src []) dst
    ((stk src).reverse ++ stk dst)

/-- Specification of popping a source onto each of two destinations. -/
def fanoutStacks {S : Type u} [DecidableEq S] (src dst₁ dst₂ : S)
    (stk : Stacks S) : Stacks S :=
  Function.update
    (Function.update (Function.update stk src []) dst₁
      ((stk src).reverse ++ stk dst₁))
    dst₂ ((stk src).reverse ++ stk dst₂)

/-- Specification of a preserving copy, with the copied word prefixed to `dst`. -/
abbrev copyStacks {S : Type u} [DecidableEq S] (src dst : S)
    (stk : Stacks S) : Stacks S :=
  Function.update stk dst (stk src ++ stk dst)

@[simp] theorem clearStacks_src {S : Type u} [DecidableEq S] (src : S) (stk : Stacks S) :
    clearStacks src stk src = [] := by simp [clearStacks]

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

@[simp] theorem transferStacks_src {S : Type u} [DecidableEq S] (src dst : S)
    (stk : Stacks S) (h : src ≠ dst) : transferStacks src dst stk src = [] := by
  simp [transferStacks, h]

@[simp] theorem transferStacks_dst {S : Type u} [DecidableEq S] (src dst : S)
    (stk : Stacks S) :
    transferStacks src dst stk dst = (stk src).reverse ++ stk dst := by
  simp [transferStacks]

theorem transferStacks_frame {S : Type u} [DecidableEq S] (src dst j : S)
    (stk : Stacks S) (hsrc : j ≠ src) (hdst : j ≠ dst) :
    transferStacks src dst stk j = stk j := by
  simp [transferStacks, hsrc, hdst]

theorem copyStacks_frame {S : Type u} [DecidableEq S] (src dst j : S)
    (stk : Stacks S) (hj : j ≠ dst) : copyStacks src dst stk j = stk j := by
  simp [copyStacks, hj]

@[simp] theorem copyStacks_dst {S : Type u} [DecidableEq S] (src dst : S)
    (stk : Stacks S) : copyStacks src dst stk dst = stk src ++ stk dst := by
  simp [copyStacks]

open BitProgram

theorem readRegs_reset {r : ℕ} (regs : Fin r → Bool) (value present : Fin r)
    (top : Option Bool) :
    readRegs (readRegs regs value present top) value present none =
      readRegs regs value present none := by
  funext j
  by_cases hp : j = present
  · subst j; simp [readRegs]
  · by_cases hv : j = value
    · subst j; simp [readRegs, hp]
    · simp [readRegs, hp, hv]

theorem readRegs_frame {r : ℕ} (regs : Fin r → Bool) (value present j : Fin r)
    (top : Option Bool) (hv : j ≠ value) (hp : j ≠ present) :
    readRegs regs value present top j = regs j := by
  simp [readRegs, hv, hp]

/-- The exit state of the clear loop; only its read registers are clobbered. -/
def clearResult {r s l : ℕ} (exit : Fin l) (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, clearStacks src stk⟩

/-- Exact execution of the two-instruction clear loop. Local code equations
allow the routine to be placed inside any finite caller program. -/
theorem clear_trace_aux {r s l : ℕ} (p : Program r s l)
    (src : Fin s) (value present : Fin r) (loop check exit : Fin l)
    (hloop : p.code loop = .pop src value present check)
    (hcheck : p.code check = .branch present loop exit)
    (xs : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hxs : stk src = xs) :
    Trace p (2 * xs.length + 2) ⟨some loop, regs, stk⟩
      (clearResult exit src value present regs stk) := by
  induction xs generalizing regs stk with
  | nil =>
      refine .cons (b := ⟨some check, readRegs regs value present none,
        clearStacks src stk⟩) ?_ ?_
      · simp [step, hloop, execInstr, hxs, clearStacks]
      · refine .cons (b := clearResult exit src value present regs stk) ?_ (.refl _)
        simp [step, hcheck, execInstr, readRegs_present, clearResult]
  | cons a xs ih =>
      let regs' := readRegs regs value present (some a)
      let stk' := Function.update stk src xs
      have hxs' : stk' src = xs := by simp [stk']
      have ht := ih regs' stk' hxs'
      have ht' : Trace p (2 * xs.length + 2) ⟨some loop, regs', stk'⟩
          (clearResult exit src value present regs stk) := by
        simpa only [clearResult, regs', readRegs_reset, stk', clearStacks,
          Function.update_idem] using ht
      have total : Trace p (2 * xs.length + 2 + 1 + 1) ⟨some loop, regs, stk⟩
          (clearResult exit src value present regs stk) := by
        refine .cons (b := ⟨some check, regs', stk'⟩) ?_ ?_
        · simp [step, hloop, execInstr, hxs, regs', stk']
        · refine .cons (b := ⟨some loop, regs', stk'⟩) ?_ ht'
          simp [step, hcheck, execInstr, regs', readRegs_present]
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using total

theorem clear_trace {r s l : ℕ} (p : Program r s l)
    (src : Fin s) (value present : Fin r) (loop check exit : Fin l)
    (hloop : p.code loop = .pop src value present check)
    (hcheck : p.code check = .branch present loop exit)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Trace p (2 * (stk src).length + 2) ⟨some loop, regs, stk⟩
      (clearResult exit src value present regs stk) :=
  clear_trace_aux p src value present loop check exit hloop hcheck _ regs stk rfl

/-- A complete concrete three-label clear program. Label `2` is its halt. -/
abbrev clearProgram {r s : ℕ} (src : Fin s) (value present : Fin r) : Program r s 3 where
  inputStack := src
  outputStack := src
  entry := 0
  code := ![.pop src value present 1, .branch present 0 2, .halt]

theorem clearProgram_trace {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Trace (clearProgram src value present) (2 * (stk src).length + 2)
      ⟨some 0, regs, stk⟩ (clearResult 2 src value present regs stk) :=
  clear_trace _ src value present 0 1 2 rfl rfl regs stk

theorem transferStacks_cons_step {S : Type u} [DecidableEq S]
    (src dst : S) (stk : Stacks S) (a : Bool) (xs : List Bool)
    (hsd : src ≠ dst) (hxs : stk src = a :: xs) :
    transferStacks src dst
        (Function.update (Function.update stk src xs) dst (a :: stk dst)) =
      transferStacks src dst stk := by
  funext j
  by_cases hd : j = dst
  · subst j
    simp [transferStacks, hsd, hxs, List.reverse_cons, List.append_assoc]
  · by_cases hs : j = src
    · subst j
      simp [transferStacks, hsd ]
    · simp [transferStacks, hs, hd]

def transferResult {r s l : ℕ} (exit : Fin l) (src dst : Fin s)
    (value present : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, transferStacks src dst stk⟩

/-- A concrete transfer loop, with one pop, one branch, and one push per bit.
The final empty read and branch account for the additional two transitions. -/
theorem transfer_trace_aux {r s l : ℕ} (p : Program r s l)
    (src dst : Fin s) (value present : Fin r) (loop check put exit : Fin l)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (hloop : p.code loop = .pop src value present check)
    (hcheck : p.code check = .branch present put exit)
    (hput : p.code put = .push dst value loop)
    (xs : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hxs : stk src = xs) :
    Trace p (3 * xs.length + 2) ⟨some loop, regs, stk⟩
      (transferResult exit src dst value present regs stk) := by
  induction xs generalizing regs stk with
  | nil =>
      have hst : transferStacks src dst stk = Function.update stk src [] := by
        funext j
        by_cases hd : j = dst
        · subst j; simp [transferStacks, hxs, hsd.symm]
        · simp [transferStacks, hd]
      refine .cons (b := ⟨some check, readRegs regs value present none,
        Function.update stk src []⟩) ?_ ?_
      · simp [step, hloop, execInstr, hxs]
      · refine .cons (b := transferResult exit src dst value present regs stk) ?_ (.refl _)
        simp [step, hcheck, execInstr, transferResult, hst, readRegs_present]
  | cons a xs ih =>
      let regs' := readRegs regs value present (some a)
      let stk₁ := Function.update stk src xs
      let stk₂ := Function.update stk₁ dst (a :: stk dst)
      have hxs' : stk₂ src = xs := by simp [stk₂, stk₁, hsd]
      have ht := ih regs' stk₂ hxs'
      have hst : transferStacks src dst stk₂ = transferStacks src dst stk :=
        transferStacks_cons_step src dst stk a xs hsd hxs
      have ht' : Trace p (3 * xs.length + 2) ⟨some loop, regs', stk₂⟩
          (transferResult exit src dst value present regs stk) := by
        simpa only [transferResult, regs', readRegs_reset, hst] using ht
      have total : Trace p (3 * xs.length + 2 + 1 + 1 + 1) ⟨some loop, regs, stk⟩
          (transferResult exit src dst value present regs stk) := by
        refine .cons (b := ⟨some check, regs', stk₁⟩) ?_ ?_
        · simp [step, hloop, execInstr, hxs, regs', stk₁]
        · refine .cons (b := ⟨some put, regs', stk₁⟩) ?_ ?_
          · simp [step, hcheck, execInstr, regs', readRegs_present]
          · refine .cons (b := ⟨some loop, regs', stk₂⟩) ?_ ht'
            simp [step, hput, execInstr, regs', stk₂, stk₁,
              readRegs_value, hvp, hsd.symm]
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using total

theorem transfer_trace {r s l : ℕ} (p : Program r s l)
    (src dst : Fin s) (value present : Fin r) (loop check put exit : Fin l)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (hloop : p.code loop = .pop src value present check)
    (hcheck : p.code check = .branch present put exit)
    (hput : p.code put = .push dst value loop)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Trace p (3 * (stk src).length + 2) ⟨some loop, regs, stk⟩
      (transferResult exit src dst value present regs stk) :=
  transfer_trace_aux p src dst value present loop check put exit hsd hvp
    hloop hcheck hput _ regs stk rfl

/-- A complete four-label transfer program; label `3` is its halt. -/
abbrev transferProgram {r s : ℕ} (src dst : Fin s) (value present : Fin r) : Program r s 4 where
  inputStack := src
  outputStack := dst
  entry := 0
  code := ![.pop src value present 1, .branch present 2 3, .push dst value 0, .halt]

theorem transferProgram_trace {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Trace (transferProgram src dst value present) (3 * (stk src).length + 2)
      ⟨some 0, regs, stk⟩ (transferResult 3 src dst value present regs stk) :=
  transfer_trace _ src dst value present 0 1 2 3 hsd hvp rfl rfl rfl regs stk

theorem fanoutStacks_cons_step {S : Type u} [DecidableEq S]
    (src dst₁ dst₂ : S) (stk : Stacks S) (a : Bool) (xs : List Bool)
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₁₂ : dst₁ ≠ dst₂)
    (hxs : stk src = a :: xs) :
    fanoutStacks src dst₁ dst₂
        (Function.update
          (Function.update (Function.update stk src xs) dst₁ (a :: stk dst₁))
          dst₂ (a :: stk dst₂)) =
      fanoutStacks src dst₁ dst₂ stk := by
  funext j
  by_cases hj₂ : j = dst₂
  · subst j
    simp [fanoutStacks, h₁, h₂, h₁₂,
      hxs, List.reverse_cons, List.append_assoc]
  · by_cases hj₁ : j = dst₁
    · subst j
      simp [fanoutStacks, h₁, h₂, h₁₂,
        hxs, List.reverse_cons, List.append_assoc]
    · by_cases hjs : j = src
      · subst j
        simp [fanoutStacks, h₁, h₂, h₁₂]
      · simp [fanoutStacks, hj₁, hj₂, hjs]

def fanoutResult {r s l : ℕ} (exit : Fin l) (src dst₁ dst₂ : Fin s)
    (value present : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, fanoutStacks src dst₁ dst₂ stk⟩

/-- Pop one source and push its bits onto two destinations, using four actual
instructions per nonempty iteration. -/
theorem fanout_trace_aux {r s l : ℕ} (p : Program r s l)
    (src dst₁ dst₂ : Fin s) (value present : Fin r)
    (loop check put₁ put₂ exit : Fin l)
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₁₂ : dst₁ ≠ dst₂) (hvp : value ≠ present)
    (hloop : p.code loop = .pop src value present check)
    (hcheck : p.code check = .branch present put₁ exit)
    (hput₁ : p.code put₁ = .push dst₁ value put₂)
    (hput₂ : p.code put₂ = .push dst₂ value loop)
    (xs : List Bool) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hxs : stk src = xs) :
    Trace p (4 * xs.length + 2) ⟨some loop, regs, stk⟩
      (fanoutResult exit src dst₁ dst₂ value present regs stk) := by
  induction xs generalizing regs stk with
  | nil =>
      have hst : fanoutStacks src dst₁ dst₂ stk = Function.update stk src [] := by
        funext j
        by_cases hj₂ : j = dst₂
        · subst j; simp [fanoutStacks, hxs, h₂.symm]
        · by_cases hj₁ : j = dst₁
          · subst j; simp [fanoutStacks, hxs, h₁.symm, h₁₂]
          · simp [fanoutStacks, hj₁, hj₂]
      refine .cons (b := ⟨some check, readRegs regs value present none,
        Function.update stk src []⟩) ?_ ?_
      · simp [step, hloop, execInstr, hxs]
      · refine .cons (b := fanoutResult exit src dst₁ dst₂ value present regs stk)
          ?_ (.refl _)
        simp [step, hcheck, execInstr, fanoutResult, hst, readRegs_present]
  | cons a xs ih =>
      let regs' := readRegs regs value present (some a)
      let stk₁ := Function.update stk src xs
      let stk₂ := Function.update stk₁ dst₁ (a :: stk dst₁)
      let stk₃ := Function.update stk₂ dst₂ (a :: stk dst₂)
      have hxs' : stk₃ src = xs := by simp [stk₃, stk₂, stk₁, h₁, h₂]
      have ht := ih regs' stk₃ hxs'
      have hst : fanoutStacks src dst₁ dst₂ stk₃ = fanoutStacks src dst₁ dst₂ stk :=
        fanoutStacks_cons_step src dst₁ dst₂ stk a xs h₁ h₂ h₁₂ hxs
      have ht' : Trace p (4 * xs.length + 2) ⟨some loop, regs', stk₃⟩
          (fanoutResult exit src dst₁ dst₂ value present regs stk) := by
        simpa only [fanoutResult, regs', readRegs_reset, hst] using ht
      have total : Trace p (4 * xs.length + 2 + 1 + 1 + 1 + 1) ⟨some loop, regs, stk⟩
          (fanoutResult exit src dst₁ dst₂ value present regs stk) := by
        refine .cons (b := ⟨some check, regs', stk₁⟩) ?_ ?_
        · simp [step, hloop, execInstr, hxs, regs', stk₁]
        · refine .cons (b := ⟨some put₁, regs', stk₁⟩) ?_ ?_
          · simp [step, hcheck, execInstr, regs', readRegs_present]
          · refine .cons (b := ⟨some put₂, regs', stk₂⟩) ?_ ?_
            · simp [step, hput₁, execInstr, regs', stk₂, stk₁,
                readRegs_value, hvp, h₁.symm]
            · refine .cons (b := ⟨some loop, regs', stk₃⟩) ?_ ht'
              simp [step, hput₂, execInstr, regs', stk₃, stk₂, stk₁,
                readRegs_value, hvp, h₂.symm, h₁₂.symm]
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using total

theorem fanout_trace {r s l : ℕ} (p : Program r s l)
    (src dst₁ dst₂ : Fin s) (value present : Fin r)
    (loop check put₁ put₂ exit : Fin l)
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₁₂ : dst₁ ≠ dst₂) (hvp : value ≠ present)
    (hloop : p.code loop = .pop src value present check)
    (hcheck : p.code check = .branch present put₁ exit)
    (hput₁ : p.code put₁ = .push dst₁ value put₂)
    (hput₂ : p.code put₂ = .push dst₂ value loop)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Trace p (4 * (stk src).length + 2) ⟨some loop, regs, stk⟩
      (fanoutResult exit src dst₁ dst₂ value present regs stk) :=
  fanout_trace_aux p src dst₁ dst₂ value present loop check put₁ put₂ exit
    h₁ h₂ h₁₂ hvp hloop hcheck hput₁ hput₂ _ regs stk rfl

theorem fanout_after_transfer_eq_copy {S : Type u} [DecidableEq S]
    (src dst tmp : S) (stk : Stacks S)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : stk tmp = []) :
    fanoutStacks tmp src dst (transferStacks src tmp stk) = copyStacks src dst stk := by
  funext j
  by_cases hd : j = dst
  · subst j
    simp [fanoutStacks, transferStacks, copyStacks, hst,
      hsd.symm, htd.symm, htmp]
  · by_cases hs : j = src
    · subst j
      simp [fanoutStacks, transferStacks, copyStacks, hsd, hst,
        hsd.symm, htd.symm, htmp]
    · by_cases ht : j = tmp
      · subst j
        simp [fanoutStacks, transferStacks, copyStacks, hst, htd,
          hsd.symm, hst.symm, htd.symm, htmp]
      · simp [fanoutStacks, transferStacks, copyStacks, hd, hs, ht]

def copyResult {r s l : ℕ} (exit : Fin l) (src dst : Fin s)
    (value present : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, copyStacks src dst stk⟩

/-- Preserving copy through one initially empty temporary stack. The source is
restored; its original word is prefixed in forward order to the destination. -/
theorem copy_trace {r s l : ℕ} (p : Program r s l)
    (src dst tmp : Fin s) (value present : Fin r)
    (moveLoop moveCheck movePut copyLoop copyCheck copyPut₁ copyPut₂ exit : Fin l)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (hm₀ : p.code moveLoop = .pop src value present moveCheck)
    (hm₁ : p.code moveCheck = .branch present movePut copyLoop)
    (hm₂ : p.code movePut = .push tmp value moveLoop)
    (hc₀ : p.code copyLoop = .pop tmp value present copyCheck)
    (hc₁ : p.code copyCheck = .branch present copyPut₁ exit)
    (hc₂ : p.code copyPut₁ = .push src value copyPut₂)
    (hc₃ : p.code copyPut₂ = .push dst value copyLoop)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmp : stk tmp = []) :
    Trace p (7 * (stk src).length + 4) ⟨some moveLoop, regs, stk⟩
      (copyResult exit src dst value present regs stk) := by
  have move := transfer_trace p src tmp value present moveLoop moveCheck movePut copyLoop
    hst hvp hm₀ hm₁ hm₂ regs stk
  have copy := fanout_trace p tmp src dst value present copyLoop copyCheck copyPut₁ copyPut₂ exit
    hst.symm htd hsd hvp hc₀ hc₁ hc₂ hc₃ (readRegs regs value present none)
    (transferStacks src tmp stk)
  have hlen : (transferStacks src tmp stk tmp).length = (stk src).length := by
    simp [transferStacks, htmp]
  have hfinal := fanout_after_transfer_eq_copy src dst tmp stk hsd hst htd htmp
  have copy' : Trace p (4 * (stk src).length + 2)
      (transferResult copyLoop src tmp value present regs stk)
      (copyResult exit src dst value present regs stk) := by
    simpa only [hlen, transferResult, fanoutResult, copyResult, readRegs_reset, hfinal] using copy
  have total := move.trans copy'
  convert total using 1 ; omega

/-- An eight-label program implementing preserving copy. Label `7` halts. -/
abbrev copyProgram {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r) : Program r s 8 where
  inputStack := src
  outputStack := dst
  entry := 0
  code := ![.pop src value present 1, .branch present 2 3, .push tmp value 0,
    .pop tmp value present 4, .branch present 5 7, .push src value 6, .push dst value 3, .halt]

theorem copyProgram_trace {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmp : stk tmp = []) :
    Trace (copyProgram src dst tmp value present) (7 * (stk src).length + 4)
      ⟨some 0, regs, stk⟩ (copyResult 7 src dst value present regs stk) :=
  copy_trace _ src dst tmp value present 0 1 2 3 4 5 6 7 hsd hst htd hvp
    rfl rfl rfl rfl rfl rfl rfl regs stk htmp

def reverseStacks {S : Type u} [DecidableEq S] (src : S) (stk : Stacks S) : Stacks S :=
  Function.update stk src (stk src).reverse

theorem three_transfers_eq_reverse {S : Type u} [DecidableEq S]
    (src tmp₁ tmp₂ : S) (stk : Stacks S)
    (h₁ : src ≠ tmp₁) (h₂ : src ≠ tmp₂) (h₁₂ : tmp₁ ≠ tmp₂)
    (htmp₁ : stk tmp₁ = []) (htmp₂ : stk tmp₂ = []) :
    transferStacks tmp₂ src (transferStacks tmp₁ tmp₂ (transferStacks src tmp₁ stk)) =
      reverseStacks src stk := by
  funext j
  by_cases hs : j = src
  · subst j
    simp [transferStacks, reverseStacks, h₁, h₂, h₂.symm, h₁₂.symm,
      htmp₁, htmp₂]
  · by_cases ht₁ : j = tmp₁
    · subst j
      simp [transferStacks, reverseStacks, h₁, h₂, h₁₂, h₁.symm, h₂.symm, h₁₂.symm,
        htmp₁, htmp₂]
    · by_cases ht₂ : j = tmp₂
      · subst j
        simp [transferStacks, reverseStacks, h₁, h₂, h₂.symm, h₁₂.symm,
          htmp₁, htmp₂]
      · simp [transferStacks, reverseStacks, hs, ht₁, ht₂]

def reverseResult {r s l : ℕ} (exit : Fin l) (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) : Cfg r s l :=
  ⟨some exit, readRegs regs value present none, reverseStacks src stk⟩

/-- In-place reversal through two initially empty temporary stacks. The
program has ten fixed labels independently of the word length. -/
abbrev reverseProgram {r s : ℕ} (src tmp₁ tmp₂ : Fin s)
    (value present : Fin r) : Program r s 10 where
  inputStack := src
  outputStack := src
  entry := 0
  code := ![.pop src value present 1, .branch present 2 3, .push tmp₁ value 0,
    .pop tmp₁ value present 4, .branch present 5 6, .push tmp₂ value 3,
    .pop tmp₂ value present 7, .branch present 8 9, .push src value 6, .halt]

theorem reverseProgram_trace {r s : ℕ} (src tmp₁ tmp₂ : Fin s) (value present : Fin r)
    (h₁ : src ≠ tmp₁) (h₂ : src ≠ tmp₂) (h₁₂ : tmp₁ ≠ tmp₂) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (htmp₁ : stk tmp₁ = []) (htmp₂ : stk tmp₂ = []) :
    Trace (reverseProgram src tmp₁ tmp₂ value present) (9 * (stk src).length + 6)
      ⟨some 0, regs, stk⟩ (reverseResult 9 src value present regs stk) := by
  let p := reverseProgram src tmp₁ tmp₂ value present
  let regs₁ := readRegs regs value present none
  let regs₂ := readRegs regs₁ value present none
  let stk₁ := transferStacks src tmp₁ stk
  let stk₂ := transferStacks tmp₁ tmp₂ stk₁
  have t₁ := transfer_trace p src tmp₁ value present 0 1 2 3 h₁ hvp
    rfl rfl rfl regs stk
  have t₂ := transfer_trace p tmp₁ tmp₂ value present 3 4 5 6 h₁₂ hvp
    rfl rfl rfl regs₁ stk₁
  have t₃ := transfer_trace p tmp₂ src value present 6 7 8 9 h₂.symm hvp
    rfl rfl rfl regs₂ stk₂
  have hlen₁ : (stk₁ tmp₁).length = (stk src).length := by
    simp [stk₁, transferStacks, htmp₁]
  have hlen₂ : (stk₂ tmp₂).length = (stk src).length := by
    simp [stk₂, stk₁, transferStacks, h₁₂.symm, h₂.symm, htmp₁, htmp₂]
  have hfinal := three_transfers_eq_reverse src tmp₁ tmp₂ stk h₁ h₂ h₁₂ htmp₁ htmp₂
  have total := (t₁.trans t₂).trans t₃
  have total' : Trace p
      ((3 * (stk src).length + 2 + (3 * (stk src).length + 2)) +
        (3 * (stk src).length + 2))
      ⟨some 0, regs, stk⟩ (reverseResult 9 src value present regs stk) := by
    simpa only [hlen₁, hlen₂, transferResult, reverseResult, regs₂, regs₁,
      readRegs_reset, stk₂, stk₁, hfinal] using total
  convert total' using 1 ; omega

theorem transferResult_stack_frame {r s l : ℕ} (exit : Fin l) (src dst j : Fin s)
    (value present : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hs : j ≠ src) (hd : j ≠ dst) :
    (transferResult exit src dst value present regs stk).stacks j = stk j :=
  transferStacks_frame src dst j stk hs hd

theorem copyResult_stack_frame {r s l : ℕ} (exit : Fin l) (src dst j : Fin s)
    (value present : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s)) (hd : j ≠ dst) :
    (copyResult exit src dst value present regs stk).stacks j = stk j :=
  copyStacks_frame src dst j stk hd

theorem transferResult_register_frame {r s l : ℕ} (exit : Fin l) (src dst : Fin s)
    (value present j : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hv : j ≠ value) (hp : j ≠ present) :
    (transferResult exit src dst value present regs stk).regs j = regs j :=
  readRegs_frame regs value present j none hv hp

theorem copyResult_register_frame {r s l : ℕ} (exit : Fin l) (src dst : Fin s)
    (value present j : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hv : j ≠ value) (hp : j ≠ present) :
    (copyResult exit src dst value present regs stk).regs j = regs j :=
  readRegs_frame regs value present j none hv hp

theorem clearResult_stack_frame {r s l : ℕ} (exit : Fin l) (src j : Fin s)
    (value present : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s)) (hs : j ≠ src) :
    (clearResult exit src value present regs stk).stacks j = stk j :=
  clearStacks_frame src j stk hs

theorem clearResult_register_frame {r s l : ℕ} (exit : Fin l) (src : Fin s)
    (value present j : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hv : j ≠ value) (hp : j ≠ present) :
    (clearResult exit src value present regs stk).regs j = regs j :=
  readRegs_frame regs value present j none hv hp

theorem reverseResult_stack_frame {r s l : ℕ} (exit : Fin l) (src j : Fin s)
    (value present : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s)) (hs : j ≠ src) :
    (reverseResult exit src value present regs stk).stacks j = stk j := by
  simp [reverseResult, reverseStacks, hs]

theorem reverseResult_register_frame {r s l : ℕ} (exit : Fin l) (src : Fin s)
    (value present j : Fin r) (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hv : j ≠ value) (hp : j ≠ present) :
    (reverseResult exit src value present regs stk).regs j = regs j :=
  readRegs_frame regs value present j none hv hp

/-- A routine boundary can be turned into a terminating execution by executing
the caller's halt instruction, with exactly one additional transition. -/
theorem halt_after_trace {r s l : ℕ} (p : Program r s l) {n : ℕ}
    {start finish : Cfg r s l} (h : Trace p n start finish) (label : Fin l)
    (hpc : finish.pc = some label) (hcode : p.code label = .halt) :
    Trace p (n + 1) start {finish with pc := none} :=
  h.trans (.cons (step_code p finish label .halt hpc hcode) (.refl _))

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
