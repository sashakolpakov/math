import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

/-- Fill each selected port with the original source word. -/
def fillStacks {S : Type u} [DecidableEq S] (src : S) (dests : List S)
    (stk : Stacks S) : Stacks S :=
  fun j => if j ∈ dests then stk src else stk j

/-- Empty the selected bank, preserving every other stack. -/
def clearBankStacks {S : Type u} [DecidableEq S] (ports : List S)
    (stk : Stacks S) : Stacks S :=
  fun j => if j ∈ ports then [] else stk j

@[simp] theorem fillStacks_nil {S : Type u} [DecidableEq S]
    (src : S) (stk : Stacks S) : fillStacks src [] stk = stk := by
  funext j
  simp [fillStacks]

@[simp] theorem fillStacks_mem {S : Type u} [DecidableEq S]
    (src j : S) (dests : List S) (stk : Stacks S) (hj : j ∈ dests) :
    fillStacks src dests stk j = stk src := by
  simp [fillStacks, hj]

theorem fillStacks_frame {S : Type u} [DecidableEq S]
    (src j : S) (dests : List S) (stk : Stacks S) (hj : j ∉ dests) :
    fillStacks src dests stk j = stk j := by
  simp [fillStacks, hj]

@[simp] theorem clearBankStacks_nil {S : Type u} [DecidableEq S]
    (stk : Stacks S) : clearBankStacks [] stk = stk := by
  funext j
  simp [clearBankStacks]

@[simp] theorem clearBankStacks_mem {S : Type u} [DecidableEq S]
    (j : S) (ports : List S) (stk : Stacks S) (hj : j ∈ ports) :
    clearBankStacks ports stk j = [] := by
  simp [clearBankStacks, hj]

theorem clearBankStacks_frame {S : Type u} [DecidableEq S]
    (j : S) (ports : List S) (stk : Stacks S) (hj : j ∉ ports) :
    clearBankStacks ports stk j = stk j := by
  simp [clearBankStacks, hj]

theorem clearStacks_eq_self_of_empty {S : Type u} [DecidableEq S]
    (tmp : S) (stk : Stacks S) (htmp : stk tmp = []) :
    clearStacks tmp stk = stk := by
  funext j
  by_cases hj : j = tmp
  · subst j
    simp [htmp]
  · exact clearStacks_frame _ _ _ hj

theorem fillStacks_cons {S : Type u} [DecidableEq S]
    (src dst : S) (dests : List S) (stk : Stacks S)
    (hsd : src ≠ dst) (hdst : stk dst = []) :
    fillStacks src dests (copyStacks src dst stk) =
      fillStacks src (dst :: dests) stk := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [fillStacks, copyStacks, hsd, hdst]
  · simp [fillStacks, copyStacks, hsd, hj]

theorem clearBankStacks_cons {S : Type u} [DecidableEq S]
    (dst : S) (ports : List S) (stk : Stacks S) :
    clearBankStacks ports (clearStacks dst stk) =
      clearBankStacks (dst :: ports) stk := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [clearBankStacks]
  · simp [clearBankStacks, clearStacks, hj]

/-- One copy per static destination, followed by a read-register reset. -/
def fillCmd {r s : ℕ} (src tmp : Fin s) (value present : Fin r) :
    List (Fin s) → Cmd r s
  | [] => .call (clearProgram tmp value present)
  | dst :: dests => .seq (.call (copyProgram src dst tmp value present))
      (fillCmd src tmp value present dests)

/-- One clear per static bank port, followed by a read-register reset. -/
def clearCmd {r s : ℕ} (tmp : Fin s) (value present : Fin r) :
    List (Fin s) → Cmd r s
  | [] => .call (clearProgram tmp value present)
  | dst :: ports => .seq (.call (clearProgram dst value present))
      (clearCmd tmp value present ports)

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

theorem copy_call_eval {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmp : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp value present)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, copyStacks src dst stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst tmp value present hsd hst htd hvp regs stk htmp

@[simp] theorem size_fillCmd {r s : ℕ} (src tmp : Fin s) (value present : Fin r)
    (dests : List (Fin s)) :
    size (fillCmd src tmp value present dests) = 8 * dests.length + 3 := by
  induction dests with
  | nil => rfl
  | cons dst dests ih => simp [fillCmd, size, ih, Nat.mul_add]; omega

@[simp] theorem size_clearCmd {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) :
    size (clearCmd tmp value present ports) = 3 * ports.length + 3 := by
  induction ports with
  | nil => rfl
  | cons dst ports ih => simp [clearCmd, size, ih, Nat.mul_add]; omega

/-- Exact execution of the static fill list.  The original source word and the
empty temporary are preserved, as are all unlisted stacks and unread registers.
-/
theorem fill_eval {r s : ℕ} (src tmp : Fin s) (value present : Fin r)
    (dests : List (Fin s)) (hdests : dests.Nodup)
    (hsrc : src ∉ dests) (htmp : tmp ∉ dests)
    (hst : src ≠ tmp) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (hempty : ∀ j ∈ dests, stk j = []) (htmpEmpty : stk tmp = []) :
    Eval (fillCmd src tmp value present dests)
      (dests.length * (7 * (stk src).length + 5) + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, fillStacks src dests stk⟩ := by
  induction dests generalizing regs stk with
  | nil =>
      have run := clear_call_eval tmp value present regs stk
      simpa [fillCmd, htmpEmpty, clearStacks_eq_self_of_empty tmp stk htmpEmpty] using run
  | cons dst dests ih =>
      have hn := List.nodup_cons.mp hdests
      have hsd : src ≠ dst := fun h => hsrc (by simp [h])
      have htd : tmp ≠ dst := fun h => htmp (by simp [h])
      have hsrc' : src ∉ dests := fun h => hsrc (by simp [h])
      have htmp' : tmp ∉ dests := fun h => htmp (by simp [h])
      have hdst : stk dst = [] := hempty dst (by simp)
      have hframe : copyStacks src dst stk src = stk src :=
        copyStacks_frame src dst src stk hsd
      have htemp : copyStacks src dst stk tmp = [] := by
        rw [copyStacks_frame src dst tmp stk htd, htmpEmpty]
      have hempty' : ∀ j ∈ dests, copyStacks src dst stk j = [] := by
        intro j hj
        have hjd : j ≠ dst := by
          intro h
          subst j
          exact hn.1 hj
        rw [copyStacks_frame src dst j stk hjd]
        exact hempty j (by simp [hj])
      have first := copy_call_eval src dst tmp value present
        hsd hst htd hvp regs stk htmpEmpty
      have rest := ih hn.2 hsrc' htmp'
        (readRegs regs value present none) (copyStacks src dst stk) hempty' htemp
      have run := Eval.seq first rest
      simpa only [fillCmd, List.length_cons, Nat.add_mul, one_mul, hframe,
        readRegs_reset, fillStacks_cons src dst dests stk hsd hdst,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

/-- Exact clearing cost in terms of the original word lengths.  The temporary
may also occur in the bank: its initial emptiness makes the final clear cost
exactly three instructions in either case. -/
theorem clear_eval {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) (hports : ports.Nodup)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmpEmpty : stk tmp = []) :
    Eval (clearCmd tmp value present ports)
      (2 * (ports.map (fun j => (stk j).length)).sum + 3 * ports.length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearBankStacks ports stk⟩ := by
  induction ports generalizing regs stk with
  | nil =>
      have run := clear_call_eval tmp value present regs stk
      simpa [clearCmd, htmpEmpty, clearStacks_eq_self_of_empty tmp stk htmpEmpty] using run
  | cons dst ports ih =>
      have hn := List.nodup_cons.mp hports
      have htemp : clearStacks dst stk tmp = [] := by
        by_cases h : tmp = dst
        · subst tmp
          simp
        · rw [clearStacks_frame dst tmp stk h, htmpEmpty]
      have hmap : ports.map (fun j => (clearStacks dst stk j).length) =
          ports.map (fun j => (stk j).length) := by
        apply List.map_congr_left
        intro j hj
        have hjd : j ≠ dst := by
          intro h
          subst j
          exact hn.1 hj
        rw [clearStacks_frame dst j stk hjd]
      have first := clear_call_eval dst value present regs stk
      have rest := ih hn.2 (readRegs regs value present none)
        (clearStacks dst stk) htemp
      have run := Eval.seq first rest
      simpa only [clearCmd, List.map_cons, List.sum_cons, List.length_cons,
        hmap, readRegs_reset, clearBankStacks_cons, Nat.mul_add,
        Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

/-- Equal-width bank cleanup has linear cost in that runtime width. -/
theorem clear_eval_uniform {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) (hports : ports.Nodup)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (w : ℕ)
    (hwidth : ∀ j ∈ ports, (stk j).length = w) (htmpEmpty : stk tmp = []) :
    Eval (clearCmd tmp value present ports) (ports.length * (2 * w + 3) + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearBankStacks ports stk⟩ := by
  have hsum : (ports.map (fun j => (stk j).length)).sum = ports.length * w := by
    induction ports with
    | nil => simp
    | cons dst ports ih =>
        have hdst := hwidth dst (by simp)
        have ht : ∀ j ∈ ports, (stk j).length = w := fun j hj => hwidth j (by simp [hj])
        simp only [List.map_cons, List.sum_cons, List.length_cons, hdst,
          ih (List.nodup_cons.mp hports).2 ht, Nat.add_mul, Nat.one_mul]
        omega
  have run := clear_eval tmp value present ports hports regs stk htmpEmpty
  rw [hsum] at run
  simpa only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using run

/-- Explicit register frame supplied by both execution theorems. -/
theorem reset_frame {r : ℕ} (regs : Fin r → Bool) (value present j : Fin r)
    (hv : j ≠ value) (hp : j ≠ present) :
    readRegs regs value present none j = regs j :=
  readRegs_frame regs value present j none hv hp

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
