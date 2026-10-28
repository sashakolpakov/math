import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! A fixed row workspace disjoint from the source evaluator and live caches.
The image is 22..25, 30..73, and75; all temporary words are physically cleared
before the source code is returned on26. -/

namespace SubexponentialSAT.Subexp.UniversalRowWorkspace

open BitProgram StructuredCalls StackRoutines

abbrev Word := List Bool
abbrev Data := State 16 288
abbrev Code := Cmd 16 288

def port (j : Fin 49) : Fin 288 :=
  if j.val < 4 then ⟨22 + j.val, by omega⟩
  else if j.val < 48 then ⟨26 + j.val, by omega⟩ else 75

theorem port_val (j : Fin 49) :
    (port j).val = if j.val < 4 then 22 + j.val else if j.val < 48 then 26 + j.val else 75 := by
  unfold port
  split_ifs <;> rfl

theorem port_injective : Function.Injective port := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [port_val, port_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem port_ne_code (j : Fin 49) : port j ≠ 26 := by
  intro h
  have hv := congrArg Fin.val h
  change (port j).val = 26 at hv
  rw [port_val] at hv
  split_ifs at hv <;> omega

theorem port_ne_targetWidth (j : Fin 49) : port j ≠ 74 := by
  intro h
  have hv := congrArg Fin.val h
  change (port j).val = 74 at hv
  rw [port_val] at hv
  split_ifs at hv <;> omega

theorem port_lt_cache (j : Fin 49) : (port j).val < 128 := by
  rw [port_val]
  split_ifs <;> omega

def workPorts : List (Fin 288) := (List.finRange 49).map port

theorem workPorts_length : workPorts.length = 49 := by simp [workPorts]

theorem mem_workPorts (j : Fin 288) : j ∈ workPorts ↔ ∃ k, port k = j := by
  simp [workPorts]

def cleared (a : Data) (j : Fin 288) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks j a.stacks⟩

def clearList : List (Fin 288) → Code
  | [] => .base .skip
  | j :: js => .seq (.call (clearProgram j (0 : Fin 16) 1)) (clearList js)

def clearResult : List (Fin 288) → Data → Data
  | [], a => a
  | j :: js, a => clearResult js (cleared a j)

def clearCost : List (Fin 288) → Data → ℕ
  | [], _ => 0
  | j :: js, a => 2 * (a.stacks j).length + 3 + clearCost js (cleared a j)

theorem clearList_eval (js : List (Fin 288)) (a : Data) :
    Eval (clearList js) (clearCost js a) a (clearResult js a) := by
  induction js generalizing a with
  | nil => exact .base (.skip _)
  | cons j js ih =>
      exact (TupleProgram.clear_eval j (0 : Fin 16) 1 a).seq (ih (cleared a j))

theorem clearResult_stacks (js : List (Fin 288)) (a : Data) (k : Fin 288) :
    (clearResult js a).stacks k = if k ∈ js then [] else a.stacks k := by
  induction js generalizing a with
  | nil => simp [clearResult]
  | cons j js ih =>
      rw [clearResult, ih]
      by_cases hkj : k = j <;> by_cases hks : k ∈ js <;>
        simp [hkj, hks, cleared, clearStacks]

theorem clearCost_bound (js : List (Fin 288)) (a : Data) (L : ℕ)
    (hL : ∀ j ∈ js, (a.stacks j).length ≤ L) :
    clearCost js a ≤ js.length * (2 * L + 3) := by
  induction js generalizing a with
  | nil => simp [clearCost]
  | cons j js ih =>
      have hj := hL j (by simp)
      have hrest : ∀ k ∈ js, ((cleared a j).stacks k).length ≤ L := by
        intro k hk
        by_cases hkj : k = j
        · simp [hkj, cleared, clearStacks]
        · simpa [cleared, clearStacks, hkj] using hL k (by simp [hk])
      have ht := ih (cleared a j) hrest
      simp only [clearCost, List.length_cons]
      nlinarith

def cleanup : Code := clearList workPorts

theorem cleanup_eval (a : Data) :
    Eval cleanup (clearCost workPorts a) a (clearResult workPorts a) := clearList_eval _ _

theorem cleanup_clears (a : Data) (j : Fin 49) :
    (clearResult workPorts a).stacks (port j) = [] := by
  rw [clearResult_stacks, ite_eq_left]
  exact mem_workPorts (port j) |>.mpr ⟨j, rfl⟩

theorem cleanup_frame (a : Data) (j : Fin 288) (hj : ¬ ∃ k, port k = j) :
    (clearResult workPorts a).stacks j = a.stacks j := by
  rw [clearResult_stacks, ite_eq_right]
  exact (mem_workPorts j).not.mpr hj

def moveCode : Code :=
  .seq (.call (transferProgram (port 31) (port 44) (0 : Fin 16) 1))
    (.call (transferProgram (port 44) 26 (0 : Fin 16) 1))

def command : Code := .seq moveCode cleanup

theorem moveCode_eval (a : Data) (source : Word)
    (hsource : a.stacks (port 31) = source)
    (htmp : a.stacks (port 44) = []) (hcode : a.stacks 26 = []) :
    ∃ b : Data, Eval moveCode (6 * source.length + 6) a b ∧
      b.stacks = Function.update (Function.update (Function.update a.stacks
        (port 31) []) (port 44) []) 26 source := by
  let mid : Data := ⟨readRegs a.regs 0 1 none, transferStacks (port 31) (port 44) a.stacks⟩
  have h1 := TupleProgram.transfer_eval (port 31) (port 44) (0 : Fin 16) 1
    (by decide) (by decide) a
  have h2 := TupleProgram.transfer_eval (port 44) (26 : Fin 288) (0 : Fin 16) 1
    (port_ne_code 44) (by decide) mid
  let b : Data := ⟨readRegs mid.regs 0 1 none, transferStacks (port 44) 26 mid.stacks⟩
  refine ⟨b, ?_, ?_⟩
  · have hmiddle : (mid.stacks (port 44)).length = source.length := by
      simp [mid, transferStacks, hsource, htmp]
    have h := h1.seq h2
    change Eval moveCode ((3 * (a.stacks (port 31)).length + 3) +
      (3 * (mid.stacks (port 44)).length + 3)) a b at h
    rw [hsource, hmiddle] at h
    convert h using 1 ; omega
  · funext k
    have h3144 : port 31 ≠ port 44 := by decide
    have h3126 : port 31 ≠ 26 := port_ne_code 31
    have h4426 : port 44 ≠ 26 := port_ne_code 44
    by_cases hk31 : k = port 31
    · subst k
      simp [b, mid, transferStacks, hsource, htmp, hcode,
        h3144, h3126, Ne.symm h3126, Ne.symm h4426]
    by_cases hk44 : k = port 44
    · subst k
      simp [b, mid, transferStacks, hsource, htmp, hcode, h4426, Ne.symm h3126, Ne.symm h4426]
    by_cases hk26 : k = 26
    · subst k
      simp [b, mid, transferStacks, hsource, htmp, hcode, Ne.symm h3126, Ne.symm h4426]
    · simp [b, mid, transferStacks, hk31, hk44, hk26]

theorem command_eval (a : Data) (source : Word)
    (hsource : a.stacks (port 31) = source)
    (htmp : a.stacks (port 44) = []) (hcode : a.stacks 26 = []) :
    ∃ n, ∃ b : Data, Eval command n a b ∧
      (∀ j : Fin 49, b.stacks (port j) = []) ∧ b.stacks 26 = source ∧
      (∀ j : Fin 288, j ≠ 26 → (¬ ∃ k, port k = j) → b.stacks j = a.stacks j) ∧
      n = 6 * source.length + 6 + clearCost workPorts
        ⟨readRegs (readRegs a.regs 0 1 none) 0 1 none,
          Function.update (Function.update (Function.update a.stacks
            (port 31) []) (port 44) []) 26 source⟩ := by
  obtain ⟨mid, hm, hms⟩ := moveCode_eval a source hsource htmp hcode
  let b := clearResult workPorts mid
  refine ⟨6 * source.length + 6 + clearCost workPorts mid, b,
    hm.seq (cleanup_eval mid), cleanup_clears mid, ?_, ?_, ?_⟩
  · rw [cleanup_frame mid 26 (by rintro ⟨k, hk⟩; exact port_ne_code k hk), hms]
    simp
  · intro j hj hjwork
    rw [cleanup_frame mid j hjwork, hms]
    have h31 : j ≠ port 31 := fun h => hjwork ⟨31, h.symm⟩
    have h44 : j ≠ port 44 := fun h => hjwork ⟨44, h.symm⟩
    simp [hj, h31, h44]
  · have hcost : clearCost workPorts mid = clearCost workPorts
        ⟨readRegs (readRegs a.regs 0 1 none) 0 1 none,
          Function.update (Function.update (Function.update a.stacks
            (port 31) []) (port 44) []) 26 source⟩ := by
      have sameStacks (js : List (Fin 288)) (s t : Data) (hst : s.stacks = t.stacks) :
          clearCost js s = clearCost js t := by
        induction js generalizing s t with
        | nil => rfl
        | cons j js ih =>
            simp only [clearCost]
            rw [hst, ih (cleared s j) (cleared t j) (by simp [cleared, hst])]
      exact sameStacks _ _ _ hms
    rw [hcost]

end SubexponentialSAT.Subexp.UniversalRowWorkspace

end OAI.Algorithms
