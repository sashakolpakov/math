import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafMarkedProgramFold
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramMass

namespace OAI.Algorithms

/-! A fixed streaming marked-clause collector. Only reference records are input.
Each record runs the paid count-query command, and its computed little-endian
answer is immediately consumed by the primitive integer adder. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Marked.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 40 768
abbrev Code := Cmd 40 768

def recordPorts : RecordPrograms.Ports 40 768 where
  tag := 16
  present := 17
  found := 18
  source := 320
  payload := 321
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def massPorts : Mass.Ports 40 768 where
  register i := i.castAdd 32
  stack := ![322,323,324]
  register_injective := Fin.castAdd_injective 8 32
  stack_injective := by decide

/-- The workspace omits exactly the five collector stacks 320,...,324. -/
def workPort (i : Fin 763) : Fin 768 :=
  if h : i.val < 320 then ⟨i.val, by omega⟩ else ⟨i.val + 5, by omega⟩
def workspace (a : Data) : Fin 763 → List Bool := fun i => a.stacks (workPort i)
def read (a : Data) : List Bool := a.stacks 322

def invariant (ready : (Fin 763 → List Bool) → Prop) (a : Data) : Prop :=
  ready (workspace a) ∧ a.stacks 323 = [] ∧ a.stacks 324 = []

def step (answer : List Bool → List Bool) (bits acc : List Bool) : List Bool :=
  BinaryArithmetic.add acc (answer bits)
def cost (answer : List Bool → List Bool) (queryCost : List Bool → ℕ)
    (acc bits : List Bool) : ℕ :=
  queryCost bits + 16 * (max acc.length (answer bits).length + 1) + 3

/-- This is a trace contract for an actual command, not a count oracle.
The answer function appears only in the correctness statement. -/
def QueryContract (query : Code) (answer : List Bool → List Bool)
    (queryCost : List Bool → ℕ) (ready : (Fin 763 → List Bool) → Prop)
    (valid : List Bool → Prop) : Prop :=
  ∀ bits tail (base : Data), valid bits → invariant ready base →
    ∃ n middle, n ≤ queryCost bits ∧ ready (workspace middle) ∧
      read middle = read base ∧ middle.stacks 323 = answer bits ∧ middle.stacks 324 = [] ∧
      Eval query n (RecordPrograms.state recordPorts base false true false tail bits.reverse)
        (RecordPrograms.state recordPorts middle false true false tail [])

def callback (query : Code) : Code := .seq query (Mass.invoke massPorts)
def command (query : Code) : Code := foldCommand recordPorts (callback query)
def program (query : Code) := compiled (command query) 320 322

private theorem workPort_ne (i : Fin 763) (j : Fin 768) (hj : 320 ≤ j.val ∧ j.val ≤ 324) :
    workPort i ≠ j := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [workPort] at hv
  split_ifs at hv <;> simp only at hv <;> omega

@[simp] theorem workspace_recordState (a : Data) (v pr f : Bool) (src payload : List Bool) :
    workspace (RecordPrograms.state recordPorts a v pr f src payload) = workspace a := by
  funext i
  have hs := workPort_ne i 320 (by decide)
  have hp := workPort_ne i 321 (by decide)
  simp [workspace, RecordPrograms.state, recordPorts, hs, hp]

private theorem mass_state_eq_self (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool)
    (hr : ∀ i, regs i = a.regs (massPorts.register i))
    (hs : ∀ i, (Mass.data regs acc next).stacks i = a.stacks (massPorts.stack i)) :
    Mass.state massPorts a regs acc next = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, massPorts.register j = i
    · obtain ⟨j, rfl⟩ := h
      exact (embedState_register massPorts.register massPorts.stack a (Mass.data regs acc next) massPorts.register_injective j).trans (hr j)
    · exact embedState_register_frame massPorts.register massPorts.stack a (Mass.data regs acc next) i h
  · funext i
    by_cases h : ∃ j, massPorts.stack j = i
    · obtain ⟨j, rfl⟩ := h
      exact (embedState_stack massPorts.register massPorts.stack a (Mass.data regs acc next) massPorts.stack_injective j).trans (hs j)
    · exact embedState_stack_frame massPorts.register massPorts.stack a (Mass.data regs acc next) i h

private theorem mass_stack_local (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool)
    (i : Fin 3) :
    (Mass.state massPorts a regs acc next).stacks (massPorts.stack i) =
      (Mass.data regs acc next).stacks i :=
  embedState_stack _ _ _ _ massPorts.stack_injective i

private theorem mass_stack_frame (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool)
    (i : Fin 768) (hi : i.val < 322 ∨ 324 < i.val) :
    (Mass.state massPorts a regs acc next).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  fin_cases j <;> simp [massPorts] at hh <;> omega

private theorem mass_reg_frame (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool)
    (i : Fin 40) (hi : 8 ≤ i.val) :
    (Mass.state massPorts a regs acc next).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  simp [massPorts] at hh
  omega

@[simp] theorem workspace_mass_state (a : Data) (regs : Fin 8 → Bool) (acc next : List Bool) :
    workspace (Mass.state massPorts a regs acc next) = workspace a := by
  funext i
  apply mass_stack_frame
  dsimp [workPort]
  split_ifs <;> simp only [] <;> omega

theorem callback_contract (query : Code) (answer : List Bool → List Bool)
    (queryCost : List Bool → ℕ) (ready : (Fin 763 → List Bool) → Prop)
    (valid : List Bool → Prop) (hq : QueryContract query answer queryCost ready valid) :
    DynamicFoldContractOn recordPorts (callback query) read (step answer)
      (cost answer queryCost) (invariant ready) valid := by
  intro bits tail base hv hb
  obtain ⟨n, middle, hn, hm, hr, hc, hs, ht⟩ := hq bits tail base hv hb
  let a := RecordPrograms.state recordPorts middle false true false tail []
  let regs := fun i => a.regs (massPorts.register i)
  have ha : Mass.state massPorts a regs (read base) (answer bits) = a := by
    apply mass_state_eq_self _ _ _ _ (fun _ => rfl)
    intro i
    fin_cases i <;>
      simp [Mass.data, BinaryPrograms.Add.stackState, massPorts, a,
        RecordPrograms.state, recordPorts, read] at hr ⊢
    · exact hr.symm
    · exact hc.symm
    · exact hs
  obtain ⟨m, hmn, regs', he⟩ := Mass.invoke_eval massPorts a regs (read base) (answer bits)
  let b := Mass.state massPorts a regs' (step answer bits (read base)) []
  have hb322 : b.stacks 322 = step answer bits (read base) := mass_stack_local a regs' _ [] 0
  have hb323 : b.stacks 323 = [] := mass_stack_local a regs' _ [] 1
  have hb324 : b.stacks 324 = [] := mass_stack_local a regs' _ [] 2
  have hb320 : b.stacks 320 = tail := by rw [mass_stack_frame _ _ _ _ _ (by decide)]; rfl
  have hb321 : b.stacks 321 = [] := by rw [mass_stack_frame _ _ _ _ _ (by decide)]; rfl
  have hb16 : b.regs 16 = false := by rw [mass_reg_frame _ _ _ _ _ (by decide)]; rfl
  have hb17 : b.regs 17 = true := by rw [mass_reg_frame _ _ _ _ _ (by decide)]; rfl
  have hb18 : b.regs 18 = false := by rw [mass_reg_frame _ _ _ _ _ (by decide)]; rfl
  have hstate : RecordPrograms.state recordPorts b false true false tail [] = b :=
    RecordPrograms.state_eq_self recordPorts b _ _ _ _ _ hb16 hb17 hb18 hb320 hb321
  refine ⟨n+m, b, by dsimp [cost]; omega, ?_, hb322, ?_⟩
  · refine ⟨?_,hb323,hb324⟩
    simpa [b,a] using hm
  · rw [hstate]
    apply Eval.seq ht
    simpa only [ha, step, b] using he

/-- Consume one physically computed count word, without requiring a canonical
representation of that integer. -/
theorem add_count_eval (ready : (Fin 763 → List Bool) → Prop)
    (middle : Data) (tail acc word : List Bool)
    (hm : ready (workspace middle)) (hr : read middle = acc)
    (hc : middle.stacks 323 = word) (hs : middle.stacks 324 = []) :
    ∃ n next, n ≤ 16*(max acc.length word.length+1)+3 ∧
      invariant ready next ∧ read next = BinaryArithmetic.add acc word ∧
      Eval (Mass.invoke massPorts) n
        (RecordPrograms.state recordPorts middle false true false tail [])
        (RecordPrograms.state recordPorts next false true false tail []) := by
  let a := RecordPrograms.state recordPorts middle false true false tail []
  let regs := fun i => a.regs (massPorts.register i)
  have ha : Mass.state massPorts a regs acc word = a := by
    apply mass_state_eq_self _ _ _ _ (fun _ => rfl)
    intro i
    fin_cases i <;>
      simp [Mass.data, BinaryPrograms.Add.stackState, massPorts, a,
        RecordPrograms.state, recordPorts, read] at hr ⊢
    · exact hr.symm
    · exact hc.symm
    · exact hs
  obtain ⟨n, hn, regs', he⟩ := Mass.invoke_eval massPorts a regs acc word
  let b := Mass.state massPorts a regs' (BinaryArithmetic.add acc word) []
  have hb322 : b.stacks 322 = BinaryArithmetic.add acc word := mass_stack_local a regs' _ [] 0
  have hb323 : b.stacks 323 = [] := mass_stack_local a regs' _ [] 1
  have hb324 : b.stacks 324 = [] := mass_stack_local a regs' _ [] 2
  have hb320 : b.stacks 320 = tail := by rw [mass_stack_frame _ _ _ _ _ (by decide)]; rfl
  have hb321 : b.stacks 321 = [] := by rw [mass_stack_frame _ _ _ _ _ (by decide)]; rfl
  have hb16 : b.regs 16 = false := by rw [mass_reg_frame _ _ _ _ _ (by decide)]; rfl
  have hb17 : b.regs 17 = true := by rw [mass_reg_frame _ _ _ _ _ (by decide)]; rfl
  have hb18 : b.regs 18 = false := by rw [mass_reg_frame _ _ _ _ _ (by decide)]; rfl
  have hstate : RecordPrograms.state recordPorts b false true false tail [] = b :=
    RecordPrograms.state_eq_self recordPorts b _ _ _ _ _ hb16 hb17 hb18 hb320 hb321
  refine ⟨n,b,hn,⟨?_,hb323,hb324⟩,hb322,?_⟩
  · simpa [b,a] using hm
  · rw [hstate]
    simpa only [ha,b] using he
end SubexponentialSAT.SqrtLog.LeafProgram.Marked.Wide

end OAI.Algorithms
