import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrepareCount
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgramRun

namespace OAI.Algorithms

/-! Construct the full ambient head-support mask from the IDs actually
selected. A low-variable mask alone is not a head-support mask. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def countRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def countInputs : List (Fin 768 × Fin 2) := [(651,0)]
def countOutputs : List (Fin 2 × Fin 768) := [(1,652)]
def trueCount : Code := stage PackingHeadProgramPrepareCount.program countRegs (by decide)
  countInputs countOutputs

def countResult (a : Data) : Data := returned countRegs (by decide) countInputs countOutputs a
  (PackingHeadProgramPrepareCount.state (fun _ => false) [] (List.replicate (a.stacks 651).length true))
def countCost (a : Data) : ℕ := stageCost countRegs (by decide) countInputs countOutputs a
  (PackingHeadProgramPrepareCount.state (fun _ => false) [] (List.replicate (a.stacks 651).length true))
  (4*(a.stacks 651).length+4)

theorem countInputs_protected : ∀ p∈countInputs,Protected p.1 := by simp [countInputs,Protected,temporary]
theorem countOutputs_protected : ∀ p∈countOutputs,Protected p.2 := by simp [countOutputs,Protected,temporary]

theorem trueCount_eval (a : Data) : Eval trueCount (countCost a) a (countResult a) := by
  let regs := (prepared (by decide) countInputs a).regs ∘ countRegs
  have hp : projectState countRegs (workPort (by decide)) (prepared (by decide) countInputs a)=
      PackingHeadProgramPrepareCount.state regs (a.stacks 651) [] := by
    apply prepared_eq countRegs (by decide) countInputs a _ countInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [countInputs,List.mem_singleton] at hp
      subst p
      rfl
    · intro j hj
      fin_cases j
      · exact False.elim (hj (651,0) (by simp [countInputs]) rfl)
      · rfl
  have ht := PackingHeadProgramPrepareCount.trace regs (a.stacks 651) []
  simp only [List.append_nil] at ht
  exact stage_eval PackingHeadProgramPrepareCount.program countRegs (Fin.castAdd_injective _ _)
    (by decide) countInputs countOutputs a _ _ countInputs_protected countOutputs_protected hp ht

theorem countResult_value (a : Data) : (countResult a).stacks 652=List.replicate (a.stacks 651).length true :=
  returned_word countRegs (by decide) countInputs countOutputs a _ countOutputs_protected
    (by decide) (1,652) (by simp [countOutputs])

theorem countResult_frame (a : Data) (i : Fin 768) (hi : Protected i) (h652 : i≠652) :
    (countResult a).stacks i=a.stacks i := by
  apply returned_frame countRegs (by decide) countInputs countOutputs a _ i hi
  intro p hp
  simp only [countOutputs,List.mem_singleton] at hp
  subst p
  exact h652

def scatterRegs : Fin 8 → Fin 16 := Fin.castAdd 8
def scatterInputs : List (Fin 768 × Fin 13) := [(650,10),(652,11),(128,12)]
def scatterOutputs : List (Fin 13 × Fin 768) := [(0,670)]
def scatterSupport : Code := stage HeadScatterProgram.program scatterRegs (by decide)
  scatterInputs scatterOutputs

theorem scatterInputs_protected : ∀ p∈scatterInputs,Protected p.1 := by simp [scatterInputs,Protected,temporary]
theorem scatterOutputs_protected : ∀ p∈scatterOutputs,Protected p.2 := by simp [scatterOutputs,Protected,temporary]

def scatterResult (a : Data) (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) : Data :=
  returned scatterRegs (by decide) scatterInputs scatterOutputs a
    (HeadScatterProgram.result regs js (List.replicate js.length true) n)
def scatterCost (a : Data) (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) : ℕ :=
  stageCost scatterRegs (by decide) scatterInputs scatterOutputs a
    (HeadScatterProgram.result regs js (List.replicate js.length true) n)
    (100*(n+1)*(js.length+1))

theorem scatterSupport_eval (a : Data) (n : ℕ) (js : List ℕ)
    (hi : a.stacks 650=HeadScatterProgram.indices js)
    (hc : a.stacks 652=List.replicate js.length true)
    (hn : a.stacks 128=List.replicate n true) (hb : ∀ j∈js,j < n) :
    ∃ regs t,t ≤ scatterCost a regs n js ∧ Eval scatterSupport t a (scatterResult a regs n js) := by
  let regs := (prepared (by decide) scatterInputs a).regs ∘ scatterRegs
  have hp : projectState scatterRegs (workPort (by decide)) (prepared (by decide) scatterInputs a)=
      HeadScatterProgram.input regs js (List.replicate js.length true) n := by
    apply prepared_eq scatterRegs (by decide) scatterInputs a _ scatterInputs_protected (by decide)
    · intro j; rfl
    · intro p hp
      simp only [scatterInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl <;> simp [HeadScatterProgram.input,HeadScatterProgram.unary,hi,hc,hn]
    · intro j hj
      have h10 : j≠10 := hj (650,10) (by simp [scatterInputs])
      have h11 : j≠11 := hj (652,11) (by simp [scatterInputs])
      have h12 : j≠12 := hj (128,12) (by simp [scatterInputs])
      fin_cases j <;> simp_all [HeadScatterProgram.input]
  obtain ⟨rf,t,ht,he⟩ := HeadScatterProgram.program_runsIn regs n js (List.replicate js.length true)
    (by simp) hb
  have h := stage_eval HeadScatterProgram.program scatterRegs (Fin.castAdd_injective _ _)
    (by decide) scatterInputs scatterOutputs a _ _ scatterInputs_protected scatterOutputs_protected hp he
  refine ⟨rf,_,?_,h⟩
  unfold scatterCost stageCost
  omega

theorem scatterResult_value (a : Data) (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) :
    (scatterResult a regs n js).stacks 670=HeadScatterProgram.mask n js (List.replicate js.length true) :=
  returned_word scatterRegs (by decide) scatterInputs scatterOutputs a _ scatterOutputs_protected
    (by decide) (0,670) (by simp [scatterOutputs])

theorem scatterResult_frame (a : Data) (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ)
    (i : Fin 768) (hi : Protected i) (h670 : i≠670) :
    (scatterResult a regs n js).stacks i=a.stacks i := by
  apply returned_frame scatterRegs (by decide) scatterInputs scatterOutputs a _ i hi
  intro p hp
  simp only [scatterOutputs,List.mem_singleton] at hp
  subst p
  exact h670

def support : Code := .seq trueCount scatterSupport

theorem support_eval (a : Data) (n : ℕ) (js : List ℕ)
    (hi : a.stacks 650=HeadScatterProgram.indices js)
    (hc : (a.stacks 651).length=js.length)
    (hn : a.stacks 128=List.replicate n true) (hb : ∀ j∈js,j < n) :
    ∃ regs t,t ≤ countCost a+scatterCost (countResult a) regs n js ∧
      Eval support t a (scatterResult (countResult a) regs n js) := by
  have h1 := trueCount_eval a
  obtain ⟨regs,t,ht,h2⟩ := scatterSupport_eval (countResult a) n js
    ((countResult_frame a 650 (by decide) (by decide)).trans hi)
    (by rw [countResult_value,hc])
    ((countResult_frame a 128 (by decide) (by decide)).trans hn) hb
  exact ⟨regs,_,Nat.add_le_add_left ht _,h1.seq h2⟩

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
