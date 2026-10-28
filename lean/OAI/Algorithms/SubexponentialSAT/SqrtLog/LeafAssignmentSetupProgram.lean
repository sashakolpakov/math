import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgramBase

namespace OAI.Algorithms

/-! Actual before/after adapters surrounding the assignment jet engine. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
open SubexponentialSAT BitProgram StructuredCalls

def saved (a : Data) : Data := moved (moved a 40 146) 42 147

def beforeCommand : Code :=
  .seq (move 40 146) (.seq (move 42 147) (.seq mergeCommand weightCommand))

def merged (a : Data) (rf : Fin 8 → Bool) : Data :=
  serviceResult (saved a) mergePorts rf
    (LeafAssignmentMergeProgram.merge (a.stacks 174) (a.stacks 178) (a.stacks 177))

def weight (a : Data) : List Bool := LeafWeightProgram.Native.result
  (a.stacks 174) (a.stacks 168) (a.stacks 178) (a.stacks 190) (a.stacks 207)

def prepared (a : Data) (rm rw : Fin 8 → Bool) : Data :=
  serviceResult (merged a rm) weightPorts rw (weight a)

def beforeCost (a : Data) : ℕ :=
  6*((a.stacks 40).length+(a.stacks 42).length)+
    59*(a.stacks 174).length+7*(weight a).length+60

def BeforeReady (a : Data) : Prop :=
  (∀i∈([145,146,147,148,340,341,342,343,359] : List (Fin 768)),a.stacks i=[]) ∧
  (a.stacks 174).length=(a.stacks 178).length ∧
  (a.stacks 174).length=(a.stacks 177).length ∧
  (a.stacks 174).length=(a.stacks 168).length

theorem before_eval (a : Data) (ha : BeforeReady a) :
    ∃rm rw, Eval beforeCommand (beforeCost a) a (prepared a rm rw) := by
  rcases ha with ⟨he,hh,hb,hs⟩
  have e1 := move_eval a 40 146 (by decide) (by decide) (by decide)
    (he 359 (by simp)) (he 146 (by simp))
  have e2 := move_eval (moved a 40 146) 42 147 (by decide) (by decide) (by decide)
    (by simpa [moved] using he 359 (by simp))
    (by simpa [moved] using he 147 (by simp))
  obtain ⟨rm,e3⟩ := merge_eval (saved a)
    (by intro i hi
        have h : i=340 ∨ i=341 ∨ i=342 ∨ i=343 := by simpa [scratch] using hi
        have hei : a.stacks i=[] := he i (by rcases h with h|h|h|h <;> simp [h])
        rcases h with rfl|rfl|rfl|rfl <;> simpa [saved,moved] using hei)
    (by simpa [saved,moved] using he 145 (by simp))
    (by simpa [saved,moved] using hh) (by simpa [saved,moved] using hb)
  have e3' : Eval mergeCommand (30*(a.stacks 174).length+22) (saved a) (merged a rm) := by
    simpa [merged,saved,moved] using e3
  obtain ⟨rw,e4⟩ := weight_eval (merged a rm)
    (by intro i hi
        have h : i=340 ∨ i=341 ∨ i=342 ∨ i=343 := by simpa [scratch] using hi
        have hei : a.stacks i=[] := he i (by rcases h with h|h|h|h <;> simp [h])
        rcases h with rfl|rfl|rfl|rfl <;>
          simpa [merged,serviceResult,mergePorts,saved,moved] using hei)
    (by simpa [merged,serviceResult,mergePorts,saved,moved] using he 148 (by simp))
    (by simpa [merged,serviceResult,mergePorts,saved,moved] using hs)
    (by simpa [merged,serviceResult,mergePorts,saved,moved] using hh)
  have e4' : Eval weightCommand (29*(a.stacks 174).length+7*(weight a).length+26)
      (merged a rm) (prepared a rm rw) := by
    simpa [prepared,weight,merged,serviceResult,mergePorts,saved,moved] using e4
  refine ⟨rm,rw,?_⟩
  have hx := e1.seq (e2.seq (e3'.seq e4'))
  change Eval beforeCommand _ a (prepared a rm rw) at hx
  convert hx using 1 ; simp [beforeCost,moved,Nat.mul_add] ; omega

theorem prepared_stacks (a : Data) (rm rw : Fin 8 → Bool) :
    (prepared a rm rw).stacks =
      Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update a.stacks 40 []) 42 []) 146 (a.stacks 40))
          147 (a.stacks 42)) 145
          (LeafAssignmentMergeProgram.merge (a.stacks 174) (a.stacks 178) (a.stacks 177)))
            148 (weight a) := by
  funext i
  by_cases h40 : i=40
  · subst i; simp [prepared,merged,serviceResult,weightPorts,mergePorts,saved,moved]
  by_cases h42 : i=42
  · subst i; simp [prepared,merged,serviceResult,weightPorts,mergePorts,saved,moved]
  by_cases h145 : i=145
  · subst i; simp [prepared,merged,serviceResult,weightPorts,mergePorts,saved,moved]
  by_cases h146 : i=146
  · subst i; simp [prepared,merged,serviceResult,weightPorts,mergePorts,saved,moved]
  by_cases h147 : i=147
  · subst i; simp [prepared,merged,serviceResult,weightPorts,mergePorts,saved,moved]
  by_cases h148 : i=148
  · subst i; simp [prepared,merged,serviceResult,weightPorts,mergePorts,saved,moved]
  simp [prepared,merged,serviceResult,weightPorts,mergePorts,saved,moved,
    h40,h42,h145,h146,h147,h148]

/-- The engine is allowed to leave temporary contents at40 and42; those are
paid-cleared before the saved head dictionaries are restored. -/
def restoreStart (a : Data) : Data := cleared (cleared a 40) 42

def afterCommand : Code :=
  .seq (clear 40) (.seq (clear 42) (.seq (move 67 41) (.seq (move 146 40)
    (.seq (move 147 42) (.seq (move 148 44) (.seq (clear 145) (clear 174)))))))

def finished (a : Data) : Data :=
  cleared (cleared (moved (moved (moved (moved (restoreStart a) 67 41) 146 40)
    147 42) 148 44) 145) 174

def afterCost (a : Data) : ℕ :=
  2*((a.stacks 40).length+(a.stacks 42).length)+
  6*((a.stacks 67).length+(a.stacks 146).length+(a.stacks 147).length+(a.stacks 148).length)+
  2*((a.stacks 145).length+(a.stacks 174).length)+36

theorem after_eval (a : Data) (h41 : a.stacks 41=[]) (h44 : a.stacks 44=[])
    (ht : a.stacks 359=[]) : Eval afterCommand (afterCost a) a (finished a) := by
  have e1 := clear_eval a 40
  have e2 := clear_eval (cleared a 40) 42
  have e3 := move_eval (restoreStart a) 67 41 (by decide) (by decide) (by decide)
    (by simpa [restoreStart,cleared] using ht)
    (by simpa [restoreStart,cleared] using h41)
  have e4 := move_eval (moved (restoreStart a) 67 41) 146 40
    (by decide) (by decide) (by decide)
    (by simpa [moved,restoreStart,cleared] using ht) (by simp [moved,restoreStart,cleared])
  have e5 := move_eval (moved (moved (restoreStart a) 67 41) 146 40) 147 42
    (by decide) (by decide) (by decide)
    (by simpa [moved,restoreStart,cleared] using ht) (by simp [moved,restoreStart,cleared])
  have e6 := move_eval (moved (moved (moved (restoreStart a) 67 41) 146 40) 147 42) 148 44
    (by decide) (by decide) (by decide)
    (by simpa [moved,restoreStart,cleared] using ht)
    (by simpa [moved,restoreStart,cleared] using h44)
  have e7 := clear_eval
    (moved (moved (moved (moved (restoreStart a) 67 41) 146 40) 147 42) 148 44) 145
  have e8 := clear_eval
    (cleared (moved (moved (moved (moved (restoreStart a) 67 41) 146 40) 147 42) 148 44) 145) 174
  have hx := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))
  change Eval afterCommand _ a (finished a) at hx
  convert hx using 1 ; simp [afterCost,restoreStart,moved,cleared,Nat.mul_add] ; omega

theorem finished_stacks (a : Data) : (finished a).stacks =
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update a.stacks 67 []) 146 []) 147 []) 148 [])
        145 []) 174 []) 41 (a.stacks 67)) 40 (a.stacks 146)) 42 (a.stacks 147))
        44 (a.stacks 148) := by
  funext i
  by_cases h40 : i=40
  · subst i; simp [finished,restoreStart,cleared,moved]
  by_cases h41 : i=41
  · subst i; simp [finished,restoreStart,cleared,moved]
  by_cases h42 : i=42
  · subst i; simp [finished,restoreStart,cleared,moved]
  by_cases h44 : i=44
  · subst i; simp [finished,restoreStart,cleared,moved]
  by_cases h67 : i=67
  · subst i; simp [finished,restoreStart,cleared,moved]
  by_cases h145 : i=145
  · subst i; simp [finished,restoreStart,cleared,moved]
  by_cases h146 : i=146
  · subst i; simp [finished,restoreStart,cleared,moved]
  by_cases h147 : i=147
  · subst i; simp [finished,restoreStart,cleared,moved]
  by_cases h148 : i=148
  · subst i; simp [finished,restoreStart,cleared,moved]
  by_cases h174 : i=174
  · subst i; simp [finished,restoreStart,cleared,moved]
  simp [finished,restoreStart,cleared,moved,h40,h41,h42,h44,h67,h145,h146,h147,h148,h174]

theorem prepared_register_frame (a : Data) (rm rw : Fin 8 → Bool)
    (i : Fin 40) (hi : 8 ≤ i.val) : (prepared a rm rw).regs i=a.regs i := by
  have hn : ¬∃j,register j=i := by
    rintro ⟨j,hj⟩
    have h := congrArg Fin.val hj
    simp [register] at h
    omega
  simp only [prepared,serviceResult]
  rw [embedState_register_frame _ _ _ _ i hn]
  simp only [merged,serviceResult]
  rw [embedState_register_frame _ _ _ _ i hn]
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  simp [saved,moved,readRegs,h0,h1]

theorem finished_register_frame (a : Data) (i : Fin 40) (hi : 2 ≤ i.val) :
    (finished a).regs i=a.regs i := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  simp [finished,restoreStart,cleared,moved,readRegs,h0,h1]

/-- Exact frame outside the six preparation destinations. -/
theorem prepared_stack_frame (a : Data) (rm rw : Fin 8 → Bool) (i : Fin 768)
    (hi : i ∉ ([40,42,145,146,147,148] : List (Fin 768))) :
    (prepared a rm rw).stacks i=a.stacks i := by
  rw [prepared_stacks]
  simp only [List.mem_cons,not_or] at hi
  rcases hi with ⟨h40,h42,h145,h146,h147,h148⟩
  simp [h40,h42,h145,h146,h147,h148]

theorem finished_stack_frame (a : Data) (i : Fin 768)
    (hi : i ∉ ([40,41,42,44,67,145,146,147,148,174] : List (Fin 768))) :
    (finished a).stacks i=a.stacks i := by
  rw [finished_stacks]
  simp only [List.mem_cons,not_or] at hi
  rcases hi with ⟨h40,h41,h42,h44,h67,h145,h146,h147,h148,h174⟩
  simp [h40,h41,h42,h44,h67,h145,h146,h147,h148,h174]

theorem beforeCost_le (a : Data) (L n W : ℕ)
    (h40 : (a.stacks 40).length ≤ L) (h42 : (a.stacks 42).length ≤ L)
    (ha : (a.stacks 174).length ≤ n) (hw : (weight a).length ≤ W) :
    beforeCost a ≤ 12*L+59*n+7*W+60 := by
  unfold beforeCost
  omega

theorem afterCost_idle (a : Data) (h40 : a.stacks 40=[]) (h42 : a.stacks 42=[]) :
    afterCost a =
      6*((a.stacks 67).length+(a.stacks 146).length+(a.stacks 147).length+(a.stacks 148).length)+
      2*((a.stacks 145).length+(a.stacks 174).length)+36 := by
  simp [afterCost,h40,h42]

/-- Uniform byte bound supplied to the enclosing assignment producer. -/
theorem afterCost_le (a : Data) (L n W : ℕ)
    (h40 : a.stacks 40=[]) (h42 : a.stacks 42=[])
    (h67 : (a.stacks 67).length ≤ L) (h146 : (a.stacks 146).length ≤ L)
    (h147 : (a.stacks 147).length ≤ L) (h148 : (a.stacks 148).length ≤ W)
    (h145 : (a.stacks 145).length ≤ n) (h174 : (a.stacks 174).length ≤ n) :
    afterCost a ≤ 18*L+6*W+4*n+36 := by
  rw [afterCost_idle a h40 h42]
  omega

end SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram

end

end OAI.Algorithms
