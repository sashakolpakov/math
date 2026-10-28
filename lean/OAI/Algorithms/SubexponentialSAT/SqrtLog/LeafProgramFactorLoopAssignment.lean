import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopCommand

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram
open IdempotentApplyProgram.Bounds

noncomputable def afterEngine (a : Factor.Data) (rm rw : Fin 8 → Bool) (rr : Fin 40 → Bool)
    (bits : List Bool) : Factor.Data :=
  ⟨rr,Function.update (LeafAssignmentSetupProgram.prepared a rm rw).stacks 67 bits⟩

def assignmentTapes (a : Factor.Data) (bits : List Bool) : Fin 768 → List Bool :=
  Function.update (Function.update (Function.update a.stacks 174 []) 41 bits) 44 (LeafAssignmentSetupProgram.weight a)

theorem finished_afterEngine (a : Factor.Data) (rm rw : Fin 8 → Bool) (rr : Fin 40 → Bool)
    (bits : List Bool) (ha : LeafAssignmentSetupProgram.BeforeReady a) (h67 : a.stacks 67=[]) :
    (LeafAssignmentSetupProgram.finished (afterEngine a rm rw rr bits)).stacks = assignmentTapes a bits := by
  rw [LeafAssignmentSetupProgram.finished_stacks]
  simp only [afterEngine,LeafAssignmentSetupProgram.prepared_stacks,assignmentTapes]
  have h145 := ha.1 145 (by simp)
  have h146 := ha.1 146 (by simp)
  have h147 := ha.1 147 (by simp)
  have h148 := ha.1 148 (by simp)
  funext i
  by_cases hi : i ∈ ([40,41,42,44,67,145,146,147,148,174] : List (Fin 768))
  · simp at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [h67,h145,h146,h147,h148]
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    rcases hi with ⟨h40,h41,h42,h44,h67',h145',h146',h147',h148',h174⟩
    simp [h40,h41,h42,h44,h67',h145',h146',h147',h148',h174]

def assignmentBudget (n B d u J C : ℕ) (ids : List ℕ) (N W : ℕ) : ℕ :=
  commandBudget n B d u J C ids+30*byteBound n B d u J+63*N+13*W+96

theorem assignment_eval {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 768 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : CallbackContract u J step ready eligible T C)
    (a : Factor.Data) (ha : LeafAssignmentSetupProgram.BeforeReady a)
    (hr : ready (LeafAssignmentSetupProgram.prepared a (fun _ => false) (fun _ => false)).stacks)
    (ids : List ℕ) (one : Raw n B d) (hg : Good Finset.univ u J one)
    (hids : ∀ id ∈ ids, eligible id) (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T)
    (h175 : a.stacks 175=ProgramEncoding.encodeRecords (records ids)) (h69 : a.stacks 69=Product.bytes one)
    (h41 : a.stacks 41=[]) (h44 : a.stacks 44=[]) (h67 : a.stacks 67=[])
    (h149 : a.stacks 149=[]) (h150 : a.stacks 150=[]) (h151 : a.stacks 151=[])
    (h159 : a.stacks 159=[]) (N W : ℕ)
    (h40 : (a.stacks 40).length ≤ byteBound n B d u J)
    (h42 : (a.stacks 42).length ≤ byteBound n B d u J)
    (hN : (a.stacks 174).length ≤ N) (hW : (LeafAssignmentSetupProgram.weight a).length ≤ W) :
    ∃ out, Good Finset.univ u J out ∧ RunRel step ids one out ∧
      ∃ k ≤ assignmentBudget n B d u J C ids N W, ∃ rr,
        Eval Factor.assignment k a ⟨rr,assignmentTapes a (Product.bytes out)⟩ := by
  obtain ⟨rm,rw,hbefore⟩ := LeafAssignmentSetupProgram.before_eval a ha
  let prepared := LeafAssignmentSetupProgram.prepared a rm rw
  have hready : ready prepared.stacks := by
    simpa only [prepared,LeafAssignmentSetupProgram.prepared_stacks] using hr
  obtain ⟨out,ho,hrel,k,hk,rr,hcommand⟩ := command_eval u J step ready eligible T C contract
    prepared hready ids one hg hids hlen
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h175)
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h69)
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h149)
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h150)
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h151)
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h67)
    (by simpa [prepared,LeafAssignmentSetupProgram.prepared_stacks] using h159)
  let engine := afterEngine a rm rw rr (Product.bytes out)
  have he41 : engine.stacks 41=[] := by simp [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks,h41]
  have he44 : engine.stacks 44=[] := by simp [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks,h44]
  have he359 : engine.stacks 359=[] := by
    simpa [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks] using ha.1 359 (by simp)
  have hafter := LeafAssignmentSetupProgram.after_eval engine he41 he44 he359
  have hb := LeafAssignmentSetupProgram.beforeCost_le a (byteBound n B d u J) N W h40 h42 hN hW
  have hoB := bytes_le_capacity Finset.univ u J out ho
  have hc := LeafAssignmentSetupProgram.afterCost_le engine (byteBound n B d u J) N W
    (by simp [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks])
    (by simp [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks])
    (by simpa [engine,afterEngine,byteBound] using hoB)
    (by simpa [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks] using h40)
    (by simpa [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks] using h42)
    (by simpa [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks] using hW)
    (by simpa [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks] using hN)
    (by simpa [engine,afterEngine,LeafAssignmentSetupProgram.prepared_stacks] using hN)
  have hout : LeafAssignmentSetupProgram.finished engine = ⟨(LeafAssignmentSetupProgram.finished engine).regs,assignmentTapes a (Product.bytes out)⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · exact finished_afterEngine a rm rw rr (Product.bytes out) ha h67
  rw [hout] at hafter
  refine ⟨out,ho,hrel,LeafAssignmentSetupProgram.beforeCost a+(k+LeafAssignmentSetupProgram.afterCost engine),?_,
    (LeafAssignmentSetupProgram.finished engine).regs,?_⟩
  · dsimp [assignmentBudget]; omega
  · exact hbefore.seq (hcommand.seq hafter)
end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop

end OAI.Algorithms
