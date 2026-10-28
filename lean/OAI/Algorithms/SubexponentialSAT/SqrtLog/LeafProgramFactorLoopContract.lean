import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopAssignment
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopSemantics

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing MomentsProgram
open IdempotentApplyProgram.Bounds MomentsAssembly

/-- Pure readiness of the supplied machine state, not an execution oracle. -/
structure AssignmentReady {n B d : ℕ} (u J : ℕ)
    (ready : (Fin 768 → List Bool) → Prop) (eligible : ℕ → Prop) (T : ℕ)
    (ids : List ℕ) (one : Raw n B d) (a : Factor.Data) : Prop where
  setup : LeafAssignmentSetupProgram.BeforeReady a
  engine : ready (LeafAssignmentSetupProgram.prepared a (fun _ => false) (fun _ => false)).stacks
  ids_good : ∀ id ∈ ids, eligible id
  ids_length : (ProgramEncoding.encodeRecords (records ids)).length ≤ T
  ids_tape : a.stacks 175=ProgramEncoding.encodeRecords (records ids)
  one_tape : a.stacks 69=Product.bytes one
  empty : ∀ i ∈ ([41,44,67,149,150,151,159] : List (Fin 768)), a.stacks i=[]
  assignment_length : (a.stacks 174).length ≤ n

def uniformAssignmentBudget (n B d u J T C : ℕ) : ℕ :=
  (C+17)*(T+1)+7*T+46*byteBound n B d u J+63*n+13*(d*B)+114

theorem assignmentBudget_le (n B d u J T C : ℕ) (ids : List ℕ)
    (h : (ProgramEncoding.encodeRecords (records ids)).length ≤ T) :
    assignmentBudget n B d u J C ids n (d*B) ≤ uniformAssignmentBudget n B d u J T C := by
  have hl := loopBudget_le C ids
  have hm := Nat.mul_le_mul_left (C+17) (Nat.add_le_add_right h 1)
  dsimp [assignmentBudget,commandBudget,uniformAssignmentBudget]
  omega

def assignmentRelation {n B d : ℕ}
    (step : AssignmentContext → List Bool → Raw n B d → ℕ → Raw n B d → Prop)
    (ids : AssignmentContext → List Bool → List ℕ) (one : Raw n B d)
    (weight : AssignmentContext → List Bool → RingProgram.Code (Word B) d)
    (c : AssignmentContext) (x : List Bool) (value : Contribution n B d) : Prop :=
  value.1=weight c x ∧ RunRel (step c x) (ids c x) one value.2

theorem assignmentTapes_machine {n B d : ℕ} (e : Product.Store)
    (left seed out : Raw n B d) (weight : RingProgram.Code (Word B) d)
    (high : Fin 768 → List Bool) (regs rr : Fin 40 → Bool)
    (hweight : LeafAssignmentSetupProgram.weight (machine regs (Product.working e left [] seed) high)=
      RingProgram.flat weight) :
    (⟨rr,assignmentTapes (machine regs (Product.working e left [] seed) high) (Product.bytes out)⟩ : Factor.Data)=
      machine rr (weightedStore e (Product.bytes left) (Product.bytes seed) (Product.bytes out)
        (RingProgram.flat weight)) (Function.update high 174 []) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    simp only [assignmentTapes,hweight]
    by_cases hi : i.val < 56
    · have h174 : i≠174 := by intro h; subst i; norm_num at hi
      have hcore : Product.tapes (weightedStore e (Product.bytes left) (Product.bytes seed)
          (Product.bytes out) (RingProgram.flat weight)) =
          Function.update (Function.update (Product.tapes (Product.working e left [] seed))
            41 (Product.bytes out)) 44 (RingProgram.flat weight) := by
        funext j
        fin_cases j <;> simp [Product.working,weightedStore,Product.tapes,
          Product.bytes,Normalize.bytes,Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary]
      have hh := (congrFun hcore (⟨i.val,hi⟩ : Fin 56)).symm
      have hi174 : i.val ≠ 174 := by omega
      simpa only [machine,hi,dite_true,Function.update_apply,Fin.ext_iff,Fin.coe_ofNat_eq_mod,
        Nat.reduceMod,hi174,ite_false] using hh
    · have h41 : i≠41 := by intro h; subst i; norm_num at hi
      have h44 : i≠44 := by intro h; subst i; norm_num at hi
      simp [machine,hi,Function.update_apply,h41,h44]

/-- The concrete Factor.assignment is a legal relational moment producer once
its concrete per-ID callback and physical input readiness have been supplied. -/
theorem assignment_contract (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (u J T C : ℕ)
    (one : Raw n (baseWidth p t) d) (hone : Good Finset.univ u J one)
    (step : AssignmentContext → List Bool → Raw n (baseWidth p t) d → ℕ → Raw n (baseWidth p t) d → Prop)
    (ready : AssignmentContext → List Bool → (Fin 768 → List Bool) → Prop)
    (eligible : AssignmentContext → List Bool → ℕ → Prop)
    (ids : AssignmentContext → List Bool → List ℕ)
    (weight : AssignmentContext → List Bool → RingProgram.Code (Word (baseWidth p t)) d)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (callbacks : ∀ c x, CallbackContract u J (step c x) (ready c x) (eligible c x) T C)
    (inputs : ∀ c x (left seed : Raw n (baseWidth p t) d) high regs,
      EntryInvariant Finset.univ u J left → EntryInvariant Finset.univ u J seed →
      validFrame high → c.Matches high → high 174=x →
      AssignmentReady u J (ready c x) (eligible c x) T (ids c x) one
        (machine regs (Product.working (Product.environment p t M cache table degree width u J) left [] seed) high))
    (weights : ∀ c x (left seed : Raw n (baseWidth p t) d) high regs,
      validFrame high → c.Matches high → high 174=x →
      LeafAssignmentSetupProgram.weight
        (machine regs (Product.working (Product.environment p t M cache table degree width u J) left [] seed) high)=
          RingProgram.flat (weight c x)) :
    MomentsAssembly.Relational.AssignmentContract p t M cache table u J
      (assignmentRelation step ids one weight) Factor.assignment degree width Finset.univ validFrame
      (uniformAssignmentBudget n (baseWidth p t) d u J T C) := by
  intro c x left seed high regs hl hs hv hc hx
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let a := machine regs (Product.working e left [] seed) high
  have hi := inputs c x left seed high regs hl hs hv hc hx
  have hw := weights c x left seed high regs hv hc hx
  have hbl := bytes_le_capacity Finset.univ u J left hl
  have hbs := bytes_le_capacity Finset.univ u J seed hs
  obtain ⟨out,ho,hr,k,hk,rr,he⟩ := assignment_eval u J (step c x) (ready c x) (eligible c x) T C
    (callbacks c x) a hi.setup hi.engine (ids c x) one hone hi.ids_good hi.ids_length hi.ids_tape hi.one_tape
    (hi.empty 41 (by simp)) (hi.empty 44 (by simp)) (hi.empty 67 (by simp))
    (hi.empty 149 (by simp)) (hi.empty 150 (by simp)) (hi.empty 151 (by simp)) (hi.empty 159 (by simp))
    n (d*baseWidth p t)
    (by simpa [a,machine,Product.working,Product.tapes,byteBound] using hbl)
    (by simpa [a,machine,Product.working,Product.tapes,byteBound] using hbs)
    hi.assignment_length (by rw [hw]; simp)
  refine ⟨(weight c x,out),⟨rfl,hr⟩,ho,k,hk.trans (assignmentBudget_le n (baseWidth p t) d u J T C _ hi.ids_length),rr,?_⟩
  rw [assignmentTapes_machine e left seed out (weight c x) high regs rr hw] at he
  exact he
end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop

end OAI.Algorithms
