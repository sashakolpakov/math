import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyTable

namespace OAI.Algorithms

/-! Relational native table traversal. Each executed iteration supplies its
own payload witness; no byte family uniform over initial registers is assumed. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Space for one framed original-variable ID and one bounded payload. -/
def literalRecordBound (n L : ℕ) : ℕ := 2*n+2*L+4

/-- The payload is existential after the actual incoming registers, not before
all executions. The accumulator bound is the complete table's size bound. -/
def RelLiteralBody (s : OuterStore) (body : OuterCode)
    (P : ℕ → List Bool → Prop) (K n L : ℕ) : Prop :=
  ∀ j, j < n → ∀ acc, acc.length ≤ n*literalRecordBound n L →
    ∀ regs : Fin 16 → Bool, ∃ bits k rf,
      k ≤ K ∧ bits.length ≤ L ∧ P j bits ∧
      Eval body k (⟨regs,literalReady s (List.replicate j true) acc⟩ : OuterData)
        (⟨rf,literalReady s (List.replicate j true)
          (Encoding.frame (Encoding.encodeNat j)++Encoding.frame bits++acc)⟩ : OuterData)

theorem literalRecord_length_le (n L j : ℕ) (hj : j < n)
    (bits : List Bool) (hb : bits.length ≤ L) :
    (Encoding.frame (Encoding.encodeNat j)++Encoding.frame bits).length ≤
      literalRecordBound n L := by
  simp only [List.length_append,Encoding.length_frame,Encoding.encodeNat,
    List.length_replicate,List.length_singleton,literalRecordBound]
  omega

theorem rel_tableResult_congr (f g : ℕ → List Bool) (j : ℕ)
    (h : ∀ i,i < j → f i=g i) (acc : List Bool) :
    tableResult f j acc=tableResult g j acc := by
  induction j generalizing acc with
  | zero => rfl
  | succ j ih =>
      have he : tableRecord f j=tableRecord g j := by
        simp only [tableRecord,h j (by omega)]
      simp only [tableResult,he]
      exact ih (fun i hi=>h i (by omega)) _

theorem rel_tableResult_length_le (f : ℕ → List Bool) (n L j : ℕ)
    (hj : j ≤ n) (h : ∀ i,i < j → (f i).length ≤ L) (acc : List Bool) :
    (tableResult f j acc).length ≤ acc.length+j*literalRecordBound n L := by
  induction j generalizing acc with
  | zero => simp [tableResult]
  | succ j ih =>
      have hr := literalRecord_length_le n L j (by omega) (f j) (h j (by omega))
      have ht := ih (by omega) (fun i hi=>h i (by omega)) (tableRecord f j++acc)
      change (tableRecord f j).length ≤ literalRecordBound n L at hr
      simp only [tableResult,List.length_append] at ht ⊢
      nlinarith

/-- Every witness is chosen along this actual run. The capacity invariant
reserves room for all remaining records before invoking the bounded body. -/
theorem literalLoop_rel_visits (s : OuterStore) (body : OuterCode)
    (P : ℕ → List Bool → Prop) (K n L : ℕ)
    (hbody : RelLiteralBody s body P K n L)
    (j : ℕ) (hj : j ≤ n) (acc : List Bool)
    (hcap : acc.length+j*literalRecordBound n L ≤ n*literalRecordBound n L)
    (regs : Fin 16 → Bool) :
    ∃ payload costs k rf,
      (∀ i,i < j → (payload i).length ≤ L ∧ P i (payload i)) ∧
      k ≤ j*(K+2)+2 ∧
      UnaryForPrograms.Visits literalPorts body costs k
        (⟨regs,literalReady s (List.replicate j true) acc⟩ : OuterData)
        (⟨rf,literalReady s [] (tableResult payload j acc)⟩ : OuterData) := by
  induction j generalizing acc regs with
  | zero =>
      refine ⟨fun _=>[],[],2,readRegs regs 0 1 none,?_,by simp,?_⟩
      · intro i hi; omega
      · simpa [literalPopped,tableResult] using
          UnaryForPrograms.Visits.done (p:=literalPorts) (body:=body)
            (⟨regs,literalReady s [] acc⟩ : OuterData) (by simp [literalReady,literalPorts])
  | succ j ih =>
      have hac : acc.length ≤ n*literalRecordBound n L := by nlinarith
      obtain ⟨bits,kb,rb,hkb,hbits,hP,hbe⟩ :=
        hbody j (by omega) acc hac (readRegs regs 0 1 (some true))
      let next := Encoding.frame (Encoding.encodeNat j)++Encoding.frame bits++acc
      have hr := literalRecord_length_le n L j (by omega) bits hbits
      have hn : next.length ≤ literalRecordBound n L+acc.length := by
        simpa only [next,List.length_append] using Nat.add_le_add_right hr acc.length
      have hnext : next.length+j*literalRecordBound n L ≤ n*literalRecordBound n L := by
        nlinarith
      obtain ⟨f,costs,kt,rt,hf,hkt,ht⟩ := ih (by omega) next hnext rb
      let payload := Function.update f j bits
      have hp : ∀ i,i < j+1 → (payload i).length ≤ L ∧ P i (payload i) := by
        intro i hi
        by_cases he : i=j
        · subst i; simpa [payload] using And.intro hbits hP
        · simpa [payload,he] using hf i (by omega)
      have htable : tableResult payload (j+1) acc=tableResult f j next := by
        change tableResult payload j (tableRecord payload j++acc)=_
        have he : tableRecord payload j++acc=next := by
          simp [payload,tableRecord,next,List.append_assoc]
        rw [he]
        apply rel_tableResult_congr
        intro i hi
        simp [payload,show i≠j by omega]
      refine ⟨payload,kb::costs,kb+kt+2,rt,hp,?_,?_⟩
      · nlinarith
      · rw [htable]
        apply UnaryForPrograms.Visits.step (p:=literalPorts) (body:=body)
          (d:=(⟨regs,literalReady s (List.replicate (j+1) true) acc⟩ : OuterData))
          (by simp [literalReady,literalPorts])
          (by simpa only [literalPopped,List.replicate_succ,List.head?_cons,List.tail_cons,next] using hbe)
          (by simp [literalReady,literalPorts,UnaryForPrograms.popped,List.replicate_succ]) ht

/-- Relational counted loop with an explicit actual-register execution. -/
theorem literalLoop_rel_run (s : OuterStore) (body : OuterCode)
    (P : ℕ → List Bool → Prop) (K n L : ℕ)
    (hbody : RelLiteralBody s body P K n L)
    (j : ℕ) (hj : j ≤ n) (acc : List Bool)
    (hcap : acc.length+j*literalRecordBound n L ≤ n*literalRecordBound n L)
    (regs : Fin 16 → Bool) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ i,i < j → (payload i).length ≤ L ∧ P i (payload i)) ∧
      k ≤ j*(K+2)+2 ∧
      Eval (UnaryForPrograms.forCmd literalPorts body) k
        (⟨regs,literalReady s (List.replicate j true) acc⟩ : OuterData)
        (⟨rf,literalReady s [] (tableResult payload j acc)⟩ : OuterData) := by
  obtain ⟨payload,costs,k,rf,hp,hk,hv⟩ :=
    literalLoop_rel_visits s body P K n L hbody j hj acc hcap regs
  exact ⟨payload,k,rf,hp,hk,hv.eval⟩

/-- Full native table producer with actual-run witnesses, measured master copy,
loop, and output move. No payload family uniform over registers is required. -/
theorem prepareFactor_rel_run (s : OuterStore) (source : OuterCode)
    (P : ℕ → List Bool → Prop) (K n L : ℕ)
    (hn : s 552=List.replicate n true)
    (h460 : s 460=[]) (h573 : s 573=[]) (h569 : s 569=[])
    (h561 : s 561=[]) (h585 : s 585=[])
    (hbody : RelLiteralBody s (literalIteration source) P K n L)
    (regs : Fin 16 → Bool) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ j,j < n → (payload j).length ≤ L ∧ P j (payload j)) ∧
      k ≤ 7*n+n*(K+2)+6*n*literalRecordBound n L+15 ∧
      Eval (prepareFactor source) k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update s 561 (tableResult payload n [])⟩ : OuterData) := by
  let a := literalReady s (List.replicate n true) []
  have hc : ExecutesOuter (liftInner (copy 212 233)) (7*n+6) s a := by
    have h := liftInner_update_run s (copy 212 233) (7*n+5) 233 (List.replicate n true) (by
      simpa [projectInner,Function.comp_def,innerPort,hn,h573] using
        copy_run 212 233 (projectInner s) (by decide) (by decide) (by decide)
          (by simpa [projectInner,Function.comp_def,innerPort] using h460))
    have heq : Function.update s (innerPort 233) (List.replicate n true)=a := by
      funext i
      by_cases hi : i=569 <;> simp [a,literalReady,Function.update_apply,innerPort,hi,h569]
    simpa [heq] using h
  obtain ⟨kc,rc,hkc,hec⟩ := hc regs
  obtain ⟨payload,kl,rl,hp,hkl,hel⟩ :=
    literalLoop_rel_run s (literalIteration source) P K n L hbody n (by omega) [] (by simp) rc
  let b := literalReady s [] (tableResult payload n [])
  have hm : ExecutesOuter (liftInner (SubexpPolynomialConstructor.move 229 221))
      (6*(tableResult payload n []).length+7) b
      (Function.update s 561 (tableResult payload n [])) := by
    have h := liftInner_run b (SubexpPolynomialConstructor.move 229 221)
      (6*(tableResult payload n []).length+6)
      (Function.update (Function.update (projectInner b) 229 []) 221 (tableResult payload n [])) (by
        simpa [projectInner,Function.comp_def,innerPort,b,literalReady] using
          SubexpPolynomialConstructor.move_run (projectInner b) 229 221
            (by decide) (by decide) (by decide)
            (by simp [projectInner,innerPort,b,literalReady,h585])
            (by simp [projectInner,innerPort,b,literalReady,h561]))
    rw [replaceInner_update,replaceInner_update,replaceInner_project] at h
    convert h using 1
    funext i
    by_cases h561' : i=561
    · subst i; simp [innerPort]
    by_cases h569' : i=569
    · subst i; simp [innerPort,h569]
    by_cases h573' : i=573
    · subst i; simp [innerPort,b,literalReady,h573]
    simp [innerPort,b,literalReady,h561',h569',h573']
  obtain ⟨km,rm,hkm,hem⟩ := hm rl
  have hlen := rel_tableResult_length_le payload n L n (by omega) (fun i hi=>(hp i hi).1) []
  simp only [List.length_nil,Nat.zero_add] at hlen
  refine ⟨payload,kc+(kl+km),rm,hp,?_,hec.seq (hel.seq hem)⟩
  nlinarith

/-- Exact lookup-table serialization of the actual relational output. -/
theorem prepareFactor_rel_lookup (s : OuterStore) (source : OuterCode)
    (P : ℕ → List Bool → Prop) (K n L : ℕ)
    (hn : s 552=List.replicate n true)
    (h460 : s 460=[]) (h573 : s 573=[]) (h569 : s 569=[])
    (h561 : s 561=[]) (h585 : s 585=[])
    (hbody : RelLiteralBody s (literalIteration source) P K n L)
    (regs : Fin 16 → Bool) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ j,j < n → (payload j).length ≤ L ∧ P j (payload j)) ∧
      k ≤ 7*n+n*(K+2)+6*n*literalRecordBound n L+15 ∧
      Eval (prepareFactor source) k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update s 561 (Squarefree.Program.lookupRecords
          (HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n)=>payload v.val) ()))⟩ : OuterData) := by
  simpa only [tableResult_incidence] using
    prepareFactor_rel_run s source P K n L hn h460 h573 h569 h561 h585 hbody regs

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
