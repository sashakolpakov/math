import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyPreparation

namespace OAI.Algorithms

/-! Relocation and the finite total-variable table traversal. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev OuterStore := Fin 768 → List Bool
abbrev OuterData := State 16 768

def ExecutesOuter (code : OuterCode) (K : ℕ) (before after : OuterStore) : Prop :=
  ∀ regs : Fin 16 → Bool, ∃ k rf, k ≤ K ∧
    Eval code k (⟨regs,before⟩ : OuterData) (⟨rf,after⟩ : OuterData)

theorem ExecutesOuter.seq {a b : OuterCode} {Ka Kb : ℕ} {s u v : OuterStore}
    (ha : ExecutesOuter a Ka s u) (hb : ExecutesOuter b Kb u v) :
    ExecutesOuter (.seq a b) (Ka+Kb) s v := by
  intro regs
  obtain ⟨na,ra,hna,hea⟩ := ha regs
  obtain ⟨nb,rb,hnb,heb⟩ := hb ra
  exact ⟨na+nb,rb,by omega,hea.seq heb⟩

theorem ExecutesOuter.mono {a : OuterCode} {Ka Kb : ℕ} {s u : OuterStore}
    (ha : ExecutesOuter a Ka s u) (h : Ka ≤ Kb) : ExecutesOuter a Kb s u := by
  intro regs
  obtain ⟨n,r,hn,he⟩ := ha regs
  exact ⟨n,r,hn.trans h,he⟩

def projectInner (s : OuterStore) : Store := s ∘ innerPort

noncomputable def replaceInner (s : OuterStore) (u : Store) : OuterStore := Function.extend innerPort u s

theorem replaceInner_project (s : OuterStore) : replaceInner s (projectInner s)=s := by
  have h := embedState_project id innerPort (⟨fun _=>false,s⟩ : OuterData)
    Function.injective_id innerPort_injective
  exact congrArg StructuredProgram.State.stacks h

theorem replaceInner_update (s : OuterStore) (u : Store) (i : Fin 256) (bits : List Bool) :
    replaceInner s (Function.update u i bits)=Function.update (replaceInner s u) (innerPort i) bits :=
  ProgramLinking.extend_update innerPort_injective _ _ _ _

theorem liftInner_run (s : OuterStore) (code : Code) (K : ℕ) (u : Store)
    (h : ExecutesIn code K (projectInner s) u) :
    ExecutesOuter (liftInner code) (K+1) s (replaceInner s u) := by
  intro regs
  obtain ⟨k,rf,hk,he⟩ := h regs
  have hl := eval_liftCommand_from_state code 0 0 id innerPort (⟨regs,s⟩ : OuterData)
    Function.injective_id innerPort_injective he
  refine ⟨k+1,rf,by omega,?_⟩
  convert hl using 1
  · rfl
  · apply state_ext
    · simp [embedState]
    · rfl

/-- A common single-result service remains a single-result service after
relocation, with the exact one-step compiled-call overhead. -/
theorem liftInner_update_run (s : OuterStore) (code : Code) (K : ℕ)
    (i : Fin 256) (bits : List Bool)
    (h : ExecutesIn code K (projectInner s) (Function.update (projectInner s) i bits)) :
    ExecutesOuter (liftInner code) (K+1) s (Function.update s (innerPort i) bits) := by
  have hh := liftInner_run s code K _ h
  simpa only [replaceInner_update,replaceInner_project] using hh

def literalReady (s : OuterStore) (count acc : List Bool) : OuterStore :=
  Function.update (Function.update s 573 count) 569 acc

def tableRecord (payload : ℕ → List Bool) (j : ℕ) : List Bool :=
  Encoding.frame (Encoding.encodeNat j) ++ Encoding.frame (payload j)

def tableResult (payload : ℕ → List Bool) : ℕ → List Bool → List Bool
  | 0,acc => acc
  | n+1,acc => tableResult payload n (tableRecord payload n ++ acc)

theorem literalPopped (s : OuterStore) (count acc : List Bool) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped literalPorts (⟨regs,literalReady s count acc⟩ : OuterData)=
      (⟨readRegs regs 0 1 count.head?,literalReady s count.tail acc⟩ : OuterData) := by
  apply state_ext
  · simp [UnaryForPrograms.popped,literalPorts,literalReady]
  · funext i
    by_cases h573 : i=573 <;> by_cases h569 : i=569 <;>
      simp [UnaryForPrograms.popped,literalPorts,literalReady,h573,h569]

/-- The table is built by n paid invocations, in descending variable order.
The callback premise is for one fixed command and is discharged by the
literal source/branch/low-worker composition. -/
theorem literalLoop_run (s : OuterStore) (body : OuterCode) (payload : ℕ → List Bool)
    (K n : ℕ)
    (hbody : ∀ j,j < n → ∀ acc, ExecutesOuter body K
      (literalReady s (List.replicate j true) acc)
      (literalReady s (List.replicate j true) (tableRecord payload j ++ acc))) :
    ∀ j,j ≤ n → ∀ acc, ExecutesOuter (UnaryForPrograms.forCmd literalPorts body)
      (j*(K+2)+2) (literalReady s (List.replicate j true) acc)
      (literalReady s [] (tableResult payload j acc)) := by
  intro j hj acc regs
  suffices h : ∃ costs k rf, UnaryForPrograms.Visits literalPorts body costs k
      (⟨regs,literalReady s (List.replicate j true) acc⟩ : OuterData)
      (⟨rf,literalReady s [] (tableResult payload j acc)⟩ : OuterData) ∧ k ≤ j*(K+2)+2 by
    obtain ⟨costs,k,rf,hv,hk⟩ := h
    exact ⟨k,rf,hk,hv.eval⟩
  induction j generalizing acc regs with
  | zero =>
      refine ⟨[],2,readRegs regs 0 1 none,?_,by simp⟩
      simpa [literalPopped,tableResult] using
        UnaryForPrograms.Visits.done (p:=literalPorts) (body:=body)
          (⟨regs,literalReady s [] acc⟩ : OuterData) (by simp [literalReady,literalPorts])
  | succ j ih =>
      obtain ⟨nb,rb,hnb,heb⟩ := hbody j (by omega) acc (readRegs regs 0 1 (some true))
      obtain ⟨costs,nt,rt,ht,hnt⟩ := ih (by omega) (tableRecord payload j ++ acc) rb
      refine ⟨nb::costs,nb+nt+2,rt,?_,?_⟩
      · have hv := UnaryForPrograms.Visits.step (p:=literalPorts) (body:=body)
          (d:=(⟨regs,literalReady s (List.replicate (j+1) true) acc⟩ : OuterData))
          (by simp [literalReady,literalPorts])
          (by simpa only [literalPopped,List.replicate_succ,List.head?_cons,List.tail_cons] using heb)
          (by simp [literalReady,literalPorts,UnaryForPrograms.popped,List.replicate_succ]) ht
        simpa only [tableResult] using hv
      · nlinarith


theorem tableResult_eq (payload : ℕ → List Bool) (n : ℕ) (acc : List Bool) :
    tableResult payload n acc=(List.range n).flatMap (tableRecord payload) ++ acc := by
  induction n generalizing acc with
  | zero => simp [tableResult]
  | succ n ih => simp [tableResult,ih,List.range_succ,List.flatMap_append,List.append_assoc]

/-- Full counted table traversal, including paid master copy and output move.
The per-literal premise is a trace for the actual fixed literalIteration.
No loop or table construction is left as a semantic operation. -/
theorem prepareFactor_run (s : OuterStore) (source : OuterCode) (payload : ℕ → List Bool)
    (K n : ℕ) (hn : s 552=List.replicate n true)
    (h460 : s 460=[]) (h573 : s 573=[]) (h569 : s 569=[])
    (h561 : s 561=[]) (h585 : s 585=[])
    (hbody : ∀ j,j < n → ∀ acc, ExecutesOuter (literalIteration source) K
      (literalReady s (List.replicate j true) acc)
      (literalReady s (List.replicate j true) (tableRecord payload j ++ acc))) :
    ExecutesOuter (prepareFactor source)
      (7*n+n*(K+2)+6*(tableResult payload n []).length+15) s
      (Function.update s 561 (tableResult payload n [])) := by
  let a := literalReady s (List.replicate n true) []
  let b := literalReady s [] (tableResult payload n [])
  have hc : ExecutesOuter (liftInner (copy 212 233)) (7*n+6) s a := by
    have h := liftInner_update_run s (copy 212 233) (7*n+5) 233 (List.replicate n true) (by
      simpa [projectInner,Function.comp_def,innerPort,hn,h573] using
        copy_run 212 233 (projectInner s) (by decide) (by decide) (by decide)
          (by simpa [projectInner,Function.comp_def,innerPort] using h460))
    have heq : Function.update s (innerPort 233) (List.replicate n true)=a := by
      funext i
      by_cases hi : i=569 <;> simp [a,literalReady,Function.update_apply,innerPort,hi,h569]
    simpa [heq] using h
  have hl : ExecutesOuter (UnaryForPrograms.forCmd literalPorts (literalIteration source))
      (n*(K+2)+2) a b := literalLoop_run s (literalIteration source) payload K n hbody n (by omega) []
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
  have h := hc.seq (hl.seq hm)
  convert h using 1 <;> first | rfl | omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
