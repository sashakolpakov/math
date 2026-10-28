import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryReadbackFrames

namespace OAI.Algorithms

/-! Relocation of the concrete reader into the shared marked/branch caller. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

abbrev Data := State 40 768
def regMap (i : Fin 19) : Fin 40 := i.castAdd 21
def stackMap (i : Fin 330) : Fin 768 := i.castAdd 438
abbrev command : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram QueryReadback.program regMap stackMap)

theorem regMap_injective : Function.Injective regMap := Fin.castAdd_injective 19 21
theorem stackMap_injective : Function.Injective stackMap := Fin.castAdd_injective 330 438

noncomputable def install (frame : Data) (a : QueryReadback.Data) : Data :=
  embedState regMap stackMap frame a

theorem register_outside (frame : Data) (a : QueryReadback.Data)
    (i : Fin 40) (hi : 19 ≤ i.val) :
    (install frame a).regs i = frame.regs i := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

theorem stack_outside (frame : Data) (a : QueryReadback.Data)
    (i : Fin 768) (hi : 330 ≤ i.val) :
    (install frame a).stacks i = frame.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

/-- The caller pays the reader's compiled halt instruction. All additional branch/setup
stacks and their controller registers are physically framed. -/
theorem run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (z : ℕ)
    (hz : z < 3^t) (hx : (RingProgram.modelRing t ht hd model M cache).decode x = (z : model.O t))
    (frame : Data) (a : QueryReadback.Data) (regs : Fin 8 → Bool) (modulus width : List Bool)
    (hm : BinaryArithmetic.toNat modulus = 3^t)
    (hw : width.length = SubexpLiftRing.baseWidth 3 t)
    (ready : QueryReadback.project a = start regs modulus width (RingProgram.flat x))
    (hs : a.stacks 323 = []) (ha : a.stacks 324 = []) :
    ∃ n b, n ≤ budget (SubexpLiftRing.baseWidth 3 t) modulus (RingProgram.flat x) +
        6 * (modulus.length + SubexpLiftRing.baseWidth 3 t) + 7 ∧
      Eval command n (install frame a) (install frame b) ∧
      BinaryArithmetic.toNat ((install frame b).stacks 323) = z ∧
      ((install frame b).stacks 323).length = modulus.length + SubexpLiftRing.baseWidth 3 t ∧
      (install frame b).stacks 324 = [] ∧
      b.stacks 320 = a.stacks 320 ∧ b.stacks 322 = a.stacks 322 ∧
      ∃ finalRegs word, b = QueryReadback.finish a finalRegs word modulus width := by
  obtain ⟨n,b,hn,he,hv,hscratch,hsource,hmass,finalRegs,word,hlen,hb⟩ :=
    QueryReadback.run t ht hd model M cache x z hz hx a regs modulus width hm hw ready hs ha
  have hc := compiled_halt_trace he 261 323
  have hl := eval_call_lifted QueryReadback.program regMap stackMap frame
    regMap_injective stackMap_injective hc
  have h323 : (install frame b).stacks 323 = b.stacks 323 :=
    embedState_stack regMap stackMap frame b stackMap_injective 323
  have h324 : (install frame b).stacks 324 = b.stacks 324 :=
    embedState_stack regMap stackMap frame b stackMap_injective 324
  have hbword : b.stacks 323 = word := by
    rw [hb]
    exact QueryReadback.finish_output a finalRegs word modulus width hs ha
  refine ⟨n+1,b,by omega,hl,?_,?_,?_,hsource,hmass,finalRegs,word,hb⟩
  · simpa only [h323] using hv
  · simpa only [h323,hbword] using hlen
  · simpa only [h324] using hscratch

def project (a : Data) : QueryReadback.Data :=
  ⟨a.regs ∘ regMap, a.stacks ∘ stackMap⟩

theorem install_project (a : Data) : install a (project a) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, regMap j = i
    · obtain ⟨j,rfl⟩ := h
      exact embedState_register regMap stackMap a (project a) regMap_injective j
    · exact embedState_register_frame regMap stackMap a (project a) i h
  · funext i
    by_cases h : ∃ j, stackMap j = i
    · obtain ⟨j,rfl⟩ := h
      exact embedState_stack regMap stackMap a (project a) stackMap_injective j
    · exact embedState_stack_frame regMap stackMap a (project a) i h

/-- Readiness is stated on the real wide caller tapes, without requiring a
caller to supply a preconstructed embedded machine state. -/
theorem run_at (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (z : ℕ)
    (hz : z < 3^t) (hx : (RingProgram.modelRing t ht hd model M cache).decode x = (z : model.O t))
    (a : Data) (hvalue : a.stacks 261 = RingProgram.flat x)
    (hm : BinaryArithmetic.toNat (a.stacks 194) = 3^t)
    (hw : (a.stacks 202).length = SubexpLiftRing.baseWidth 3 t)
    (hempty : ∀ i ∈ ([323,324,325,326,327,328,329] : List (Fin 768)), a.stacks i = []) :
    ∃ k b, k ≤ budget (SubexpLiftRing.baseWidth 3 t) (a.stacks 194) (RingProgram.flat x) +
        6*((a.stacks 194).length+SubexpLiftRing.baseWidth 3 t)+7 ∧
      Eval command k a b ∧ BinaryArithmetic.toNat (b.stacks 323) = z ∧
      (b.stacks 323).length = (a.stacks 194).length+SubexpLiftRing.baseWidth 3 t ∧
      b.stacks 324 = [] ∧
      ∃ finalRegs word, b = install a
        (QueryReadback.finish (project a) finalRegs word (a.stacks 194) (a.stacks 202)) := by
  let q := project a
  have hs : q.stacks 323 = [] := hempty 323 (by simp)
  have ha : q.stacks 324 = [] := hempty 324 (by simp)
  have hr : QueryReadback.project q = start (q.regs ∘ QueryReadback.regMap)
      (a.stacks 194) (a.stacks 202) (RingProgram.flat x) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [QueryReadback.stackMap,q,project,stackMap,store,hvalue,hempty 325 (by simp),hempty 326 (by simp),
          hempty 327 (by simp),hempty 328 (by simp),hempty 329 (by simp)]
  obtain ⟨k,b,hk,he,hv,hl,hclear,_,_,rr,word,hb⟩ :=
    run t ht hd model M cache x z hz hx a q (q.regs ∘ QueryReadback.regMap)
      (a.stacks 194) (a.stacks 202) hm hw hr hs ha
  rw [show install a q = a from install_project a] at he
  exact ⟨k,install a b,hk,he,hv,hl,hclear,rr,word,congrArg (install a) hb⟩

theorem finished_stack_frame (a : Data) (regs : Fin 8 → Bool)
    (word : List Bool) (i : Fin 768)
    (hi : i ∉ ([194,202,261,323,324,325,326,327,328,329] : List (Fin 768))) :
    (install a (QueryReadback.finish (project a) regs word
      (a.stacks 194) (a.stacks 202))).stacks i = a.stacks i := by
  by_cases hsmall : i.val < 330
  · let j : Fin 330 := ⟨i.val,hsmall⟩
    have heq : stackMap j = i := Fin.ext rfl
    rw [← heq]
    rw [show (install a (QueryReadback.finish (project a) regs word
        (a.stacks 194) (a.stacks 202))).stacks (stackMap j) =
        (QueryReadback.finish (project a) regs word (a.stacks 194) (a.stacks 202)).stacks j from
      embedState_stack regMap stackMap a _ stackMap_injective j]
    rw [QueryReadback.finish_stack_frame]
    · rfl
    · intro hj
      apply hi
      have hm := List.mem_map.mpr ⟨j,hj,heq⟩
      simpa [stackMap] using hm
  · exact stack_outside a _ i (by omega)

end SubexponentialSAT.SqrtLog.LeafProgram.QueryReadback.Wide

end OAI.Algorithms
