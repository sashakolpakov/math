import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyOuter
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyLow

namespace OAI.Algorithms

/-! Actual literal table entry construction and branch dispatch. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem makeLiteralKey_run (s : Store) (j : ℕ) (hj : s 233=List.replicate j true)
    (h215 : s 215=[]) (h120 : s 120=[]) :
    ExecutesIn makeLiteralKey (7*j+7) s (Function.update s 215 (Encoding.encodeNat j)) := by
  let a := Function.update s 215 [false]
  have hp : ExecutesIn (Subexp.TupleProgram.pushConst 215 0 false) 2 s a := by
    intro regs
    refine ⟨2,Function.update regs 0 false,by omega,?_⟩
    simpa [a,h215,Subexp.TupleProgram.pushedState] using
      Subexp.TupleProgram.pushConst_eval (215 : Fin 256) (0 : Fin 16) false (⟨regs,s⟩ : Data)
  have hc : ExecutesIn (copy 233 215) (7*j+5) a
      (Function.update s 215 (Encoding.encodeNat j)) := by
    simpa [a,hj,Encoding.encodeNat] using copy_run 233 215 a
      (by decide) (by decide) (by decide) (by simp [a,h120])
  convert hp.seq hc using 1 <;> first | rfl | omega

theorem readFlag_outer (s : OuterStore) (source : Fin 256)
    (hsrc : source≠222) (hsrc' : source≠223) (h120s : source≠120)
    (h120 : s 460=[]) (h222 : s 562=[]) (h223 : s 563=[])
    (regs : Fin 16 → Bool) :
    ∃ k rf,k ≤ 10*(s 573).length+9*(s (innerPort source)).length+17 ∧
      Eval (liftInner (readFlag source)) k (⟨regs,s⟩ : OuterData) (⟨rf,s⟩ : OuterData) ∧
      rf 15=(s (innerPort source)).getD (s 573).length false := by
  obtain ⟨k,rf,hk,he,hf⟩ := readFlag_eval (projectInner s) source hsrc hsrc' h120s
    (by simpa [projectInner,Function.comp_def,innerPort] using h120)
    (by simpa [projectInner,Function.comp_def,innerPort] using h222)
    (by simpa [projectInner,Function.comp_def,innerPort] using h223) regs
  have hl := eval_liftCommand_from_state (readFlag source) 0 0 id innerPort
    (⟨regs,s⟩ : OuterData) Function.injective_id innerPort_injective he
  have hout : embedState id innerPort (⟨regs,s⟩ : OuterData)
      (⟨rf,projectInner s⟩ : Data)=(⟨rf,s⟩ : OuterData) := by
    apply state_ext
    · simp [embedState]
    · exact replaceInner_project s
  rw [hout] at hl
  refine ⟨k+1,rf,?_,hl,?_⟩
  · simpa [projectInner,Function.comp_def,innerPort] using Nat.add_le_add_right hk 1
  · simpa [projectInner,Function.comp_def,innerPort] using hf

/-- The only service premise here is the actual source command's execution.
The high branch is the native mask lookup and constant dictionary emitter. -/
theorem literalPayload_run (s : OuterStore) (source : OuterCode)
    (n W Ksource Klow : ℕ) (rows payload : List Bool)
    (hn : (s 552).length=n) (hm : (s 575).length=n)
    (hzero : (s 547).length=W) (hone : (s 548).length=W)
    (h220 : s 560=[]) (he : ∀ i∈originScratch,s (innerPort i)=[])
    (hsource : ExecutesOuter source Ksource s (Function.update s 545 rows))
    (hlow : ExecutesIn prepareLow Klow (projectInner (Function.update s 545 rows))
      (Function.update (projectInner (Function.update s 545 rows)) 217 payload)) :
    ExecutesOuter (literalPayload source)
      (10*(s 573).length+9*(s 574).length+18 +
        (10*(s 573).length+42*n+29*W+109) + Ksource+Klow+1) s
      (if (s 574).getD (s 573).length false then
        Function.update s 557 (Encoding.frame (originKey n)++
          Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)++s 557)
       else Function.update (Function.update s 545 rows) 557 payload) := by
  intro regs
  obtain ⟨nr,rr,hnr,hr,hbit⟩ := readFlag_outer s 234 (by decide) (by decide) (by decide)
    (by simpa [innerPort] using he 120 (by simp [originScratch]))
    (by simpa [innerPort] using he 222 (by simp [originScratch]))
    (by simpa [innerPort] using he 223 (by simp [originScratch])) regs
  change nr ≤ 10*(s 573).length+9*(s 574).length+17 at hnr
  change rr 15=(s 574).getD (s 573).length false at hbit
  cases hb:(s 574).getD (s 573).length false with
  | false =>
      obtain ⟨ns,rs,hns,hes⟩ := hsource rr
      have hh := liftInner_update_run (Function.update s 545 rows) prepareLow Klow 217 payload hlow
      obtain ⟨nl,rl,hnl,hel⟩ := hh rs
      have hflag : rr 15=false := by simpa only [hb] using hbit
      have hrun := hr.seq (Eval.ite_false (yes:=liftInner highConstant) hflag (hes.seq hel))
      refine ⟨nr+(ns+nl+1),rl,by omega,?_⟩
      simpa [literalPayload,hb,innerPort] using hrun
  | true =>
      have hh := highConstant_run (projectInner s) n W
        (by simpa [projectInner,Function.comp_def,innerPort] using hn)
        (by simpa [projectInner,Function.comp_def,innerPort] using hm)
        (by simpa [projectInner,Function.comp_def,innerPort] using hzero)
        (by simpa [projectInner,Function.comp_def,innerPort] using hone)
        (by simpa [projectInner,Function.comp_def,innerPort] using h220)
        (by simpa [projectInner,Function.comp_def] using he)
      have hhl := liftInner_update_run s highConstant _ 217 _ hh
      obtain ⟨nh,rh,hnh,heh⟩ := hhl rr
      change nh ≤ (10*(s 573).length+42*n+29*W+108)+1 at hnh
      have hflag : rr 15=true := by simpa only [hb] using hbit
      have hrun := hr.seq (Eval.ite_true (no:=.seq source (liftInner prepareLow)) hflag heh)
      refine ⟨nr+(nh+1),rh,?_,?_⟩
      · omega
      · simpa [literalPayload,hb,innerPort,projectInner,Function.comp_def] using hrun


theorem finishLiteral_run (s : Store) (he : ∀ i∈entryScratch,s i=[]) :
    ExecutesIn finishLiteral
      (22*(s 215).length+19*(s 217).length+2*(s 205).length+45) s
      (Function.update (Function.update (Function.update (Function.update s 217 [])
        229 (Encoding.frame (s 215)++Encoding.frame (s 217)++s 229)) 215 []) 205 []) := by
  have h1 := entry_run s he
  let a := Function.update (Function.update s 217 []) 229
    (Encoding.frame (s 215)++Encoding.frame (s 217)++s 229)
  have h2 := clear_run 215 a
  have h3 := clear_run 205 (Function.update a 215 [])
  have h := h1.seq (h2.seq h3)
  convert h using 1
  · rfl
  · simp only [a,Function.update_of_ne (by decide : (215:Fin 256)≠229),
      Function.update_of_ne (by decide : (215:Fin 256)≠217),
      Function.update_of_ne (by decide : (205:Fin 256)≠215),
      Function.update_of_ne (by decide : (205:Fin 256)≠229),
      Function.update_of_ne (by decide : (205:Fin 256)≠217)]
    omega

/-- Literal control skeleton. The payload premise is discharged by the native
branch/source/low preparation theorem, rather than a supplied table. -/
theorem literalIteration_run (s : OuterStore) (source : OuterCode) (j K : ℕ)
    (rows payload : List Bool)
    (hj : s 573=List.replicate j true)
    (h545 : s 545=[]) (h555 : s 555=[]) (h557 : s 557=[])
    (he : ∀ i∈entryScratch,s (innerPort i)=[])
    (hpayload : ExecutesOuter (literalPayload source) K
      (Function.update s 555 (Encoding.encodeNat j))
      (Function.update (Function.update (Function.update s 555 (Encoding.encodeNat j))
        545 rows) 557 payload)) :
    ExecutesOuter (literalIteration source)
      (7*j+K+22*(j+1)+19*payload.length+2*rows.length+54) s
      (Function.update s 569 (Encoding.frame (Encoding.encodeNat j)++
        Encoding.frame payload++s 569)) := by
  let key := Encoding.encodeNat j
  let a := Function.update s 555 key
  let b := Function.update (Function.update a 545 rows) 557 payload
  have hkey : ExecutesOuter (liftInner makeLiteralKey) (7*j+8) s a := by
    have h := liftInner_update_run s makeLiteralKey (7*j+7) 215 key
      (makeLiteralKey_run (projectInner s) j
        (by simpa [projectInner,Function.comp_def,innerPort] using hj)
        (by simpa [projectInner,Function.comp_def,innerPort] using h555)
        (by simpa [projectInner,Function.comp_def,innerPort] using he 120 (by simp [entryScratch])))
    simpa [a,innerPort] using h
  have hb : ∀ i∈entryScratch,(projectInner b) i=[] := by
    intro i hi
    have hn : innerPort i≠555 ∧ innerPort i≠545 ∧ innerPort i≠557 := by
      simp [entryScratch] at hi
      constructor
      · intro h
        have hv := congrArg Fin.val h
        simp [innerPort] at hv
        omega
      constructor
      · intro h
        have hv := congrArg Fin.val h
        simp [innerPort] at hv
        omega
      · intro h
        have hv := congrArg Fin.val h
        simp [innerPort] at hv
        omega
    simpa [b,a,projectInner,Function.comp_def,Function.update_apply,hn.1,hn.2.1,hn.2.2] using he i hi
  have hend := liftInner_run b finishLiteral
    (22*key.length+19*payload.length+2*rows.length+45)
    (Function.update (Function.update (Function.update (Function.update (projectInner b) 217 [])
      229 (Encoding.frame ((projectInner b) 215)++Encoding.frame ((projectInner b) 217)++
        (projectInner b) 229)) 215 []) 205 [])
    (by simpa [projectInner,Function.comp_def,innerPort,b,a] using finishLiteral_run (projectInner b) hb)
  rw [replaceInner_update,replaceInner_update,replaceInner_update,replaceInner_update,
    replaceInner_project] at hend
  have hout : Function.update (Function.update (Function.update (Function.update b
      (innerPort 217) []) (innerPort 229)
      (Encoding.frame ((projectInner b) 215)++Encoding.frame ((projectInner b) 217)++(projectInner b) 229))
      (innerPort 215) []) (innerPort 205) []=
      Function.update s 569 (Encoding.frame key++Encoding.frame payload++s 569) := by
    funext i
    by_cases h545' : i=545
    · subst i; simp [innerPort,h545]
    by_cases h555' : i=555
    · subst i; simp [innerPort,h555]
    by_cases h557' : i=557
    · subst i; simp [innerPort,h557]
    by_cases h569' : i=569
    · subst i; simp [innerPort,projectInner,b,a]
    simp [innerPort,projectInner,b,a,h545',h555',h557',h569']
  rw [hout] at hend
  have h := hkey.seq (hpayload.seq hend)
  convert h using 1 <;> first | rfl | (simp [key,Encoding.encodeNat]; omega)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
