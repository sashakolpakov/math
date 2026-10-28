import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyLiteral

namespace OAI.Algorithms

/-! Relational source composition binds the actual row/output witness of each
execution. It does not require equal polynomials to have equal encodings. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem literalPayload_rel (s : OuterStore) (source : OuterCode)
    (n W Ksource Klow Lrows Lpayload : ℕ) (Good : List Bool → Prop)
    (hn : (s 552).length=n) (hm : (s 575).length=n)
    (hzero : (s 547).length=W) (hone : (s 548).length=W)
    (h545 : s 545=[]) (h557 : s 557=[]) (h220 : s 560=[])
    (he : ∀ i∈originScratch,s (innerPort i)=[])
    (hsource : (s 574).getD (s 573).length false=false →
      ∀ regs : Fin 16 → Bool, ∃ words payload k rf,
      k ≤ Ksource ∧ words.length ≤ Lrows ∧ payload.length ≤ Lpayload ∧ Good payload ∧
      Eval source k (⟨regs,s⟩ : OuterData) (⟨rf,Function.update s 545 words⟩ : OuterData) ∧
      ExecutesIn prepareLow Klow (projectInner (Function.update s 545 words))
        (Function.update (projectInner (Function.update s 545 words)) 217 payload))
    (hhigh : (s 574).getD (s 573).length false=true →
      Good (Encoding.frame (originKey n)++
        Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)))
    (hhighLength : (Encoding.frame (originKey n)++
      Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)).length ≤ Lpayload)
    (regs : Fin 16 → Bool) :
    ∃ words payload k rf,
      k ≤ 10*(s 573).length+9*(s 574).length+18+
        (10*(s 573).length+42*n+29*W+109)+Ksource+Klow+1 ∧
      words.length ≤ Lrows ∧ payload.length ≤ Lpayload ∧ Good payload ∧
      Eval (literalPayload source) k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update (Function.update s 545 words) 557 payload⟩ : OuterData) := by
  obtain ⟨nr,rr,hnr,hr,hbit⟩ := readFlag_outer s 234 (by decide) (by decide) (by decide)
    (by simpa [innerPort] using he 120 (by simp [originScratch]))
    (by simpa [innerPort] using he 222 (by simp [originScratch]))
    (by simpa [innerPort] using he 223 (by simp [originScratch])) regs
  change nr ≤ 10*(s 573).length+9*(s 574).length+17 at hnr
  change rr 15=(s 574).getD (s 573).length false at hbit
  cases hb:(s 574).getD (s 573).length false with
  | false =>
      obtain ⟨words,payload,ns,rs,hns,hw,hp,hgood,hes,hlow⟩ := hsource hb rr
      obtain ⟨nl,rl,hnl,hel⟩ :=
        liftInner_update_run (Function.update s 545 words) prepareLow Klow 217 payload hlow rs
      have hflag : rr 15=false := by simpa only [hb] using hbit
      have hrun := hr.seq (Eval.ite_false (yes:=liftInner highConstant) hflag (hes.seq hel))
      refine ⟨words,payload,nr+(ns+nl+1),rl,by omega,hw,hp,hgood,?_⟩
      simpa [literalPayload,innerPort] using hrun
  | true =>
      let payload := Encoding.frame (originKey n)++
        Encoding.frame (if (s 575).getD (s 573).length false then s 548 else s 547)
      have hh := highConstant_run (projectInner s) n W
        (by simpa [projectInner,Function.comp_def,innerPort] using hn)
        (by simpa [projectInner,Function.comp_def,innerPort] using hm)
        (by simpa [projectInner,Function.comp_def,innerPort] using hzero)
        (by simpa [projectInner,Function.comp_def,innerPort] using hone)
        (by simpa [projectInner,Function.comp_def,innerPort] using h220)
        (by simpa [projectInner,Function.comp_def] using he)
      obtain ⟨nh,rh,hnh,heh⟩ := liftInner_update_run s highConstant _ 217 _ hh rr
      change nh ≤ (10*(s 573).length+42*n+29*W+108)+1 at hnh
      have hflag : rr 15=true := by simpa only [hb] using hbit
      have hrun := hr.seq (Eval.ite_true (no:=.seq source (liftInner prepareLow)) hflag heh)
      refine ⟨[],payload,nr+(nh+1),rh,by omega,by simp,hhighLength,hhigh hb,?_⟩
      have hz : Function.update s 545 []=s := by simpa only [←h545] using Function.update_eq_self 545 s
      simpa [literalPayload,innerPort,projectInner,Function.comp_def,payload,h557,hz] using hrun

theorem literalIteration_rel (s : OuterStore) (source : OuterCode) (j K Lrows Lpayload : ℕ)
    (Good : List Bool → Prop)
    (hj : s 573=List.replicate j true)
    (h545 : s 545=[]) (h555 : s 555=[]) (h557 : s 557=[])
    (he : ∀ i∈entryScratch,s (innerPort i)=[])
    (hpayload : ∀ regs : Fin 16 → Bool, ∃ words payload k rf,
      k ≤ K ∧ words.length ≤ Lrows ∧ payload.length ≤ Lpayload ∧ Good payload ∧
      Eval (literalPayload source) k
        (⟨regs,Function.update s 555 (Encoding.encodeNat j)⟩ : OuterData)
        (⟨rf,Function.update (Function.update (Function.update s 555 (Encoding.encodeNat j))
          545 words) 557 payload⟩ : OuterData))
    (regs : Fin 16 → Bool) :
    ∃ payload k rf,k ≤ 7*j+K+22*(j+1)+19*Lpayload+2*Lrows+54 ∧
      payload.length ≤ Lpayload ∧ Good payload ∧
      Eval (literalIteration source) k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update s 569 (Encoding.frame (Encoding.encodeNat j)++
          Encoding.frame payload++s 569)⟩ : OuterData) := by
  let key := Encoding.encodeNat j
  let a := Function.update s 555 key
  have hkey : ExecutesOuter (liftInner makeLiteralKey) (7*j+8) s a := by
    have h := liftInner_update_run s makeLiteralKey (7*j+7) 215 key
      (makeLiteralKey_run (projectInner s) j
        (by simpa [projectInner,Function.comp_def,innerPort] using hj)
        (by simpa [projectInner,Function.comp_def,innerPort] using h555)
        (by simpa [projectInner,Function.comp_def,innerPort] using he 120 (by simp [entryScratch])))
    simpa [a,innerPort] using h
  obtain ⟨nk,rk,hnk,hek⟩ := hkey regs
  obtain ⟨words,payload,np,rp,hnp,hw,hp,hgood,hep⟩ := hpayload rk
  let b := Function.update (Function.update a 545 words) 557 payload
  have hb : ∀ i∈entryScratch,(projectInner b) i=[] := by
    intro i hi
    have hn : innerPort i ≠ 555 ∧ innerPort i ≠ 545 ∧ innerPort i ≠ 557 := by
      simp [entryScratch] at hi
      constructor
      · intro h
        have hv := congrArg Fin.val h
        simp [innerPort] at hv
        omega
      constructor <;> intro h
      all_goals
        have hv := congrArg Fin.val h
        simp [innerPort] at hv
        omega
    simpa [b,a,projectInner,Function.comp_def,Function.update_apply,hn.1,hn.2.1,hn.2.2] using he i hi
  have hend := liftInner_run b finishLiteral
    (22*key.length+19*payload.length+2*words.length+45)
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
  obtain ⟨nf,rf,hnf,hef⟩ := hend rp
  refine ⟨payload,nk+(np+nf),rf,?_,hp,hgood,hek.seq (hep.seq hef)⟩
  simp only [key,Encoding.encodeNat,List.length_append,List.length_replicate,List.length_singleton] at hnf
  omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
