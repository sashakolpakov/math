import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyOrigin
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeBitProgram

namespace OAI.Algorithms

/-! Native high-variable dispatch from original-coordinate mask/assignment
masters. The runtime index is233, and both source masters are retained. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

def flagRegs : Fin 3 → Fin 16 := ![0,1,15]
def flagStacks : Fin 2 → Fin 256 := ![222,223]
def bitRead : Code := .call (ProgramLinking.liftProgram
  Subexp.TypeBitProgram.program flagRegs flagStacks)

theorem bitRead_eval (s : Store) (regs : Fin 16 → Bool) :
    ∃ rf, Eval bitRead (Subexp.TypeBitProgram.cost (s 222) (s 223))
      (⟨regs,s⟩ : Data) (⟨rf,Function.update (Function.update s 222 []) 223 []⟩ : Data) ∧
      rf 15=(s 223).getD (s 222).length false := by
  let d : Data := ⟨regs,s⟩
  let a := projectState flagRegs flagStacks d
  let b : State 3 2 := ⟨Subexp.TypeBitProgram.resultRegs ((s 223).getD (s 222).length false),![[],[]]⟩
  have ht := Subexp.TypeBitProgram.trace (s 222) (s 223) a.regs
  have ha : a.withPC (some Subexp.TypeBitProgram.program.entry)=
      Subexp.TypeBitProgram.cfg (some 0) a.regs (s 222) (s 223) := by
    apply congrArg (fun ss : Fin 2 → List Bool => (⟨some 0,a.regs,ss⟩ : Cfg 3 2 7))
    funext i; fin_cases i <;> rfl
  have hb : b.withPC none=Subexp.TypeBitProgram.cfg none b.regs [] [] := by
    apply congrArg (fun ss : Fin 2 → List Bool => (⟨none,b.regs,ss⟩ : Cfg 3 2 7))
    funext i; fin_cases i <;> rfl
  have ht' : Trace Subexp.TypeBitProgram.program
      (Subexp.TypeBitProgram.cost (s 222) (s 223))
      (a.withPC (some Subexp.TypeBitProgram.program.entry)) (b.withPC none) := by
    rw [ha,hb]
    exact ht
  have he := eval_call_from_state Subexp.TypeBitProgram.program flagRegs flagStacks d
    (by decide) (by decide) ht'
  let rf := Function.extend flagRegs b.regs regs
  have hout : embedState flagRegs flagStacks d b =
      (⟨rf,Function.update (Function.update s 222 []) 223 []⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ (by decide) (by decide)
    · intro i; exact (show Function.Injective flagRegs from by decide).extend_apply b.regs regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [b,flagStacks]
    · intro i hi
      have h222 : i≠222 := by intro h; subst i; exact hi ⟨0,rfl⟩
      have h223 : i≠223 := by intro h; subst i; exact hi ⟨1,rfl⟩
      simp [d,h222,h223]
  rw [hout] at he
  refine ⟨rf,he,?_⟩
  change Function.extend flagRegs b.regs regs (flagRegs 2)=_
  rw [(show Function.Injective flagRegs from by decide).extend_apply]
  rfl

def readFlag (source : Fin 256) : Code :=
  .seq (copy 233 222) (.seq (copy source 223) bitRead)

theorem readFlag_eval (s : Store) (source : Fin 256)
    (hsrc : source≠222) (hsrc' : source≠223) (h120s : source≠120)
    (h120 : s 120=[]) (h222 : s 222=[]) (h223 : s 223=[])
    (regs : Fin 16 → Bool) :
    ∃ k rf, k ≤ 10*(s 233).length+9*(s source).length+16 ∧
      Eval (readFlag source) k (⟨regs,s⟩ : Data) (⟨rf,s⟩ : Data) ∧
      rf 15=(s source).getD (s 233).length false := by
  let s1 := Function.update s 222 (s 233)
  let s2 := Function.update s1 223 (s source)
  have h1 : ExecutesIn (copy 233 222) (7*(s 233).length+5) s s1 := by
    simpa [s1,h222] using copy_run 233 222 s (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn (copy source 223) (7*(s source).length+5) s1 s2 := by
    simpa [s1,s2,hsrc,h223] using copy_run source 223 s1 hsrc' h120s (by decide)
      (by simp [s1,h120])
  obtain ⟨n1,r1,hn1,he1⟩ := h1 regs
  obtain ⟨n2,r2,hn2,he2⟩ := h2 r1
  obtain ⟨rf,he3,hflag⟩ := bitRead_eval s2 r2
  have hout : Function.update (Function.update s2 222 []) 223 []=s := by
    funext i
    by_cases h222' : i=222 <;> by_cases h223' : i=223 <;>
      simp [s2,s1,h222',h223',h222,h223]
  rw [hout] at he3
  refine ⟨n1+(n2+Subexp.TypeBitProgram.cost (s2 222) (s2 223)),rf,?_,?_,?_⟩
  · have hc : Subexp.TypeBitProgram.cost (s2 222) (s2 223) ≤
        3*(s 233).length+2*(s source).length+6 := by
      simpa [s2,s1] using Subexp.TypeBitProgram.cost_le (s2 222) (s2 223)
    omega
  · exact he1.seq (he2.seq he3)
  · simpa [s2,s1] using hflag

/-- For a high literal, select the full ring constant from the current branch. -/
def highConstant : Code := .seq (readFlag 235)
  (.seq (.ite 15 (copy 208 220) (copy 207 220)) (.seq origin (clear 220)))


theorem highConstant_run (s : Store) (n W : ℕ)
    (hn : (s 212).length=n) (hm : (s 235).length=n)
    (hzero : (s 207).length=W) (hone : (s 208).length=W)
    (h220 : s 220=[]) (he : ∀ i∈originScratch,s i=[]) :
    ExecutesIn highConstant (10*(s 233).length+42*n+29*W+108) s
      (Function.update s 217 (Encoding.frame (originKey n)++
        Encoding.frame (if (s 235).getD (s 233).length false then s 208 else s 207)++s 217)) := by
  intro regs
  let b := (s 235).getD (s 233).length false
  let value := if b then s 208 else s 207
  let s1 := Function.update s 220 value
  let s2 := Function.update s1 217 (Encoding.frame (originKey n)++Encoding.frame value++s 217)
  have hv : value.length=W := by cases hb:b <;> simp [value,hb,hzero,hone]
  obtain ⟨nr,rr,hnr,hr,hbit⟩ := readFlag_eval s 235 (by decide) (by decide) (by decide)
    (he 120 (by simp [originScratch])) (he 222 (by simp [originScratch]))
    (he 223 (by simp [originScratch])) regs
  have hcopy : ∃ nc rc, nc ≤ 7*W+6 ∧
      Eval (.ite 15 (copy 208 220) (copy 207 220)) nc
        (⟨rr,s⟩ : Data) (⟨rc,s1⟩ : Data) := by
    cases hb:b with
    | false =>
      obtain ⟨nc,rc,hnc,hc⟩ := copy_run 207 220 s (by decide) (by decide) (by decide)
        (he 120 (by simp [originScratch])) rr
      refine ⟨nc+1,rc,by simpa [hzero] using Nat.add_le_add_right hnc 1,?_⟩
      have hf : rr 15=false := hbit.trans hb
      have hh := Eval.ite_false (yes:=copy 208 220) hf hc
      simpa [s1,value,hb,h220] using hh
    | true =>
      obtain ⟨nc,rc,hnc,hc⟩ := copy_run 208 220 s (by decide) (by decide) (by decide)
        (he 120 (by simp [originScratch])) rr
      refine ⟨nc+1,rc,by simpa [hone] using Nat.add_le_add_right hnc 1,?_⟩
      have hf : rr 15=true := hbit.trans hb
      have hh := Eval.ite_true (no:=copy 207 220) hf hc
      simpa [s1,value,hb,h220] using hh
  obtain ⟨nc,rc,hnc,hc⟩ := hcopy
  have hs1 : ∀ i∈originScratch,s1 i=[] := by
    intro i hi
    have hi220 : i ≠ 220 := by
      intro h
      subst i
      simp [originScratch] at hi
    simpa [s1,hi220] using he i hi
  have horigin : ExecutesIn origin (33*n+20*W+83) s1 s2 := by
    simpa [s2,s1,hv] using origin_run s1 n (by simpa [s1] using hn) hs1
  obtain ⟨no,ro,hno,ho⟩ := horigin rc
  have hout : Function.update s2 220 []=Function.update s 217
      (Encoding.frame (originKey n)++Encoding.frame value++s 217) := by
    funext i
    by_cases h217' : i=217 <;> by_cases h220' : i=220 <;>
      simp [s2,s1,h217',h220',h220]
  have hclear := clear_run 220 s2
  rw [hout] at hclear
  obtain ⟨nf,rf,hnf,hf⟩ := hclear ro
  refine ⟨nr+(nc+(no+nf)),rf,?_,hr.seq (hc.seq (ho.seq hf))⟩
  simp only [s2,s1,Function.update_same,Function.update_of_ne (by decide : (220:Fin 256)≠217),hv] at hnf
  rw [hm] at hnr
  omega


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
