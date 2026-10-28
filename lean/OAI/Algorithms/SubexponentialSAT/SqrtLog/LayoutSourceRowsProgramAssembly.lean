import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramController

namespace OAI.Algorithms

/-! The fixed outer source-row controller, including cache initialization,
actual pair-plan search, row traversal, and packed-index cleanup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def preparedSourceStore (s : Store) (D W : ℕ) (ps : List (ℕ × ℕ)) (v N f : ℕ) : Store :=
  Function.update (initializeFinish s D W) 304
    (LayoutSourcePlanLookup.unary (ps.idxOf (v,N+f)))

def RowsClean (s : Store) : Prop :=
  ∀ i∈([205,240,330,334,320,331,332,339] : List (Fin 340)), s i=[]

theorem sourceRows_present_from_rows {Witness : Type*}
    (source : Code) (s : Store) (D W v N f : ℕ) (ps : List (ℕ × ℕ))
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts) D W)
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hmem : (v,N+f) ∈ ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s D W⟩ : Data))
    (encode : Witness → List Bool) (R : ℕ → Witness → Prop) (K rowWidth : ℕ)
    (hspec : RelRowSpec (sourceRowWith source) (preparedSourceStore s D W ps v N f) encode R N K rowWidth)
    (hclean : RowsClean (preparedSourceStore s D W ps v N f))
    (regs : Fin 16 → Bool) :
    ∃ ws n rf, RowProperty encode R rowWidth 0 ws ∧ ws.length=N ∧
      n ≤ LayoutSourceRowsProgramInitialize.budget D W+
        LayoutSourcePlanLookup.pairBudget v N f ps+N*(K+19*rowWidth+39)+
        2*(ps.idxOf (v,N+f))+23 ∧
      Eval (sourceRowsWith source) n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (initializeFinish s D W) 205 (Encoding.encodeList encode ws)⟩ : Data) := by
  let s1 := initializeFinish s D W
  let p := preparedSourceStore s D W ps v N f
  obtain ⟨n1,r1,hn1,he1⟩ := initializeSource_run s D W hinit regs
  have hc : LayoutSourcePlanLookup.Native.Clean (⟨r1,s1⟩ : Data) := hlookup
  obtain ⟨n2,hn2,e2,he2,hs2,hflag⟩ := LayoutSourcePlanLookup.pair_command_eval_found
    (⟨r1,s1⟩ : Data) ps v N f
    (by simpa [s1,initializeFinish] using hv)
    (by simpa [s1,initializeFinish] using hN)
    (by simpa [s1,initializeFinish] using hf)
    (by simpa [s1,initializeFinish] using hplan) hc
  have he2' : Eval LayoutSourcePlanLookup.Native.command n2 (⟨r1,s1⟩ : Data)
      (⟨e2.regs,p⟩ : Data) := by
    have hh : e2=(⟨e2.regs,p⟩ : Data) := by
      apply SubexpScanPrimitives.state_ext
      · rfl
      · exact hs2
    rw [hh] at he2
    exact he2
  obtain ⟨ws,n3,r3,hr,hcount,hn3,he3⟩ := rowsCommand_rel (sourceRowWith source) p encode R N K rowWidth hspec
    (by simp [p,preparedSourceStore,initializeFinish,hN,LayoutSourcePlanLookup.unary])
    (hclean 240 (by simp)) (hclean 330 (by simp)) (hclean 334 (by simp))
    (hclean 320 (by simp)) (hclean 331 (by simp)) (hclean 332 (by simp))
    (hclean 205 (by simp)) (hclean 339 (by simp)) e2.regs
  let p' := Function.update p 205 (Encoding.encodeList encode ws)
  obtain ⟨n4,r4,hn4,he4⟩ := clear_run 304 p' r3
  have h304 : s1 304=[] := hlookup 304 (by simp)
  have hout : Function.update p' 304 []=
      Function.update s1 205 (Encoding.encodeList encode ws) := by
    funext i
    by_cases h : i=304 <;>
      simp [p',p,preparedSourceStore,s1,Function.update_apply,h,h304]
  rw [hout] at he4
  have hbranch := Eval.ite_true (no := zeroRows) (by simpa [hmem] using hflag) he3
  refine ⟨ws,n1+(n2+((n3+1)+n4)),r4,hr,hcount,?_,he1.seq (he2'.seq (hbranch.seq he4))⟩
  have hn4' : n4 ≤ 2*(ps.idxOf (v,N+f))+3 := by
    simpa [p',p,preparedSourceStore,LayoutSourcePlanLookup.unary] using hn4
  omega

theorem sourceRows_absent (source : Code) (s : Store) (D W v N f : ℕ) (ps : List (ℕ × ℕ))
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts) D W)
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hmem : (v,N+f) ∉ ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s D W⟩ : Data))
    (hclean : RowsClean (preparedSourceStore s D W ps v N f)) :
    ExecutesIn (sourceRowsWith source)
      (LayoutSourceRowsProgramInitialize.budget D W+
        LayoutSourcePlanLookup.pairBudget v N f ps+N*(26*(D*W)+44)+
        2*(ps.idxOf (v,N+f))+23) s
      (Function.update (initializeFinish s D W) 205
        (Encoding.encodeList id (List.replicate N (List.replicate (D*W) false)))) := by
  intro regs
  let s1 := initializeFinish s D W
  let p := preparedSourceStore s D W ps v N f
  let bits := List.replicate (D*W) false
  obtain ⟨n1,r1,hn1,he1⟩ := initializeSource_run s D W hinit regs
  have hc : LayoutSourcePlanLookup.Native.Clean (⟨r1,s1⟩ : Data) := hlookup
  obtain ⟨n2,hn2,e2,he2,hs2,hflag⟩ := LayoutSourcePlanLookup.pair_command_eval_found
    (⟨r1,s1⟩ : Data) ps v N f
    (by simpa [s1,initializeFinish] using hv)
    (by simpa [s1,initializeFinish] using hN)
    (by simpa [s1,initializeFinish] using hf)
    (by simpa [s1,initializeFinish] using hplan) hc
  have he2' : Eval LayoutSourcePlanLookup.Native.command n2 (⟨r1,s1⟩ : Data)
      (⟨e2.regs,p⟩ : Data) := by
    have hh : e2=(⟨e2.regs,p⟩ : Data) := by
      apply SubexpScanPrimitives.state_ext
      · rfl
      · exact hs2
    rw [hh] at he2
    exact he2
  obtain ⟨n3,r3,hn3,he3⟩ := zeroRows_run p bits N
    (by simp [p,bits,preparedSourceStore,initializeFinish])
    (by simp [p,preparedSourceStore,initializeFinish,hN,LayoutSourcePlanLookup.unary])
    (hclean 240 (by simp)) (hclean 330 (by simp)) (hclean 334 (by simp))
    (hclean 320 (by simp)) (hclean 331 (by simp)) (hclean 332 (by simp))
    (hclean 205 (by simp)) (hclean 339 (by simp)) e2.regs
  let p' := Function.update p 205 (Encoding.encodeList id (List.replicate N bits))
  obtain ⟨n4,r4,hn4,he4⟩ := clear_run 304 p' r3
  have h304 : s1 304=[] := hlookup 304 (by simp)
  have hout : Function.update p' 304 []=
      Function.update s1 205 (Encoding.encodeList id (List.replicate N bits)) := by
    funext i
    by_cases h : i=304 <;>
      simp [p',p,preparedSourceStore,s1,Function.update_apply,h,h304]
  rw [hout] at he4
  have hbranch := Eval.ite_false (yes := rowsCommand (sourceRowWith source)) (by simpa [hmem] using hflag) he3
  refine ⟨n1+(n2+((n3+1)+n4)),r4,?_,he1.seq (he2'.seq (hbranch.seq he4))⟩
  have hn4' : n4 ≤ 2*(ps.idxOf (v,N+f))+3 := by
    simpa [p',p,preparedSourceStore,LayoutSourcePlanLookup.unary] using hn4
  simp only [bits,List.length_replicate] at hn3
  omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
