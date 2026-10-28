import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyCoordinate

namespace OAI.Algorithms

/-! Fixed native traversal of the actual runtime-framed row list. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

def coordinate : Code := .seq loadCoordinate finishCoordinate

def rowPorts : UnaryForPrograms.Ports 16 256 := ⟨231,0,1⟩
def rowLoop (body : Code) : Code := UnaryForPrograms.forCmd rowPorts body

def rowsReady {C : Type*} (base : Store) (encode : C → List Bool)
    (j : ℕ) (cs : List C) (acc count : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update base
    230 (Encoding.encodeList encode cs)) 231 count) 218 (List.replicate j true)) 217 acc

def rowsResult {C : Type*} (step : ℕ → C → List Bool → List Bool) :
    ℕ → List C → List Bool → List Bool
  | _, [], acc => acc
  | j, c::cs, acc => rowsResult step (j+1) cs (step j c acc)

theorem rowPopped {C : Type*} (base : Store) (encode : C → List Bool)
    (j : ℕ) (cs : List C) (acc count : List Bool) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped rowPorts (⟨regs,rowsReady base encode j cs acc count⟩ : Data) =
      (⟨readRegs regs 0 1 count.head?,rowsReady base encode j cs acc count.tail⟩ : Data) := by
  apply state_ext
  · simp [UnaryForPrograms.popped,rowPorts,rowsReady]
  · funext i
    by_cases h231 : i=231 <;> by_cases h218 : i=218 <;> by_cases h217 : i=217 <;>
      simp [UnaryForPrograms.popped,rowPorts,rowsReady,Function.update_apply,h231,h218,h217]

/-- The callback premise is an execution trace for a fixed command. It is
instantiated by the fully composed load/shift/emission worker. -/
theorem rowLoop_run {C : Type*} (base : Store) (encode : C → List Bool)
    (body : Code) (step : ℕ → C → List Bool → List Bool) (K n : ℕ)
    (hbody : ∀ j, j < n → ∀ c cs acc count,
      ExecutesIn body K (rowsReady base encode j (c::cs) acc count)
        (rowsReady base encode (j+1) cs (step j c acc) count))
    (j : ℕ) (cs : List C) (acc count : List Bool)
    (hbound : j+cs.length ≤ n) (hlen : count.length=cs.length) :
    ExecutesIn (rowLoop body) (cs.length*(K+2)+2)
      (rowsReady base encode j cs acc count)
      (rowsReady base encode (j+cs.length) [] (rowsResult step j cs acc) []) := by
  intro regs
  suffices h : ∃ costs k rf, UnaryForPrograms.Visits rowPorts body costs k
      (⟨regs,rowsReady base encode j cs acc count⟩ : Data)
      (⟨rf,rowsReady base encode (j+cs.length) [] (rowsResult step j cs acc) []⟩ : Data) ∧
      k ≤ cs.length*(K+2)+2 by
    obtain ⟨costs,k,rf,hv,hk⟩ := h
    exact ⟨k,rf,hk,hv.eval⟩
  induction cs generalizing j acc count regs with
  | nil =>
      have hh : count=[] := List.length_eq_zero_iff.mp hlen
      subst count
      refine ⟨[],2,readRegs regs 0 1 none,?_,by simp⟩
      simpa [rowsResult,rowPopped] using
        UnaryForPrograms.Visits.done (p:=rowPorts) (body:=body)
          (⟨regs,rowsReady base encode j [] acc []⟩ : Data) (by simp [rowsReady,rowPorts])
  | cons c cs ih =>
      cases count with
      | nil => simp at hlen
      | cons bit count =>
          have hcount : count.length=cs.length := by simpa using hlen
          have hj : j < n := by simp only [List.length_cons] at hbound; omega
          have hb := hbody j hj c cs acc count
          obtain ⟨nb,rb,hnb,heb⟩ := hb (readRegs regs 0 1 (some bit))
          obtain ⟨costs,nt,rt,ht,hnt⟩ := ih (j:=j+1) (acc:=step j c acc) (count:=count) (regs:=rb)
            (by simp only [List.length_cons] at hbound; omega) hcount
          refine ⟨nb::costs,nb+nt+2,rt,?_,?_⟩
          · have hv := UnaryForPrograms.Visits.step
              (p:=rowPorts) (body:=body)
              (d:=(⟨regs,rowsReady base encode j (c::cs) acc (bit::count)⟩ : Data))
              (by simp [rowsReady,rowPorts])
              (by simpa only [rowPopped,List.head?_cons,List.tail_cons] using heb)
              (by simp [rowsReady,rowPorts,UnaryForPrograms.popped]) ht
            simpa [rowsResult,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hv
          · simp only [List.length_cons]
            nlinarith

/-- Masters205/212 are copied, scanned and retained. Only dictionary217 changes. -/
def scanRows (body : Code) : Code := .seq (copy 205 230) (.seq (copy 212 231)
  (.seq (rowLoop body) (.seq (clear 230) (clear 218))))


theorem scanRows_run {C : Type*} (s : Store) (encode : C → List Bool)
    (body : Code) (step : ℕ → C → List Bool → List Bool) (K : ℕ)
    (cs : List C) (hcs : s 205=Encoding.encodeList encode cs)
    (hn : (s 212).length=cs.length)
    (h120 : s 120=[]) (h230 : s 230=[]) (h231 : s 231=[]) (h218 : s 218=[])
    (hbody : ∀ j, j < cs.length → ∀ c rest acc count,
      ExecutesIn body K (rowsReady s encode j (c::rest) acc count)
        (rowsReady s encode (j+1) rest (step j c acc) count)) :
    ExecutesIn (scanRows body)
      (7*(s 205).length+9*cs.length+cs.length*(K+2)+20) s
      (Function.update s 217 (rowsResult step 0 cs (s 217))) := by
  let s1 := Function.update s 230 (s 205)
  let s2 := Function.update s1 231 (s 212)
  let s3 := rowsReady s encode cs.length [] (rowsResult step 0 cs (s 217)) []
  let s4 := Function.update s3 230 []
  have h1 : ExecutesIn (copy 205 230) (7*(s 205).length+5) s s1 := by
    simpa [s1,h230] using copy_run 205 230 s (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn (copy 212 231) (7*cs.length+5) s1 s2 := by
    simpa [s2,s1,h231,hn] using copy_run 212 231 s1
      (by decide) (by decide) (by decide) (by simp [s1,h120])
  have hin : rowsReady s encode 0 cs (s 217) (s 212)=s2 := by
    funext i
    by_cases h217' : i=217 <;> by_cases h218' : i=218 <;>
      by_cases h230' : i=230 <;> by_cases h231' : i=231 <;>
      simp [s2,s1,rowsReady,hcs,h218,h217',h218',h230',h231']
  have h3 : ExecutesIn (rowLoop body) (cs.length*(K+2)+2) s2 s3 := by
    have h := rowLoop_run s encode body step K cs.length hbody 0 cs (s 217) (s 212)
      (by omega) hn
    rw [hin] at h
    simpa [s3] using h
  have h4 : ExecutesIn (clear 230) 5 s3 s4 := by
    simpa [s4,s3,rowsReady,Encoding.encodeList] using clear_run 230 s3
  have hout : Function.update s4 218 []=Function.update s 217 (rowsResult step 0 cs (s 217)) := by
    funext i
    by_cases h217' : i=217 <;> by_cases h218' : i=218 <;>
      by_cases h230' : i=230 <;> by_cases h231' : i=231 <;>
      simp [s4,s3,rowsReady,h217',h218',h230',h231',h218,h230,h231]
  have h5 : ExecutesIn (clear 218) (2*cs.length+3) s4
      (Function.update s 217 (rowsResult step 0 cs (s 217))) := by
    have h := clear_run 218 s4
    rw [hout] at h
    simpa [s4,s3,rowsReady] using h
  have hcost : (7*(s 205).length+5) + ((7*cs.length+5) +
      ((cs.length*(K+2)+2) + (5 + (2*cs.length+3)))) =
      7*(s 205).length+9*cs.length+cs.length*(K+2)+20 := by
    omega
  rw [← hcost]
  simpa only [scanRows] using h1.seq (h2.seq (h3.seq (h4.seq h5)))


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
