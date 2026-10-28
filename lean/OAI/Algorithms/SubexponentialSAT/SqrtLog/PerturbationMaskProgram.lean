import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionStore
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeMask

namespace OAI.Algorithms

/-! A fixed native constructor for original-coordinate singleton masks.
Masters212/218 are retained; output214 and scratch120/221/222/223 are the
only touched stacks. No table of masks or semantic mask oracle is supplied. -/
namespace SubexponentialSAT.SqrtLog.PerturbationMaskProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

private def fill (s : Store) (count out : List Bool) : Store :=
  Function.update (Function.update s 221 count) 214 out

@[simp] private theorem fill_count (s : Store) (count out : List Bool) :
    fill s count out 221=count := by simp [fill]
@[simp] private theorem fill_out (s : Store) (count out : List Bool) :
    fill s count out 214=out := by simp [fill]
@[simp] private theorem fill_update_count (s : Store) (count out next : List Bool) :
    Function.update (fill s count out) 221 next=fill s next out := by
  ext i
  by_cases h0 : i=221 <;> by_cases h1 : i=214 <;>
    simp [fill,Function.update_apply,h0,h1]
@[simp] private theorem fill_update_out (s : Store) (count out next : List Bool) :
    Function.update (fill s count out) 214 next=fill s count next := by
  simp [fill]

abbrev pushBit (b : Bool) : Code := Subexp.TupleProgram.pushConst 214 0 b

def zeroPorts : UnaryForPrograms.Ports 16 256 := ⟨221,0,1⟩
abbrev zeroLoop : Code := UnaryForPrograms.forCmd zeroPorts (pushBit false)
abbrev zeroCommand : Code := .seq (copy 212 221) zeroLoop

theorem pushBit_run (s : Store) (b : Bool) : ExecutesIn (pushBit b) 2 s
    (Function.update s 214 (b::s 214)) := by
  intro regs
  refine ⟨2,Function.update regs 0 b,le_rfl,?_⟩
  simpa [pushBit,Subexp.TupleProgram.pushedState] using
    Subexp.TupleProgram.pushConst_eval (214 : Fin 256) (0 : Fin 16) b (⟨regs,s⟩ : Data)

private theorem zero_visits (s : Store) (count out : List Bool) (regs : Fin 16 → Bool) :
    ∃ rr, UnaryForPrograms.Visits zeroPorts (pushBit false)
      (List.replicate count.length 2) (4*count.length+2)
      (⟨regs,fill s count out⟩ : Data)
      (⟨rr,fill s [] (List.replicate count.length false++out)⟩ : Data) := by
  induction count generalizing out regs with
  | nil =>
      refine ⟨readRegs regs 0 1 none,?_⟩
      simpa [zeroPorts,UnaryForPrograms.popped] using
        (UnaryForPrograms.Visits.done (p := zeroPorts) (body := pushBit false)
          (⟨regs,fill s [] out⟩ : Data) (by simp [zeroPorts,fill]))
  | cons bit count ih =>
      let rp := readRegs regs 0 1 (some bit)
      let rb := Function.update rp 0 false
      have hb : Eval (pushBit false) 2
          (UnaryForPrograms.popped zeroPorts (⟨regs,fill s (bit::count) out⟩ : Data))
          (⟨rb,fill s count (false::out)⟩ : Data) := by
        simpa [pushBit,Subexp.TupleProgram.pushedState,UnaryForPrograms.popped,
          zeroPorts,rp,rb] using
          Subexp.TupleProgram.pushConst_eval (214 : Fin 256) (0 : Fin 16) false
            (⟨rp,fill s count out⟩ : Data)
      obtain ⟨rr,ht⟩ := ih (false::out) rb
      have he := UnaryForPrograms.Visits.step
        (p := zeroPorts) (body := pushBit false)
        (by simp [zeroPorts,fill] : (fill s (bit::count) out) zeroPorts.counter ≠ [])
        hb (by simp [zeroPorts,fill,UnaryForPrograms.popped]) ht
      have hout : List.replicate count.length false ++ (false::out) =
          List.replicate (count.length+1) false ++ out := by
        rw [List.replicate_succ']
        simp only [List.append_assoc,List.singleton_append]
      rw [hout] at he
      refine ⟨rr,?_⟩
      convert he using 1 <;> simp [List.replicate_succ] ; omega

theorem zeroLoop_run (s : Store) (count out : List Bool)
    (hc : s 221=count) (ho : s 214=out) :
    ExecutesIn zeroLoop (4*count.length+2) s
      (Function.update (Function.update s 221 []) 214
        (List.replicate count.length false++out)) := by
  intro regs
  obtain ⟨rr,hv⟩ := zero_visits s count out regs
  have hs : fill s count out=s := by
    ext i
    by_cases h0 : i=221 <;> by_cases h1 : i=214 <;>
      simp_all [fill]
  refine ⟨4*count.length+2,rr,le_rfl,?_⟩
  have he := hv.eval
  rw [hs] at he
  exact he

/-- Zero-mask construction retains the count master and all unrelated stacks. -/
theorem zero_run (s : Store) (n : ℕ) (hn : (s 212).length=n)
    (h120 : s 120=[]) (h221 : s 221=[]) (h214 : s 214=[]) :
    ExecutesIn zeroCommand (11*n+7) s
      (Function.update s 214 (List.replicate n false)) := by
  let mid := Function.update s 221 (s 212)
  have h1 : ExecutesIn (copy 212 221) (7*n+5) s mid := by
    simpa [mid,hn,h221] using copy_run 212 221 s (by decide) (by decide) (by decide) h120
  have h2 := zeroLoop_run mid (s 212) [] (by simp [mid]) (by simp [mid,h214])
  have he : Function.update (Function.update mid 221 []) 214
      (List.replicate (s 212).length false++[]) =
      Function.update s 214 (List.replicate n false) := by
    ext i
    by_cases h0 : i=221 <;> by_cases h1 : i=214 <;>
      simp_all [mid]
  rw [he] at h2
  have h := h1.seq h2
  convert h using 1 ; simp only [hn] ; omega

def bits (n j : ℕ) : List Bool :=
  List.replicate j false ++ true :: List.replicate (n-j-1) false

private theorem zero_split (n j : ℕ) (hj : j < n) :
    List.replicate n false =
      List.replicate j false ++ false :: List.replicate (n-j-1) false := by
  have hn : n=j+((n-j-1)+1) := by omega
  conv_lhs => rw [hn,List.replicate_add,List.replicate_succ]

/-- Read the zero zeroPrefix, replace the selected bit, and restore the zeroPrefix. -/
abbrev selectCommand : Code :=
  .seq (takeWord 218 221 222 214 223 0 1)
    (.seq (popToken 214) (.seq (pushBit true)
      (.call (StackRoutines.transferProgram 223 214 (0 : Fin 16) 1))))

theorem select_run (s : Store) (n j : ℕ) (hj : j < n)
    (hindex : (s 218).length=j) (hmask : s 214=List.replicate n false)
    (h221 : s 221=[]) (h222 : s 222=[]) (h223 : s 223=[]) :
    ExecutesIn selectCommand (17*j+17) s (Function.update s 214 (bits n j)) := by
  let zeroPrefix := List.replicate j false
  let suffix := List.replicate (n-j-1) false
  let s1 := Function.update (Function.update s 214 (false::suffix)) 223 zeroPrefix
  let s2 := Function.update (Function.update s 214 suffix) 223 zeroPrefix
  let s3 := Function.update (Function.update s 214 (true::suffix)) 223 zeroPrefix
  have h1 : ExecutesIn (takeWord 218 221 222 214 223 0 1) (14*j+11) s s1 := by
    intro regs
    refine ⟨14*j+11,readRegs regs 0 1 none,le_rfl,?_⟩
    simpa [afterTake,zeroPrefix,suffix,s1,h223] using
      takeWord_eval (⟨regs,s⟩ : Data) 218 221 222 214 223 0 1
        (by decide) (by decide) zeroPrefix (false::suffix)
        (by simpa [zeroPrefix,suffix,hmask] using zero_split n j hj) h221 h222
        (by simpa [zeroPrefix] using hindex)
  have h2 : ExecutesIn (popToken 214) 1 s1 s2 := by
    have h := popToken_run 214 s1 false suffix (by simp [s1])
    convert h using 1
    ext i
    by_cases h0 : i=214 <;> by_cases h1 : i=223 <;>
      simp [s1,s2,h0,h1]
  have h3 : ExecutesIn (pushBit true) 2 s2 s3 := by
    have h := pushBit_run s2 true
    convert h using 1
    ext i
    by_cases h0 : i=214 <;> by_cases h1 : i=223 <;>
      simp [s2,s3,h0,h1]
  have h4 : ExecutesIn (.call (StackRoutines.transferProgram 223 214 (0 : Fin 16) 1))
      (3*j+3) s3 (Function.update s 214 (bits n j)) := by
    intro regs
    have h := transfer_eval (⟨regs,s3⟩ : Data) 223 214 0 1 (by decide) (by decide)
    have he : afterTransfer (⟨regs,s3⟩ : Data) 223 214 0 1 =
        (⟨readRegs regs 0 1 none,Function.update s 214 (bits n j)⟩ : Data) := by
      apply SubexpScanPrimitives.state_ext
      · rfl
      · ext i
        by_cases h0 : i=214 <;> by_cases h1 : i=223 <;>
          simp_all [afterTransfer,StackRoutines.transferStacks,s3,zeroPrefix,suffix,bits,
          Function.update_apply]
    rw [he] at h
    exact ⟨3*j+3,readRegs regs 0 1 none,le_rfl,by simpa [s3,zeroPrefix] using h⟩
  have h := h1.seq (h2.seq (h3.seq h4))
  convert h using 1 ; omega

abbrev command : Code := .seq zeroCommand selectCommand

theorem command_run (s : Store) (n j : ℕ) (hj : j < n)
    (hn : (s 212).length=n) (hindex : (s 218).length=j)
    (h120 : s 120=[]) (h214 : s 214=[])
    (h221 : s 221=[]) (h222 : s 222=[]) (h223 : s 223=[]) :
    ExecutesIn command (11*n+17*j+24) s (Function.update s 214 (bits n j)) := by
  have h1 := zero_run s n hn h120 h221 h214
  have h2 := select_run (Function.update s 214 (List.replicate n false)) n j hj
    (by simpa using hindex) (by simp) (by simpa using h221)
    (by simpa using h222) (by simpa using h223)
  have h := h1.seq h2
  simpa only [Function.update_idem,show 11*n+7+(17*j+17)=11*n+17*j+24 by omega] using h

/-- One native step advances the caller's original-coordinate unary index. -/
abbrev advance : Code := Subexp.TupleProgram.pushConst 218 0 true

theorem advance_run (s : Store) : ExecutesIn advance 2 s
    (Function.update s 218 (true::s 218)) := by
  intro regs
  exact ⟨2,Function.update regs 0 true,le_rfl,
    Subexp.TupleProgram.pushConst_eval (218 : Fin 256) (0 : Fin 16) true (⟨regs,s⟩ : Data)⟩

@[simp] theorem bits_length (n j : ℕ) (hj : j < n) : (bits n j).length=n := by
  simp only [bits,List.length_append,List.length_replicate,List.length_cons]
  omega

theorem bits_eq_ofFn (n j : ℕ) (hj : j < n) :
    bits n j=List.ofFn (fun v : Fin n => decide (v.val=j)) := by
  apply List.ext_getElem
  · simp [hj]
  · intro i hi h'
    have hin : i < n := by simpa only [bits_length n j hj] using hi
    by_cases hij : i < j
    · simp [bits,List.getElem_append_left,hij,show i≠j by omega]
    · have hle : j ≤ i := by omega
      by_cases heq : i=j
      · subst i
        simp [bits,List.getElem_append_right]
      · have hlt : j < i := by omega
        simp [bits,List.getElem_append_right,hle,List.getElem_cons,
          show i-j≠0 by omega,heq]

theorem bits_eq_encodeMask {n : ℕ} (v : Fin n) :
    bits n v.val=Squarefree.encodeMask {v} := by
  rw [bits_eq_ofFn n v.val v.isLt]
  congr 1
  funext w
  simp [Fin.ext_iff]

theorem singleton_run {n : ℕ} (s : Store) (v : Fin n)
    (hn : (s 212).length=n) (hindex : (s 218).length=v.val)
    (h120 : s 120=[]) (h214 : s 214=[])
    (h221 : s 221=[]) (h222 : s 222=[]) (h223 : s 223=[]) :
    ExecutesIn command (11*n+17*v.val+24) s
      (Function.update s 214 (Squarefree.encodeMask {v})) := by
  simpa only [bits_eq_encodeMask] using
    command_run s n v.val v.isLt hn hindex h120 h214 h221 h222 h223

abbrev program := compiled command 212 214

theorem primitive_singleton {n : ℕ} (s : Store) (v : Fin n)
    (hn : (s 212).length=n) (hindex : (s 218).length=v.val)
    (h120 : s 120=[]) (h214 : s 214=[])
    (h221 : s 221=[]) (h222 : s 222=[]) (h223 : s 223=[])
    (regs : Fin 16 → Bool) :
    ∃ rr, Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(28*n+25))
      (primitiveCfg program ((⟨regs,s⟩ : Data).withPC (some program.entry)))
      (primitiveCfg program ((⟨rr,Function.update s 214 (Squarefree.encodeMask {v})⟩ : Data).withPC none)) := by
  obtain ⟨m,rr,hm,he⟩ := singleton_run s v hn hindex h120 h214 h221 h222 h223 regs
  have hr : RunsIn program (28*n+25)
      ((⟨regs,s⟩ : Data).withPC (some program.entry))
      ((⟨rr,Function.update s 214 (Squarefree.encodeMask {v})⟩ : Data).withPC none) :=
    ⟨m+1,by have hv := v.isLt; omega,compiled_halt_trace he 212 214⟩
  exact ⟨rr,primitive_execution program hr⟩

end SubexponentialSAT.SqrtLog.PerturbationMaskProgram

end OAI.Algorithms
