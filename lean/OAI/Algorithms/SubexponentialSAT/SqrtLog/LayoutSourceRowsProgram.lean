import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramFrame
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding

namespace OAI.Algorithms

/-! Complete finite controllers for source fiber sums and ambient source-row
serialization. Parameters are actual finite programs with paid contracts. -/

/-! A runtime owner-fiber fold of actual serialized polynomial sources. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

attribute [local simp] Fin.coe_ofNat_eq_mod

def indexBytes (ids : List ℕ) : List Bool := ids.flatMap Encoding.encodeNat

def sumBytes (source : ℕ → List Bool) (ids : List ℕ) : List Bool :=
  ids.flatMap (fun i => source i ++ [true,false])

def fiberState (base : Store) (ids : List ℕ) (acc : List Bool) : Store :=
  Function.update (Function.update (Function.update base 328
    (List.replicate ids.length true)) 329 (indexBytes ids)) 333 acc

def fiberPorts : UnaryForPrograms.Ports 16 340 := ⟨328,14,15⟩
def fiberBody (source : Code) : Code :=
  .seq readIndex (.seq source (.seq appendSource (clear 305)))
def fiberLoop (source : Code) : Code := UnaryForPrograms.forCmd fiberPorts (fiberBody source)

/-- The source provider is an actual fixed command. Its contract includes the
complete caller state and the runtime incidence index on305. -/
def SourceSpec (source : Code) (base : Store) (bytes : ℕ → List Bool)
    (I K : ℕ) : Prop :=
  ∀ i, i  ≤  I → ∀ ids acc,
    ExecutesIn source K (Function.update (fiberState base ids acc) 305 (List.replicate i true))
      (Function.update (Function.update (fiberState base ids acc) 305
        (List.replicate i true)) 287 (bytes i))

theorem fiberBody_run (source : Code) (base : Store) (bytes : ℕ → List Bool)
    (I K L : ℕ) (spec : SourceSpec source base bytes I K)
    (hL : ∀ i, i  ≤  I → (bytes i).length  ≤  L)
    (h305 : base 305=[]) (h287 : base 287=[])
    (i : ℕ) (hi : i  ≤  I) (ids : List ℕ) (acc : List Bool) :
    ExecutesIn (fiberBody source) (K+5*I+3*L+13)
      (Function.update (fiberState base (i::ids) acc) 328 (List.replicate ids.length true))
      (fiberState base ids ((bytes i++[true,false]).reverse++acc)) := by
  let s := Function.update (fiberState base (i::ids) acc) 328 (List.replicate ids.length true)
  let t := Function.update (fiberState base ids acc) 305 (List.replicate i true)
  let u := Function.update t 287 (bytes i)
  have h1 := readIndex_run s i (indexBytes ids)
    (by simp [s,fiberState,indexBytes]) (by simp [s,fiberState,h305])
  have he1 : Function.update (Function.update s 329 (indexBytes ids)) 305
      (List.replicate i true)=t := by
    funext j
    by_cases h328 : j=328 <;> by_cases h329 : j=329 <;>
      by_cases h333 : j=333 <;> by_cases hh305 : j=305 <;>
      simp [s,t,fiberState,Function.update_apply,h328,h329,h333,hh305]
  rw [he1] at h1
  have h2 : ExecutesIn source K t u := spec i hi ids acc
  have h3 := appendSource_run u
  have h4 := clear_run 305 (appendResult u)
  have he4 : Function.update (appendResult u) 305 []=
      fiberState base ids ((bytes i++[true,false]).reverse++acc) := by
    funext j
    by_cases h328 : j=328 <;> by_cases h329 : j=329 <;>
      by_cases h333 : j=333 <;> by_cases hh305 : j=305 <;> by_cases hh287 : j=287 <;>
      simp [u,t,appendResult,fiberState,Function.update_apply,h328,h329,h333,hh305,hh287,
        h305,h287,List.reverse_append,List.append_assoc]
  rw [he4] at h4
  have h := h1.seq (h2.seq (h3.seq h4))
  apply h.mono
  have hl := hL i hi
  simp only [u,t,Function.update_same]
  simp [appendResult,fiberState]
  omega

theorem fiber_popped (base : Store) (ids : List ℕ) (acc : List Bool)
    (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped fiberPorts (⟨regs,fiberState base ids acc⟩ : Data) =
      (⟨readRegs regs 14 15 (List.replicate ids.length true).head?,
        Function.update (fiberState base ids acc) 328
          (List.replicate ids.length true).tail⟩ : Data) := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped,fiberPorts,fiberState]
  · simp [UnaryForPrograms.popped,fiberPorts,fiberState]

theorem fiber_visits (source : Code) (base : Store) (bytes : ℕ → List Bool)
    (I K L : ℕ) (spec : SourceSpec source base bytes I K)
    (hL : ∀ i, i  ≤  I → (bytes i).length  ≤  L)
    (h305 : base 305=[]) (h287 : base 287=[])
    (ids : List ℕ) (hI : ∀ i ∈ ids, i  ≤  I) (acc : List Bool) (regs : Fin 16 → Bool) :
    ∃ costs n rf, n  ≤  ids.length*(K+5*I+3*L+15)+2 ∧
      UnaryForPrograms.Visits fiberPorts (fiberBody source) costs n
        (⟨regs,fiberState base ids acc⟩ : Data)
        (⟨rf,fiberState base [] ((sumBytes bytes ids).reverse++acc)⟩ : Data) := by
  induction ids generalizing acc regs with
  | nil =>
    refine ⟨[],2,readRegs regs 14 15 none,by simp,?_⟩
    have he : Function.update (fiberState base [] acc) 328 []=fiberState base [] acc := by
      funext j
      by_cases hj : j=328 <;> simp [fiberState,Function.update_apply,hj]
    simpa [fiber_popped,he,sumBytes] using
      UnaryForPrograms.Visits.done (p := fiberPorts) (body := fiberBody source)
        (⟨regs,fiberState base [] acc⟩ : Data) (by simp [fiberPorts,fiberState])
  | cons i ids ih =>
    obtain ⟨nb,rb,hnb,hb⟩ := fiberBody_run source base bytes I K L spec hL h305 h287
      i (hI i (by simp)) ids acc (readRegs regs 14 15 (some true))
    obtain ⟨costs,nt,rt,hnt,ht⟩ := ih (by intro j hj; exact hI j (by simp [hj]))
      ((bytes i++[true,false]).reverse++acc) rb
    refine ⟨nb::costs,nb+nt+2,rt,?_,?_⟩
    · simp only [List.length_cons]; nlinarith
    · have h := UnaryForPrograms.Visits.step (p := fiberPorts) (body := fiberBody source)
        (d := (⟨regs,fiberState base (i::ids) acc⟩ : Data))
        (by simp [fiberPorts,fiberState])
        (by simpa [fiber_popped,List.replicate_succ] using hb)
        (by simp [fiberState,fiberPorts,UnaryForPrograms.popped]) ht
      simpa [sumBytes,List.reverse_append,List.append_assoc] using h

theorem fiberLoop_run (source : Code) (base : Store) (bytes : ℕ → List Bool)
    (I K L : ℕ) (spec : SourceSpec source base bytes I K)
    (hL : ∀ i, i  ≤  I → (bytes i).length  ≤  L)
    (h305 : base 305=[]) (h287 : base 287=[])
    (ids : List ℕ) (hI : ∀ i ∈ ids, i  ≤  I) (acc : List Bool) :
    ExecutesIn (fiberLoop source) (ids.length*(K+5*I+3*L+15)+2)
      (fiberState base ids acc)
      (fiberState base [] ((sumBytes bytes ids).reverse++acc)) := by
  intro regs
  obtain ⟨costs,n,rf,hn,he⟩ := fiber_visits source base bytes I K L spec hL h305 h287 ids hI acc regs
  exact ⟨n,rf,hn,he.eval⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def ownerRegisters : Fin 5 → Fin 16 := Fin.castAdd 11
theorem ownerRegisters_injective : Function.Injective ownerRegisters := Fin.castAdd_injective _ _
def ownerStacks : Fin 11 → Fin 340 := ![320,337,321,322,323,324,325,326,327,328,329]
theorem ownerStacks_injective : Function.Injective ownerStacks := by decide
def findOwner : Code := .call (ProgramLinking.liftProgram
  LayoutOwnerFiberProgram.program ownerRegisters ownerStacks)

def ownerResult (a : Data) (regs : Fin 16 → Bool) (is : List ℕ) : Data :=
  ⟨regs,Function.update (Function.update a.stacks 328 (LayoutOwnerFiberProgram.unary is.length)) 329 (LayoutOwnerFiberProgram.encodeIndices is)⟩

theorem findOwner_eval (a : Data) (query : ℕ) (ps : List (ℕ × ℕ))
    (hq : a.stacks 320=LayoutOwnerFiberProgram.unary query)
    (hs : a.stacks 337=LayoutOwnerFiberProgram.stream ps)
    (he : ∀ i : Fin 11, 2 ≤ i.val → a.stacks (ownerStacks i)=[]) :
    ∃ n  ≤  LayoutOwnerFiberProgram.budget query ps, ∃ rf,
      Eval findOwner n a
        (ownerResult a rf (LayoutOwnerFiberProgram.fiberIndices query 0 ps)) := by
  obtain ⟨rf,n,hn,ht⟩ := LayoutOwnerFiberProgram.program_runs query ps (a.regs ∘ ownerRegisters)
  have hi : projectState ownerRegisters ownerStacks a=
      LayoutOwnerFiberProgram.data (a.regs ∘ ownerRegisters) (LayoutOwnerFiberProgram.unary query)
        (LayoutOwnerFiberProgram.stream ps) [] [] [] [] [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hh : 2 ≤ i.val
      · have hz := he i hh
        fin_cases i <;> simp_all [LayoutOwnerFiberProgram.data,ownerStacks]
      · fin_cases i <;> simp_all [LayoutOwnerFiberProgram.data,ownerStacks]
  rw [←hi] at ht
  have hc := eval_call_from_state LayoutOwnerFiberProgram.program ownerRegisters ownerStacks a
    ownerRegisters_injective ownerStacks_injective ht
  let out := LayoutOwnerFiberProgram.data rf (LayoutOwnerFiberProgram.unary query) (LayoutOwnerFiberProgram.stream ps)
    [] [] [] [] [] [] [] (LayoutOwnerFiberProgram.unary (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length)
      (LayoutOwnerFiberProgram.encodeIndices (LayoutOwnerFiberProgram.fiberIndices query 0 ps))
  let rr := (embedState ownerRegisters ownerStacks a out).regs
  have ho : embedState ownerRegisters ownerStacks a out=
      ownerResult a rr (LayoutOwnerFiberProgram.fiberIndices query 0 ps) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hp : ∃ j, ownerStacks j=i
      · obtain ⟨j,rfl⟩ := hp
        have hh := embedState_stack ownerRegisters ownerStacks a out ownerStacks_injective j
        exact hh.trans (by
          by_cases hj : 2 ≤ j.val
          · have hz := he j hj
            fin_cases j <;> simp_all [out,LayoutOwnerFiberProgram.data,ownerStacks]
          · fin_cases j <;> simp_all [out,LayoutOwnerFiberProgram.data,ownerStacks])
      · have hh := embedState_stack_frame ownerRegisters ownerStacks a out i hp
        have h214 : i≠329 := fun h => hp ⟨10,h.symm⟩
        have h215 : i≠328 := fun h => hp ⟨9,h.symm⟩
        exact hh.trans (by simp [h214,h215])
  change Eval findOwner n a (embedState ownerRegisters ownerStacks a out) at hc
  rw [ho] at hc
  exact ⟨n,hn,rr,hc⟩


def frameRegisters : Fin 3 → Fin 16 := Fin.castAdd 13
def frameStacks : Fin 2 → Fin 340 := ![330,334]
theorem frameRegisters_injective : Function.Injective frameRegisters := Fin.castAdd_injective _ _
theorem frameStacks_injective : Function.Injective frameStacks := by decide

def frameRow : Code := .call (ProgramLinking.liftProgram
  Squarefree.Program.frameEmitProgram frameRegisters frameStacks)

theorem frameRow_run (s : Store) :
    ExecutesIn frameRow (4*(s 330).length+6) s
      (Function.update (Function.update s 330 []) 334 (Encoding.frame (s 330).reverse++s 334)) := by
  intro regs
  let a : Data := ⟨regs,s⟩
  let small := projectState frameRegisters frameStacks a
  obtain ⟨rf,ht⟩ := Squarefree.Program.frameEmit_trace (s 330).reverse (s 334) small.regs
  have heq : Squarefree.Program.frameData small.regs ((s 330).reverse).reverse (s 334)=small := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [a,frameStacks]
  rw [heq] at ht
  have he := eval_call_from_state Squarefree.Program.frameEmitProgram frameRegisters frameStacks a
    frameRegisters_injective frameStacks_injective ht
  let out := Squarefree.Program.frameData rf [] (Encoding.frame (s 330).reverse++s 334)
  have hs : out.stacks=Function.update (Function.update small.stacks 0 []) 1
      (Encoding.frame (s 330).reverse++s 334) := by
    funext i; fin_cases i <;> simp [out,Squarefree.Program.frameData]
  have hh : (embedState frameRegisters frameStacks a out).stacks =
      Function.update (Function.update s 330 []) 334 (Encoding.frame (s 330).reverse++s 334) := by
    change Function.extend frameStacks out.stacks s = _
    rw [hs,ProgramLinking.extend_update frameStacks_injective,
      ProgramLinking.extend_update frameStacks_injective]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project frameRegisters frameStacks a frameRegisters_injective frameStacks_injective)
    change Function.extend frameStacks small.stacks s=s at hb
    rw [hb]
    rfl
  change Eval frameRow (4*(s 330).reverse.length+6) a
    (embedState frameRegisters frameStacks a out) at he
  have hout : embedState frameRegisters frameStacks a out=
      (⟨(embedState frameRegisters frameStacks a out).regs,
        Function.update (Function.update s 330 []) 334
          (Encoding.frame (s 330).reverse++s 334)⟩ : Data) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact hh
  rw [hout] at he
  exact ⟨4*(s 330).length+6,(embedState frameRegisters frameStacks a out).regs,
    le_rfl,by simpa [a] using he⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def rowRecord (bits : List Bool) : List Bool := true::Encoding.frame bits

def emitRow : Code := .seq (transfer 240 330)
  (.seq frameRow (.seq (push 334 true) (transfer 334 332)))

theorem emitRow_run (s : Store) (h330 : s 330=[]) (h334 : s 334=[]) :
    ExecutesIn emitRow (13*(s 240).length+20) s
      (Function.update (Function.update s 240 []) 332 ((rowRecord (s 240)).reverse++s 332)) := by
  let s1 := Function.update (Function.update s 240 []) 330 (s 240).reverse
  let s2 := Function.update (Function.update s1 330 []) 334 (Encoding.frame (s 240))
  let s3 := Function.update s2 334 (rowRecord (s 240))
  have h1 : ExecutesIn (transfer 240 330) (3*(s 240).length+3) s s1 := by
    simpa [s1,h330] using transfer_run 240 330 s (by decide)
  have h2 : ExecutesIn frameRow (4*(s 240).length+6) s1 s2 := by
    simpa [s1,s2,h334] using frameRow_run s1
  have h3 : ExecutesIn (push 334 true) 2 s2 s3 := by
    simpa [s3,s2,rowRecord] using push_run 334 true s2
  have h4 := transfer_run 334 332 s3 (by decide)
  have he : Function.update (Function.update s3 334 []) 332
      ((s3 334).reverse++s3 332)=
        Function.update (Function.update s 240 []) 332 ((rowRecord (s 240)).reverse++s 332) := by
    funext i
    by_cases h240 : i=240 <;> by_cases h332 : i=332 <;>
      by_cases hh330 : i=330 <;> by_cases hh334 : i=334 <;>
      simp [s3,s2,s1,h240,h332,hh330,hh334,h330,h334]
  rw [he] at h4
  apply (h1.seq (h2.seq (h3.seq h4))).mono
  simp [s3,s2,rowRecord]
  omega

def finishRows : Code := .seq (push 332 false) (transfer 332 205)

theorem finishRows_run (s : Store) (h205 : s 205=[]) :
    ExecutesIn finishRows (3*(s 332).length+8) s
      (Function.update (Function.update s 332 []) 205 ((s 332).reverse++[false])) := by
  have h1 := push_run 332 false s
  have h2 := transfer_run 332 205 (Function.update s 332 (false::s 332)) (by decide)
  have he : Function.update (Function.update (Function.update s 332 (false::s 332)) 332 [])
      205 ((Function.update s 332 (false::s 332) 332).reverse ++
      (Function.update s 332 (false::s 332) 205))=
        Function.update (Function.update s 332 []) 205 ((s 332).reverse++[false]) := by
    simp [h205,List.reverse_cons]
  rw [he] at h2
  exact (h1.seq h2).mono (by simp; omega)

def rowState (base : Store) (j : ℕ) (remaining acc : List Bool) : Store :=
  Function.update (Function.update (Function.update base 320 (List.replicate j true))
    331 remaining) 332 acc

def rowBytes (value : ℕ → List Bool) (j n : ℕ) : List Bool :=
  ((List.range' j n).map (fun i => rowRecord (value i))).flatten

@[simp] theorem rowBytes_zero (value : ℕ → List Bool) (j : ℕ) : rowBytes value j 0=[] := by
  simp [rowBytes]

theorem rowBytes_succ (value : ℕ → List Bool) (j n : ℕ) :
    rowBytes value j (n+1)=rowRecord (value j)++rowBytes value (j+1) n := by
  simp [rowBytes,List.range'_succ]

theorem rowBytes_length (value : ℕ → List Bool) (W : ℕ)
    (hw : ∀ j, (value j).length=W) (j n : ℕ) :
    (rowBytes value j n).length=n*(2*W+2) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih => rw [rowBytes_succ,List.length_append,ih]; simp [rowRecord,hw]; ring

def rowPorts : UnaryForPrograms.Ports 16 340 := ⟨331,14,15⟩
def rowBody (callback : Code) : Code := .seq callback (.seq emitRow (push 320 true))
def rowLoop (callback : Code) : Code := UnaryForPrograms.forCmd rowPorts (rowBody callback)
def rowsCommand (callback : Code) : Code :=
  .seq (copy 212 331) (.seq (rowLoop callback) (.seq (clear 320) finishRows))
def rowsProgram (callback : Code) := compiled (rowsCommand callback) 212 205

def RowSpec (callback : Code) (base : Store) (value : ℕ → List Bool) (N K : ℕ) : Prop :=
  ∀ j, j < N → ∀ remaining acc,
    ExecutesIn callback K (rowState base j remaining acc)
      (Function.update (rowState base j remaining acc) 240 (value j))

theorem rowBody_run (callback : Code) (base : Store) (value : ℕ → List Bool)
    (N K W : ℕ) (spec : RowSpec callback base value N K)
    (hw : ∀ j, (value j).length=W) (h240 : base 240=[])
    (h330 : base 330=[]) (h334 : base 334=[])
    (j : ℕ) (hj : j < N) (remaining acc : List Bool) :
    ExecutesIn (rowBody callback) (K+13*W+22) (rowState base j remaining acc)
      (rowState base (j+1) remaining ((rowRecord (value j)).reverse++acc)) := by
  let s := rowState base j remaining acc
  let s1 := Function.update s 240 (value j)
  let s2 := rowState base j remaining ((rowRecord (value j)).reverse++acc)
  have h1 : ExecutesIn callback K s s1 := spec j hj remaining acc
  have he2 : Function.update (Function.update s1 240 []) 332
      ((rowRecord (s1 240)).reverse++s1 332)=s2 := by
    funext i
    by_cases h320 : i=320 <;> by_cases h331 : i=331 <;>
      by_cases h332 : i=332 <;> by_cases hh240 : i=240 <;>
      simp [s2,s1,s,rowState,h320,h331,h332,hh240,h240]
  have h2 : ExecutesIn emitRow (13*W+20) s1 s2 := by
    have h := emitRow_run s1 (by simp [s1,s,rowState,h330]) (by simp [s1,s,rowState,h334])
    rw [he2] at h
    simpa [s1,hw] using h
  have h3 := push_run 320 true s2
  have he3 : Function.update s2 320 (true::s2 320)=
      rowState base (j+1) remaining ((rowRecord (value j)).reverse++acc) := by
    funext i
    by_cases h320 : i=320 <;> by_cases h331 : i=331 <;> by_cases h332 : i=332 <;>
      simp [s2,rowState,h320,h331,h332,List.replicate_succ]
  rw [he3] at h3
  exact (h1.seq (h2.seq h3)).mono (by omega)

theorem row_popped (base : Store) (j : ℕ) (remaining acc : List Bool) (regs : Fin 16 → Bool) :
    UnaryForPrograms.popped rowPorts (⟨regs,rowState base j remaining acc⟩ : Data)=
      (⟨readRegs regs 14 15 remaining.head?,rowState base j remaining.tail acc⟩ : Data) := by
  apply SubexpScanPrimitives.state_ext
  · simp [UnaryForPrograms.popped,rowPorts,rowState]
  · funext i
    by_cases h320 : i=320 <;> by_cases h331 : i=331 <;> by_cases h332 : i=332 <;>
      simp [UnaryForPrograms.popped,rowPorts,rowState,h320,h331,h332]

theorem row_visits (callback : Code) (base : Store) (value : ℕ → List Bool)
    (N K W : ℕ) (spec : RowSpec callback base value N K)
    (hw : ∀ j, (value j).length=W) (h240 : base 240=[])
    (h330 : base 330=[]) (h334 : base 334=[])
    (remaining acc : List Bool) (j : ℕ) (hj : j+remaining.length ≤ N) (regs : Fin 16 → Bool) :
    ∃ costs n rf, n ≤ remaining.length*(K+13*W+24)+2 ∧
      UnaryForPrograms.Visits rowPorts (rowBody callback) costs n
        (⟨regs,rowState base j remaining acc⟩ : Data)
        (⟨rf,rowState base (j+remaining.length) []
          ((rowBytes value j remaining.length).reverse++acc)⟩ : Data) := by
  induction remaining generalizing j acc regs with
  | nil =>
    refine ⟨[],2,readRegs regs 14 15 none,by simp,?_⟩
    simpa only [row_popped,List.head?_nil,List.tail_nil,List.length_nil,
      Nat.add_zero,rowBytes_zero,List.reverse_nil,List.nil_append] using
      UnaryForPrograms.Visits.done (p := rowPorts) (body := rowBody callback)
        (⟨regs,rowState base j [] acc⟩ : Data) (by simp [rowState,rowPorts])
  | cons b remaining ih =>
    obtain ⟨nb,rb,hnb,hb⟩ := rowBody_run callback base value N K W spec hw h240 h330 h334
      j (by simp only [List.length_cons] at hj; omega) remaining acc (readRegs regs 14 15 (some b))
    obtain ⟨costs,nt,rt,hnt,ht⟩ := ih ((rowRecord (value j)).reverse++acc) (j+1)
      (by simp only [List.length_cons] at hj; omega) rb
    refine ⟨nb::costs,nb+nt+2,rt,?_,?_⟩
    · simp only [List.length_cons]; nlinarith
    · have h := UnaryForPrograms.Visits.step (p := rowPorts) (body := rowBody callback)
        (d := (⟨regs,rowState base j (b::remaining) acc⟩ : Data))
        (by simp [rowState,rowPorts])
        (by simpa only [row_popped,List.head?_cons,List.tail_cons] using hb)
        (by simp [rowState,rowPorts,UnaryForPrograms.popped]) ht
      simpa only [List.length_cons,rowBytes_succ,List.reverse_append,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem rowLoop_run (callback : Code) (base : Store) (value : ℕ → List Bool)
    (N K W : ℕ) (spec : RowSpec callback base value N K)
    (hw : ∀ j, (value j).length=W) (h240 : base 240=[])
    (h330 : base 330=[]) (h334 : base 334=[])
    (remaining acc : List Bool) (j : ℕ) (hj : j+remaining.length ≤ N) :
    ExecutesIn (rowLoop callback) (remaining.length*(K+13*W+24)+2)
      (rowState base j remaining acc)
      (rowState base (j+remaining.length) [] ((rowBytes value j remaining.length).reverse++acc)) := by
  intro regs
  obtain ⟨costs,n,rf,hn,he⟩ := row_visits callback base value N K W spec hw h240 h330 h334
    remaining acc j hj regs
  exact ⟨n,rf,hn,he.eval⟩

theorem rowsCommand_run (callback : Code) (base : Store) (value : ℕ → List Bool)
    (N K W : ℕ) (spec : RowSpec callback base value N K)
    (hw : ∀ j, (value j).length=W) (hN : (base 212).length=N)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[])
    (h320 : base 320=[]) (h331 : base 331=[]) (h332 : base 332=[])
    (h205 : base 205=[]) (h339 : base 339=[]) :
    ExecutesIn (rowsCommand callback) (N*(K+19*W+39)+18) base
      (Function.update base 205 (rowBytes value 0 N++[false])) := by
  let s1 := rowState base 0 (base 212) []
  let s2 := rowState base N [] (rowBytes value 0 N).reverse
  let s3 := Function.update s2 320 []
  have he1 : Function.update base 331 (base 212++base 331)=s1 := by
    funext i
    by_cases hi320 : i=320 <;> by_cases hi331 : i=331 <;> by_cases hi332 : i=332 <;>
      simp [s1,rowState,hi320,hi331,hi332,h320,h331,h332]
  have h1 : ExecutesIn (copy 212 331) (7*N+5) base s1 := by
    have h := copy_run 212 331 base (by decide) (by decide) (by decide) h339
    rw [he1,hN] at h
    exact h
  have h2 : ExecutesIn (rowLoop callback) (N*(K+13*W+24)+2) s1 s2 := by
    have h := rowLoop_run callback base value N K W spec hw h240 h330 h334
      (base 212) [] 0 (by omega)
    simpa only [s1,s2,hN,Nat.zero_add,List.append_nil] using h
  have h3 : ExecutesIn (clear 320) (2*N+3) s2 s3 := by
    simpa [s2,rowState,s3] using clear_run 320 s2
  have he4 : Function.update (Function.update s3 332 []) 205
      ((s3 332).reverse++[false])=Function.update base 205 (rowBytes value 0 N++[false]) := by
    funext i
    by_cases hi320 : i=320 <;> by_cases hi331 : i=331 <;>
      by_cases hi332 : i=332 <;> by_cases hi205 : i=205 <;>
      simp [s3,s2,rowState,hi320,hi331,hi332,hi205,h320,h331,h332]
  have h4 : ExecutesIn finishRows (3*(N*(2*W+2))+8) s3
      (Function.update base 205 (rowBytes value 0 N++[false])) := by
    have h := finishRows_run s3 (by simp [s3,s2,rowState,h205])
    rw [he4] at h
    simpa [s3,s2,rowState,rowBytes_length value W hw] using h
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by ring_nf; omega)

theorem rowsProgram_runsIn (callback : Code) (base : Store) (value : ℕ → List Bool)
    (N K W : ℕ) (spec : RowSpec callback base value N K)
    (hw : ∀ j, (value j).length=W) (hN : (base 212).length=N)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[])
    (h320 : base 320=[]) (h331 : base 331=[]) (h332 : base 332=[])
    (h205 : base 205=[]) (h339 : base 339=[]) (regs : Fin 16 → Bool) :
    ∃ rf, RunsIn (rowsProgram callback) (N*(K+19*W+39)+19)
      ((⟨regs,base⟩ : Data).withPC (some (rowsProgram callback).entry))
      ((⟨rf,Function.update base 205 (rowBytes value 0 N++[false])⟩ : Data).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := rowsCommand_run callback base value N K W spec hw hN
    h240 h330 h334 h320 h331 h332 h205 h339 regs
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 212 205⟩

theorem rowBytes_encoding (value : ℕ → List Bool) (j n : ℕ) :
    rowBytes value j n++[false]=Encoding.encodeList id ((List.range' j n).map value) := by
  induction n generalizing j with
  | zero => simp [rowBytes,Encoding.encodeList]
  | succ n ih =>
      rw [rowBytes_succ,List.append_assoc,ih]
      simp [List.range'_succ,Encoding.encodeList,rowRecord]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {Witness : Type*}

def emittedBytes (encode : Witness → List Bool) (ws : List Witness) : List Bool :=
  ws.flatMap (fun w => encode w++[true,false])

/-- Witnesses may be selected by the concrete run. Every result carries its
semantic relation, exact serialization, and a byte bound. -/
def RelSourceSpec (source : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (I K L : ℕ) : Prop :=
  ∀ i, i ≤ I → ∀ ids acc regs, ∃ w n rf,
    R i w ∧ (encode w).length ≤ L ∧ n ≤ K ∧
    Eval source n (⟨regs,Function.update (fiberState base ids acc) 305
      (List.replicate i true)⟩ : Data)
      (⟨rf,Function.update (Function.update (fiberState base ids acc) 305
        (List.replicate i true)) 287 (encode w)⟩ : Data)

theorem finishSource_run (base : Store) (h305 : base 305=[]) (h287 : base 287=[])
    (i : ℕ) (ids : List ℕ) (acc bytes : List Bool) :
    ExecutesIn (.seq appendSource (clear 305)) (3*bytes.length+2*i+10)
      (Function.update (Function.update (fiberState base ids acc) 305
        (List.replicate i true)) 287 bytes)
      (fiberState base ids ((bytes++[true,false]).reverse++acc)) := by
  let u := Function.update (Function.update (fiberState base ids acc) 305
    (List.replicate i true)) 287 bytes
  have h1 := appendSource_run u
  have h2 := clear_run 305 (appendResult u)
  have he : Function.update (appendResult u) 305 []=
      fiberState base ids ((bytes++[true,false]).reverse++acc) := by
    funext j
    by_cases h328 : j=328 <;> by_cases h329 : j=329 <;>
      by_cases h333 : j=333 <;> by_cases hh305 : j=305 <;> by_cases hh287 : j=287 <;>
      simp [u,appendResult,fiberState,Function.update_apply,h328,h329,h333,hh305,hh287,
        h305,h287,List.reverse_append,List.append_assoc]
  rw [he] at h2
  apply (h1.seq h2).mono
  simp [u,appendResult,fiberState]
  omega

theorem fiberBody_rel (source : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (I K L : ℕ) (spec : RelSourceSpec source base encode R I K L)
    (h305 : base 305=[]) (h287 : base 287=[])
    (i : ℕ) (hi : i ≤ I) (ids : List ℕ) (acc : List Bool) (regs : Fin 16 → Bool) :
    ∃ w n rf, R i w ∧ n ≤ K+5*I+3*L+13 ∧
      Eval (fiberBody source) n
        (⟨regs,Function.update (fiberState base (i::ids) acc) 328
          (List.replicate ids.length true)⟩ : Data)
        (⟨rf,fiberState base ids ((encode w++[true,false]).reverse++acc)⟩ : Data) := by
  let s := Function.update (fiberState base (i::ids) acc) 328 (List.replicate ids.length true)
  let t := Function.update (fiberState base ids acc) 305 (List.replicate i true)
  have h1 := readIndex_run s i (indexBytes ids)
    (by simp [s,fiberState,indexBytes]) (by simp [s,fiberState,h305])
  have he1 : Function.update (Function.update s 329 (indexBytes ids)) 305
      (List.replicate i true)=t := by
    funext j
    by_cases h328 : j=328 <;> by_cases h329 : j=329 <;>
      by_cases h333 : j=333 <;> by_cases hh305 : j=305 <;>
      simp [s,t,fiberState,Function.update_apply,h328,h329,h333,hh305]
  rw [he1] at h1
  obtain ⟨n1,r1,hn1,he1⟩ := h1 regs
  obtain ⟨w,n2,r2,hw,hl,hn2,he2⟩ := spec i hi ids acc r1
  obtain ⟨n3,r3,hn3,he3⟩ := finishSource_run base h305 h287 i ids acc (encode w) r2
  exact ⟨w,n1+(n2+n3),r3,hw,by omega,he1.seq (he2.seq he3)⟩

theorem fiber_visits_rel (source : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (I K L : ℕ) (spec : RelSourceSpec source base encode R I K L)
    (h305 : base 305=[]) (h287 : base 287=[])
    (ids : List ℕ) (hI : ∀ i∈ids, i ≤ I) (acc : List Bool) (regs : Fin 16 → Bool) :
    ∃ ws costs n rf, List.Forall₂ R ids ws ∧ n ≤ ids.length*(K+5*I+3*L+15)+2 ∧
      UnaryForPrograms.Visits fiberPorts (fiberBody source) costs n
        (⟨regs,fiberState base ids acc⟩ : Data)
        (⟨rf,fiberState base [] ((emittedBytes encode ws).reverse++acc)⟩ : Data) := by
  induction ids generalizing acc regs with
  | nil =>
    refine ⟨[],[],2,readRegs regs 14 15 none,List.Forall₂.nil,by simp,?_⟩
    have he : Function.update (fiberState base [] acc) 328 []=fiberState base [] acc := by
      funext j
      by_cases hj : j=328 <;> simp [fiberState,Function.update_apply,hj]
    simpa [fiber_popped,he,emittedBytes] using
      UnaryForPrograms.Visits.done (p := fiberPorts) (body := fiberBody source)
        (⟨regs,fiberState base [] acc⟩ : Data) (by simp [fiberPorts,fiberState])
  | cons i ids ih =>
    obtain ⟨w,nb,rb,hw,hnb,hb⟩ := fiberBody_rel source base encode R I K L spec h305 h287
      i (hI i (by simp)) ids acc (readRegs regs 14 15 (some true))
    obtain ⟨ws,costs,nt,rt,hws,hnt,ht⟩ := ih (by intro j hj; exact hI j (by simp [hj]))
      ((encode w++[true,false]).reverse++acc) rb
    refine ⟨w::ws,nb::costs,nb+nt+2,rt,List.Forall₂.cons hw hws,?_,?_⟩
    · simp only [List.length_cons]; nlinarith
    · have h := UnaryForPrograms.Visits.step (p := fiberPorts) (body := fiberBody source)
        (d := (⟨regs,fiberState base (i::ids) acc⟩ : Data))
        (by simp [fiberPorts,fiberState])
        (by simpa [fiber_popped,List.replicate_succ] using hb)
        (by simp [fiberState,fiberPorts,UnaryForPrograms.popped]) ht
      simpa [emittedBytes,List.reverse_append,List.append_assoc] using h

theorem fiberLoop_rel (source : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (I K L : ℕ) (spec : RelSourceSpec source base encode R I K L)
    (h305 : base 305=[]) (h287 : base 287=[])
    (ids : List ℕ) (hI : ∀ i∈ids, i ≤ I) (acc : List Bool) (regs : Fin 16 → Bool) :
    ∃ ws n rf, List.Forall₂ R ids ws ∧ n ≤ ids.length*(K+5*I+3*L+15)+2 ∧
      Eval (fiberLoop source) n (⟨regs,fiberState base ids acc⟩ : Data)
        (⟨rf,fiberState base [] ((emittedBytes encode ws).reverse++acc)⟩ : Data) := by
  obtain ⟨ws,costs,n,rf,hws,hn,he⟩ := fiber_visits_rel source base encode R I K L spec
    h305 h287 ids hI acc regs
  exact ⟨ws,n,rf,hws,hn,he.eval⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {Witness : Type*}

def sourceForOwner (source : Code) : Code := .seq findOwner (.seq zeroSource (fiberLoop source))

theorem sourceForOwner_run (source : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (I K L : ℕ) (spec : RelSourceSpec source base encode R I K L)
    (query : ℕ) (ps : List (ℕ × ℕ))
    (hq : base 320=LayoutOwnerFiberProgram.unary query)
    (hs : base 337=LayoutOwnerFiberProgram.stream ps)
    (hclean : ∀ i : Fin 11, 2 ≤ i.val → base (ownerStacks i)=[])
    (h305 : base 305=[]) (h287 : base 287=[]) (h333 : base 333=[])
    (hI : ∀ i∈LayoutOwnerFiberProgram.fiberIndices query 0 ps, i ≤ I)
    (regs : Fin 16 → Bool) :
    ∃ ws n rf, List.Forall₂ R (LayoutOwnerFiberProgram.fiberIndices query 0 ps) ws ∧
      n ≤ LayoutOwnerFiberProgram.budget query ps+
        (LayoutOwnerFiberProgram.fiberIndices query 0 ps).length*(K+5*I+3*L+15)+6 ∧
      Eval (sourceForOwner source) n (⟨regs,base⟩ : Data)
        (⟨rf,Function.update base 333 ([false,false]++emittedBytes encode ws).reverse⟩ : Data) := by
  let ids := LayoutOwnerFiberProgram.fiberIndices query 0 ps
  let b := Function.update (Function.update base 328 (List.replicate ids.length true))
    329 (indexBytes ids)
  obtain ⟨n1,hn1,r1,he1⟩ := findOwner_eval (⟨regs,base⟩ : Data) query ps hq hs hclean
  have he1' : Eval findOwner n1 (⟨regs,base⟩ : Data) (⟨r1,b⟩ : Data) := by
    simpa [ownerResult,b,ids,indexBytes,LayoutOwnerFiberProgram.encodeIndices,
      LayoutOwnerFiberProgram.unary] using he1
  obtain ⟨n2,r2,hn2,he2⟩ := zeroSource_run b (by simp [b,h333]) r1
  have he2' : Eval zeroSource n2 (⟨r1,b⟩ : Data)
      (⟨r2,fiberState base ids [false,false]⟩ : Data) := by
    simpa [fiberState,b] using he2
  obtain ⟨ws,n3,r3,hr,hn3,he3⟩ := fiberLoop_rel source base encode R I K L spec
    h305 h287 ids hI [false,false] r2
  have h328 : base 328=[] := hclean 9 (by decide)
  have h329 : base 329=[] := hclean 10 (by decide)
  have hout : fiberState base [] ((emittedBytes encode ws).reverse++[false,false])=
      Function.update base 333 ([false,false]++emittedBytes encode ws).reverse := by
    funext j
    by_cases hh328 : j=328 <;> by_cases hh329 : j=329 <;> by_cases hh333 : j=333 <;>
      simp [fiberState,indexBytes,hh328,hh329,hh333,h328,h329]
  rw [hout] at he3
  exact ⟨ws,n1+(n2+n3),r3,hr,by dsimp only [ids] at hn3; omega,he1'.seq (he2'.seq he3)⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def executorPorts : Fin 256 → Fin 340 := Fin.castAdd 84
theorem executorPorts_injective : Function.Injective executorPorts := Fin.castAdd_injective _ _

def resetExecutor : Code := liftCommand SubexpDenseLiteralPadding.reset 26 26 id executorPorts

abbrev execute {l : ℕ} (p : Program 16 256 l) : Code :=
  .seq resetExecutor (.call (ProgramLinking.liftProgram p id executorPorts))

theorem resetExecutor_eval (s : Store) (regs : Fin 16 → Bool) :
    Eval resetExecutor 18 (⟨regs,s⟩ : Data) (⟨fun _ => false,s⟩ : Data) := by
  let a : Data := ⟨regs,s⟩
  have h := SubexpDenseLiteralPadding.reset_eval regs (s ∘ executorPorts)
  have he := eval_liftCommand_from_state SubexpDenseLiteralPadding.reset 26 26 id executorPorts a
    Function.injective_id executorPorts_injective h
  have hout : embedState id executorPorts a
      (⟨fun _ => false,s ∘ executorPorts⟩ : State 16 256)=(⟨fun _ => false,s⟩ : Data) := by
    apply SubexpScanPrimitives.state_ext
    · funext i
      exact embedState_register id executorPorts a _ Function.injective_id i
    · have hb := congrArg StructuredProgram.State.stacks
        (embedState_project id executorPorts a Function.injective_id executorPorts_injective)
      change Function.extend executorPorts (s ∘ executorPorts) s=s at hb ⊢
      exact hb
  rw [hout] at he
  exact he

/-- The native executor returns the plain array on240, consumes its source26,
and preserves the entire remaining caller bank. -/
theorem execute_run {l : ℕ} (p : Program 16 256 l) (K : ℕ) (s : Store) (bits : List Bool)
    (hrun : ∃ rf, RunsIn p K
      ((⟨fun _ => false,s ∘ executorPorts⟩ : State 16 256).withPC (some p.entry))
      ((⟨rf,Function.update (Function.update (s ∘ executorPorts) 26 []) 240 bits⟩ :
        State 16 256).withPC none)) :
    ExecutesIn (execute p) (K+18) s
      (Function.update (Function.update s 26 []) 240 bits) := by
  intro regs
  obtain ⟨rf,n,hn,ht⟩ := hrun
  let a : Data := ⟨fun _ => false,s⟩
  let out : State 16 256 :=
    ⟨rf,Function.update (Function.update (s ∘ executorPorts) 26 []) 240 bits⟩
  have hc := eval_call_from_state p id executorPorts a
    Function.injective_id executorPorts_injective ht
  have hs : (embedState id executorPorts a out).stacks=
      Function.update (Function.update s 26 []) 240 bits := by
    change Function.extend executorPorts out.stacks s = _
    dsimp only [out]
    rw [ProgramLinking.extend_update executorPorts_injective,
      ProgramLinking.extend_update executorPorts_injective]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project id executorPorts a Function.injective_id executorPorts_injective)
    change Function.extend executorPorts (s ∘ executorPorts) s=s at hb
    rw [hb]
    rfl
  have hout : embedState id executorPorts a out=
      (⟨(embedState id executorPorts a out).regs,
        Function.update (Function.update s 26 []) 240 bits⟩ : Data) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact hs
  change Eval _ n a (embedState id executorPorts a out) at hc
  rw [hout] at hc
  exact ⟨18+n,_,by omega,(resetExecutor_eval s regs).seq hc⟩

/-- Controls21/26 are temporarily parked while source333 is interpreted. -/
abbrev evaluateRow {l : ℕ} (p : Program 16 256 l) : Code :=
  .seq (transfer 21 335) (.seq (transfer 26 336) (.seq (transfer 333 26)
    (.seq (execute p) (.seq (transfer 335 21) (transfer 336 26)))))

def evaluationInput (s : Store) : Store :=
  let s1 := Function.update (Function.update s 21 []) 335 (s 21).reverse
  let s2 := Function.update (Function.update s1 26 []) 336 (s 26).reverse
  Function.update (Function.update s2 333 []) 26 (s 333).reverse

theorem evaluateRow_run {l : ℕ} (p : Program 16 256 l) (K : ℕ) (s : Store) (bits : List Bool)
    (h335 : s 335=[]) (h336 : s 336=[])
    (hcore : ExecutesIn (execute p) K (evaluationInput s)
      (Function.update (Function.update (evaluationInput s) 26 []) 240 bits)) :
    ExecutesIn (evaluateRow p) (K+6*(s 21).length+6*(s 26).length+3*(s 333).length+15) s
      (Function.update (Function.update s 333 []) 240 bits) := by
  let s1 := Function.update (Function.update s 21 []) 335 (s 21).reverse
  let s2 := Function.update (Function.update s1 26 []) 336 (s 26).reverse
  let s3 := evaluationInput s
  let s4 := Function.update (Function.update s3 26 []) 240 bits
  let s5 := Function.update (Function.update s4 335 []) 21 (s 21)
  have h1 : ExecutesIn (transfer 21 335) (3*(s 21).length+3) s s1 := by
    simpa [s1,h335] using transfer_run 21 335 s (by decide)
  have h2 : ExecutesIn (transfer 26 336) (3*(s 26).length+3) s1 s2 := by
    simpa [s1,s2,h336] using transfer_run 26 336 s1 (by decide)
  have h3 : ExecutesIn (transfer 333 26) (3*(s 333).length+3) s2 s3 := by
    simpa [s3,s2,s1,evaluationInput] using transfer_run 333 26 s2 (by decide)
  have h4 : ExecutesIn (execute p) K s3 s4 := hcore
  have h5 : ExecutesIn (transfer 335 21) (3*(s 21).length+3) s4 s5 := by
    simpa [s5,s4,s3,evaluationInput] using transfer_run 335 21 s4 (by decide)
  have h6 := transfer_run 336 26 s5 (by decide)
  have he6 : Function.update (Function.update s5 336 []) 26
      ((s5 336).reverse++s5 26)=Function.update (Function.update s 333 []) 240 bits := by
    funext i
    by_cases h21 : i=21 <;> by_cases h26 : i=26 <;> by_cases h333 : i=333 <;>
      by_cases hi335 : i=335 <;> by_cases hi336 : i=336 <;> by_cases h240 : i=240 <;>
      simp [s5,s4,s3,evaluationInput,h21,h26,h333,hi335,hi336,h240,h335,h336]
  rw [he6] at h6
  apply (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))).mono
  simp [s5,s4,s3,evaluationInput]
  omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
variable {Witness : Type*}

def records (encode : Witness → List Bool) (ws : List Witness) : List Bool :=
  ws.flatMap (fun w => rowRecord (encode w))

def RowProperty (encode : Witness → List Bool) (R : ℕ → Witness → Prop) (W : ℕ) :
    ℕ → List Witness → Prop
  | _, [] => True
  | j, w::ws => R j w ∧ (encode w).length=W ∧ RowProperty encode R W (j+1) ws

theorem records_length (encode : Witness → List Bool) (R : ℕ → Witness → Prop)
    (W j : ℕ) (ws : List Witness) (h : RowProperty encode R W j ws) :
    (records encode ws).length=ws.length*(2*W+2) := by
  induction ws generalizing j with
  | nil => simp [records]
  | cons w ws ih =>
      obtain ⟨_,hw,ht⟩ := h
      change (rowRecord (encode w)++records encode ws).length=(w::ws).length*(2*W+2)
      rw [List.length_append,ih (j+1) ht]
      simp only [rowRecord,List.length_cons,Encoding.length_frame,hw]
      ring

theorem records_encoding (encode : Witness → List Bool) (ws : List Witness) :
    records encode ws++[false]=Encoding.encodeList encode ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simpa [records,rowRecord,Encoding.encodeList,List.append_assoc] using
        (congrArg (fun b => rowRecord (encode w)++b) ih)

def RelRowSpec (callback : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (N K W : ℕ) : Prop :=
  ∀ j, j < N → ∀ remaining acc regs, ∃ w n rf,
    R j w ∧ (encode w).length=W ∧ n ≤ K ∧
    Eval callback n (⟨regs,rowState base j remaining acc⟩ : Data)
      (⟨rf,Function.update (rowState base j remaining acc) 240 (encode w)⟩ : Data)

theorem rowTail_run (base : Store) (j : ℕ) (remaining acc bits : List Bool)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[]) :
    ExecutesIn (.seq emitRow (push 320 true)) (13*bits.length+22)
      (Function.update (rowState base j remaining acc) 240 bits)
      (rowState base (j+1) remaining ((rowRecord bits).reverse++acc)) := by
  let s1 := Function.update (rowState base j remaining acc) 240 bits
  let s2 := rowState base j remaining ((rowRecord bits).reverse++acc)
  have he1 : Function.update (Function.update s1 240 []) 332
      ((rowRecord (s1 240)).reverse++s1 332)=s2 := by
    funext i
    by_cases h320 : i=320 <;> by_cases h331 : i=331 <;>
      by_cases h332 : i=332 <;> by_cases hh240 : i=240 <;>
      simp [s2,s1,rowState,Function.update_apply,h320,h331,h332,hh240,h240]
  have h1 : ExecutesIn emitRow (13*bits.length+20) s1 s2 := by
    have h := emitRow_run s1 (by simp [s1,rowState,h330]) (by simp [s1,rowState,h334])
    rw [he1] at h
    simpa [s1] using h
  have h2 := push_run 320 true s2
  have he2 : Function.update s2 320 (true::s2 320)=
      rowState base (j+1) remaining ((rowRecord bits).reverse++acc) := by
    funext i
    by_cases h320 : i=320 <;> by_cases h331 : i=331 <;> by_cases h332 : i=332 <;>
      simp [s2,rowState,h320,h331,h332,List.replicate_succ]
  rw [he2] at h2
  exact (h1.seq h2).mono (by omega)

theorem rowBody_rel (callback : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (N K W : ℕ) (spec : RelRowSpec callback base encode R N K W)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[])
    (j : ℕ) (hj : j < N) (remaining acc : List Bool) (regs : Fin 16 → Bool) :
    ∃ w n rf, R j w ∧ (encode w).length=W ∧ n ≤ K+13*W+22 ∧
      Eval (rowBody callback) n (⟨regs,rowState base j remaining acc⟩ : Data)
        (⟨rf,rowState base (j+1) remaining ((rowRecord (encode w)).reverse++acc)⟩ : Data) := by
  obtain ⟨w,n1,r1,hw,hl,hn1,he1⟩ := spec j hj remaining acc regs
  obtain ⟨n2,r2,hn2,he2⟩ := rowTail_run base j remaining acc (encode w) h240 h330 h334 r1
  exact ⟨w,n1+n2,r2,hw,hl,by omega,he1.seq he2⟩

theorem row_visits_rel (callback : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (N K W : ℕ) (spec : RelRowSpec callback base encode R N K W)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[])
    (remaining acc : List Bool) (j : ℕ) (hj : j+remaining.length ≤ N) (regs : Fin 16 → Bool) :
    ∃ ws costs n rf, RowProperty encode R W j ws ∧ ws.length=remaining.length ∧
      n ≤ remaining.length*(K+13*W+24)+2 ∧
      UnaryForPrograms.Visits rowPorts (rowBody callback) costs n
        (⟨regs,rowState base j remaining acc⟩ : Data)
        (⟨rf,rowState base (j+remaining.length) [] ((records encode ws).reverse++acc)⟩ : Data) := by
  induction remaining generalizing j acc regs with
  | nil =>
    refine ⟨[],[],2,readRegs regs 14 15 none,True.intro,rfl,by simp,?_⟩
    simpa only [row_popped,List.head?_nil,List.tail_nil,List.length_nil,
      Nat.add_zero,records,List.flatMap_nil,List.reverse_nil,List.nil_append] using
      UnaryForPrograms.Visits.done (p := rowPorts) (body := rowBody callback)
        (⟨regs,rowState base j [] acc⟩ : Data) (by simp [rowState,rowPorts])
  | cons b remaining ih =>
    obtain ⟨w,nb,rb,hw,hl,hnb,hb⟩ := rowBody_rel callback base encode R N K W spec h240 h330 h334
      j (by simp only [List.length_cons] at hj; omega) remaining acc (readRegs regs 14 15 (some b))
    obtain ⟨ws,costs,nt,rt,hws,hcount,hnt,ht⟩ := ih ((rowRecord (encode w)).reverse++acc) (j+1)
      (by simp only [List.length_cons] at hj; omega) rb
    refine ⟨w::ws,nb::costs,nb+nt+2,rt,⟨hw,hl,hws⟩,by simp [hcount],?_,?_⟩
    · simp only [List.length_cons]; nlinarith
    · have h := UnaryForPrograms.Visits.step (p := rowPorts) (body := rowBody callback)
        (d := (⟨regs,rowState base j (b::remaining) acc⟩ : Data))
        (by simp [rowState,rowPorts])
        (by simpa only [row_popped,List.head?_cons,List.tail_cons] using hb)
        (by simp [rowState,rowPorts,UnaryForPrograms.popped]) ht
      simpa [List.length_cons,records,List.reverse_append,List.append_assoc,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem rowsCommand_rel (callback : Code) (base : Store) (encode : Witness → List Bool)
    (R : ℕ → Witness → Prop) (N K W : ℕ) (spec : RelRowSpec callback base encode R N K W)
    (hN : (base 212).length=N)
    (h240 : base 240=[]) (h330 : base 330=[]) (h334 : base 334=[])
    (h320 : base 320=[]) (h331 : base 331=[]) (h332 : base 332=[])
    (h205 : base 205=[]) (h339 : base 339=[]) (regs : Fin 16 → Bool) :
    ∃ ws n rf, RowProperty encode R W 0 ws ∧ ws.length=N ∧ n ≤ N*(K+19*W+39)+18 ∧
      Eval (rowsCommand callback) n (⟨regs,base⟩ : Data)
        (⟨rf,Function.update base 205 (Encoding.encodeList encode ws)⟩ : Data) := by
  let s1 := rowState base 0 (base 212) []
  have he1 : Function.update base 331 (base 212++base 331)=s1 := by
    funext i
    by_cases hi320 : i=320 <;> by_cases hi331 : i=331 <;> by_cases hi332 : i=332 <;>
      simp [s1,rowState,hi320,hi331,hi332,h320,h331,h332]
  obtain ⟨n1,r1,hn1,hec⟩ := copy_run 212 331 base (by decide) (by decide) (by decide) h339 regs
  rw [he1] at hec
  obtain ⟨ws,costs,n2,r2,hr,hcount,hn2,he2⟩ := row_visits_rel callback base encode R N K W spec
    h240 h330 h334 (base 212) [] 0 (by omega) r1
  let s2 := rowState base N [] (records encode ws).reverse
  have hh2 : Eval (rowLoop callback) n2 (⟨r1,s1⟩ : Data) (⟨r2,s2⟩ : Data) := by
    simpa [rowLoop,s1,s2,hN] using he2.eval
  let s3 := Function.update s2 320 []
  obtain ⟨n3,r3,hn3,he3⟩ := clear_run 320 s2 r2
  obtain ⟨n4,r4,hn4,he4⟩ := finishRows_run s3 (by simp [s3,s2,rowState,h205]) r3
  have hout : Function.update (Function.update s3 332 []) 205 ((s3 332).reverse++[false])=
      Function.update base 205 (Encoding.encodeList encode ws) := by
    funext i
    by_cases hi320 : i=320 <;> by_cases hi331 : i=331 <;>
      by_cases hi332 : i=332 <;> by_cases hi205 : i=205 <;>
      simp [s3,s2,rowState,hi320,hi331,hi332,hi205,h320,h331,h332,
        records_encoding]
  rw [hout] at he4
  have hwlen := records_length encode R W 0 ws hr
  refine ⟨ws,n1+(n2+(n3+n4)),r4,hr,hcount.trans hN,?_,hec.seq (hh2.seq (he3.seq he4))⟩
  have hn3' : n3 ≤ 2*N+3 := by simpa [s2,rowState] using hn3
  have hn4' : n4 ≤ 3*(records encode ws).length+8 := by simpa [s3,s2,rowState] using hn4
  rw [hcount,hN] at hwlen
  rw [hwlen] at hn4'
  rw [hN] at hn1 hn2
  nlinarith

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

variable {R : Type*}

theorem serialize_append (encode : R → List Bool) (a b : List (Algorithm.Instr R)) :
    SubexpPostfixControl.serializeCode encode (a++b)=
      SubexpPostfixControl.serializeCode encode a++SubexpPostfixControl.serializeCode encode b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [SubexpPostfixControl.serializeCode,ih,List.append_assoc]

def foldExpr (source : ℕ → Algorithm.Expr R) (seed : Algorithm.Expr R) (ids : List ℕ) :
    Algorithm.Expr R := ids.foldl (fun acc i => .add acc (source i)) seed

theorem foldExpr_code (encode : R → List Bool) (source : ℕ → Algorithm.Expr R)
    (seed : Algorithm.Expr R) (ids : List ℕ) :
    SubexpPostfixControl.serializeCode encode (foldExpr source seed ids).compile =
      SubexpPostfixControl.serializeCode encode seed.compile++
        sumBytes (fun i => SubexpPostfixControl.serializeCode encode (source i).compile) ids := by
  induction ids generalizing seed with
  | nil => simp [foldExpr,sumBytes]
  | cons i ids ih =>
      rw [foldExpr,List.foldl_cons]
      change SubexpPostfixControl.serializeCode encode
        (foldExpr source (.add seed (source i)) ids).compile=_
      rw [ih]
      simp [Algorithm.Expr.compile,serialize_append,SubexpPostfixControl.serializeCode,
        SubexpPostfixControl.serializeInstr,sumBytes,List.append_assoc]

theorem foldExpr_eval [AddMonoid R] [Mul R] (source : ℕ → Algorithm.Expr R)
    (seed : Algorithm.Expr R) (ids : List ℕ) :
    (foldExpr source seed ids).eval=seed.eval+(ids.map fun i => (source i).eval).sum := by
  induction ids generalizing seed with
  | nil => simp [foldExpr]
  | cons i ids ih =>
      change (foldExpr source (.add seed (source i)) ids).eval=_
      rw [ih]
      simp [Algorithm.Expr.eval,add_assoc]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
variable {R : Type*}

def foldSources (seed : Algorithm.Expr R) (sources : List (Algorithm.Expr R)) : Algorithm.Expr R :=
  sources.foldl Algorithm.Expr.add seed

theorem foldSources_code (encode : R → List Bool) (seed : Algorithm.Expr R)
    (sources : List (Algorithm.Expr R)) :
    SubexpPostfixControl.serializeCode encode (foldSources seed sources).compile=
      SubexpPostfixControl.serializeCode encode seed.compile++
        emittedBytes (fun e : Algorithm.Expr R =>
          SubexpPostfixControl.serializeCode encode e.compile) sources := by
  induction sources generalizing seed with
  | nil => simp [foldSources,emittedBytes]
  | cons e es ih =>
      change SubexpPostfixControl.serializeCode encode (foldSources (.add seed e) es).compile=_
      rw [ih]
      simp [Algorithm.Expr.compile,serialize_append,SubexpPostfixControl.serializeCode,
        SubexpPostfixControl.serializeInstr,emittedBytes,List.append_assoc]

theorem foldSources_zero_code (encode : R → List Bool) (z : R) (hz : encode z=[])
    (sources : List (Algorithm.Expr R)) :
    SubexpPostfixControl.serializeCode encode (foldSources (.lit z) sources).compile=
      [false,false]++emittedBytes (fun e : Algorithm.Expr R =>
          SubexpPostfixControl.serializeCode encode e.compile) sources := by
  rw [foldSources_code]
  simp [Algorithm.Expr.compile,SubexpPostfixControl.serializeCode,
    SubexpPostfixControl.serializeInstr,hz,Encoding.frame]

theorem foldSources_eval [AddMonoid R] [Mul R] (seed : Algorithm.Expr R)
    (sources : List (Algorithm.Expr R)) :
    (foldSources seed sources).eval=seed.eval+(sources.map Algorithm.Expr.eval).sum := by
  induction sources generalizing seed with
  | nil => simp [foldSources]
  | cons e es ih =>
      change (foldSources (.add seed e) es).eval=_
      rw [ih]
      simp [Algorithm.Expr.eval,add_assoc]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

/-- Semantic values are added in the same order as the emitted sources. -/
theorem foldSources_map_eval {C A : Type*} [AddMonoid A] [Mul A]
    (decode : C → A) (seed : Algorithm.Expr C) (sources : List (Algorithm.Expr C)) :
    ((foldSources seed sources).map decode).eval=
      (seed.map decode).eval+(sources.map (fun e => (e.map decode).eval)).sum := by
  induction sources generalizing seed with
  | nil => simp [foldSources]
  | cons e es ih =>
      change ((foldSources (.add seed e) es).map decode).eval=_
      rw [ih]
      simp [Algorithm.Expr.map,Algorithm.Expr.eval,add_assoc]

theorem related_sources_sum {C A : Type*} [AddMonoid A] [Mul A]
    (decode : C → A) (value : ℕ → A) (ids : List ℕ) (sources : List (Algorithm.Expr C))
    (h : List.Forall₂ (fun i e => (e.map decode).eval=value i) ids sources) :
    (sources.map (fun e => (e.map decode).eval)).sum=(ids.map value).sum := by
  induction h with
  | nil => rfl
  | cons h hs ih => simp [h,ih]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
