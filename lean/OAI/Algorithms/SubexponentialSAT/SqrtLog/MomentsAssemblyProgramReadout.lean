import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

/-- Readout work stays below the persistent source and arithmetic metadata. -/
def readoutWorkPorts : List (Fin 768) :=
  [96,97,98,99,100,101,103,105,106,107,108,109,110,111,112,113,
    114,115,116,117,118,119,120,121,122,123,124,125,126,127,189]

/-- Readout uses only its named arithmetic inputs and reserved work tapes. -/
def readoutPorts : Fin 40 → Fin 768 :=
  ![102,96,97,98,99,5,100,101,103,105,106,107,12,108,109,166,
    110,111,112,113,114,115,116,117,39,118,119,190,45,46,120,121,
    122,123,124,125,191,126,127,189]

theorem readoutPorts_injective : Function.Injective readoutPorts := by decide

def readout : Code := .call (ProgramLinking.liftProgram MomentsReadoutProgram.program coreRegisters readoutPorts)

theorem readout_output_stacks (regs : Fin 8 → Bool) (a : MomentsReadoutProgram.D)
    (h : MomentsReadoutProgram.High) (bits : List Bool) :
    (MomentsReadoutProgram.wideState regs {a with out := bits} h).stacks =
      Function.update (MomentsReadoutProgram.wideState regs a h).stacks 0 bits := by
  funext i
  fin_cases i <;> simp [MomentsReadoutProgram.wideState,MomentsReadoutProgram.wideTapes
]

/-- Relocate the actual native readout. It changes only output102 among
caller tapes, so node caches, jet-shape104, and the sparse answer166 survive. -/
theorem readout_eval {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Product.Entry n (baseWidth p e) d))
    (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (width count t J shape : List Bool) (W : ℕ)
    (hc : count.length=d) (hw : width.length=baseWidth p e) (hs : shape.length=n)
    (hk : ∀ a∈entries, (Squarefree.encodeIndex a.1).length ≤ W)
    (frame : Data)
    (hproj : projectState coreRegisters readoutPorts frame =
      MomentsReadoutProgram.wideState (frame.regs ∘ coreRegisters)
        (MomentsProgram.Dictionary.inputTape M.bits width count
          (Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries) [] [])
        (MomentsReadoutProgram.inputHigh (RingProgram.flat zero) t J shape)) :
    ∃ k ≤ MomentsReadoutProgram.uniformReadoutBudget (baseWidth p e) d n t.length J.length W entries.length,
      ∃ rr, Eval readout k frame
        ⟨rr,Function.update frame.stacks 102 (MomentsReadoutProgram.outputBits p e M cache entries t.length zero 0 J.length)⟩ := by
  obtain ⟨rr,k,hk',ht⟩ := MomentsReadoutProgram.program_runsIn_polynomial p e M cache entries zero
    (frame.regs ∘ coreRegisters) width count t J shape W hc hw hs hk
  let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
  let a := MomentsProgram.Dictionary.inputTape M.bits width count encoded [] []
  let high := MomentsReadoutProgram.inputHigh (RingProgram.flat zero) t J shape
  let bits := MomentsReadoutProgram.outputBits p e M cache entries t.length zero 0 J.length
  let out := MomentsReadoutProgram.wideState rr {a with out := bits} high
  have ht' : Trace MomentsReadoutProgram.program k
      ((projectState coreRegisters readoutPorts frame).withPC (some MomentsReadoutProgram.program.entry))
      (out.withPC none) := by simpa only [hproj,out,a,high,encoded,bits] using ht
  have he := eval_call_from_state MomentsReadoutProgram.program coreRegisters readoutPorts frame
    coreRegisters_injective readoutPorts_injective ht'
  let result := embedState coreRegisters readoutPorts frame out
  have hresult : result = ⟨result.regs,Function.update frame.stacks 102 bits⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i ∈ Set.range readoutPorts
      · obtain ⟨j,rfl⟩ := hi
        have hpj : frame.stacks (readoutPorts j) =
            (MomentsReadoutProgram.wideState rr a high).stacks j :=
          congrFun (congrArg StructuredProgram.State.stacks hproj) j
        have ho := readout_output_stacks rr a high bits
        change (embedState coreRegisters readoutPorts frame out).stacks (readoutPorts j) = _
        rw [embedState_stack _ _ _ _ readoutPorts_injective]
        change (MomentsReadoutProgram.wideState rr {a with out := bits} high).stacks j = _
        rw [ho]
        by_cases hj : j=0
        · subst j; simp [readoutPorts]
        · have h102 : readoutPorts j ≠ 102 := by
            intro h
            have hh : readoutPorts j = readoutPorts 0 := by simpa [readoutPorts] using h
            exact hj (readoutPorts_injective hh)
          simp only [Function.update_noteq hj,Function.update_noteq h102]
          exact hpj.symm
      · change (embedState coreRegisters readoutPorts frame out).stacks i = _
        rw [embedState_stack_frame _ _ _ _ i hi]
        have h102 : i ≠ 102 := by intro h; apply hi; exact ⟨0,by simpa [readoutPorts] using h.symm⟩
        simp [h102]
  refine ⟨k,hk',result.regs,?_⟩
  change Eval readout k frame result at he
  rw [hresult] at he
  exact he

end SubexponentialSAT.SqrtLog.MomentsAssembly

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

theorem readout_project_machine {n d : ℕ} (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (entries : List (Product.Entry n (baseWidth p t) d))
    (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width shape : List Bool) (u J : ℕ) (regs : Fin 40 → Bool)
    (high : Fin 768 → List Bool)
    (h102 : high 102 = []) (h166 : high 166 = Product.bytes entries)
    (h190 : high 190 = RingProgram.flat zero) (h191 : high 191 = shape)
    (hwork : ∀ i ∈ readoutWorkPorts, high i = []) :
    projectState coreRegisters readoutPorts
      (machine regs (emptyCore (Product.environment p t M cache table degree width u J)) high) =
      MomentsReadoutProgram.wideState (regs ∘ coreRegisters)
        (MomentsProgram.Dictionary.inputTape M.bits width degree
          (Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries) [] [])
        (MomentsReadoutProgram.inputHigh (RingProgram.flat zero) (List.replicate u true)
          (List.replicate J true) shape) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;>
      simp [machine,emptyCore,Product.environment,Product.idle,Product.tapes,
        readoutPorts,MomentsReadoutProgram.wideTapes,
        MomentsReadoutProgram.inputHigh,MomentsProgram.Dictionary.inputTape,

        Product.bytes,Normalize.bytes,Squarefree.Program.encodeDictionary,
        h102,h166,h190,h191] <;>
      exact hwork _ (by decide)

/-- Concrete assembly-to-dense-jet boundary on the final 40/768 workspace. -/
theorem readout_machine_eval {n d : ℕ} (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (entries : List (Product.Entry n (baseWidth p t) d))
    (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (degree width shape : List Bool) (u J W : ℕ) (regs : Fin 40 → Bool)
    (high : Fin 768 → List Bool)
    (hd : degree.length=d) (hw : width.length=baseWidth p t) (hs : shape.length=n)
    (hk : ∀ a∈entries, (Squarefree.encodeIndex a.1).length ≤ W)
    (h102 : high 102 = []) (h166 : high 166 = Product.bytes entries)
    (h190 : high 190 = RingProgram.flat zero) (h191 : high 191 = shape)
    (hwork : ∀ i ∈ readoutWorkPorts, high i = []) :
    let core := emptyCore (Product.environment p t M cache table degree width u J)
    ∃ k ≤ MomentsReadoutProgram.uniformReadoutBudget (baseWidth p t) d n u J W entries.length,
      ∃ rr, Eval readout k (machine regs core high)
        (machine rr core (Function.update high 102 (MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J))) := by
  dsimp only
  let core := emptyCore (Product.environment p t M cache table degree width u J)
  obtain ⟨k,hk',rr,he⟩ := readout_eval p t M cache entries zero width degree
    (List.replicate u true) (List.replicate J true) shape W hd hw hs hk
    (machine regs core high) (readout_project_machine p t M cache table entries zero
      degree width shape u J regs high h102 h166 h190 h191 hwork)
  refine ⟨k,by simpa using hk',rr,?_⟩
  have he' : Eval readout k (machine regs core high)
      ⟨rr,Function.update (machine regs core high).stacks 102
        (MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J)⟩ := by
    simpa only [List.length_replicate] using he
  convert he' using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : i.val < 56
    · have hne : i ≠ 102 := by intro h; subst i; norm_num at hi
      simp [machine,hi,hne,core]
    · simp [machine,hi,Function.update_apply]

def denseCommand (produce : Code) : Code := .seq (command produce) readout

def denseProgram (produce : Code) := compiled (denseCommand produce) 163 102

end SubexponentialSAT.SqrtLog.MomentsAssembly

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

/-- Full moment assembly followed by physical dense Z-jet readout. All
remaining premises concern actual input encodings and the paid assignment
producer; no precomputed sums, products, or projected jets are accepted. -/
theorem denseProgram_run (produce : Code) (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width shape : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hshape : shape.length=n) (u J W : ℕ)
    (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
    (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
      List (Product.Entry n (baseWidth p t) d) → ℕ)
    (validFrame : (Fin 768 → List Bool) → Prop)
    (contract : AssignmentContract produce p t M cache table degree width u J meaning cost validFrame)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (bs : List BucketInput) (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (hsupports : base 169 = rawFrames (ss.map Squarefree.encodeMask))
    (hone : base 167 = Product.bytes one) (hclean : SupportClean base)
    (h162 : base 162 = []) (h170 : base 170 = []) (h177 : base 177 = [])
    (hv : BucketFrames (n:=n) validFrame base bs)
    (h102 : base 102 = []) (h190 : base 190 = RingProgram.flat zero) (h191 : base 191 = shape)
    (hwork : ∀ i ∈ readoutWorkPorts, base i = [])
    (hk : ∀ a ∈ bucketsRun p t M cache table u J meaning base ss one bs seed,
      (Squarefree.encodeIndex a.1).length ≤ W) :
    let e := Product.environment p t M cache table degree width u J
    let entries := bucketsRun p t M cache table u J meaning base ss one bs seed
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    ∃ rr, RunsIn (denseProgram produce)
      (bucketsWork p t M cache table u J meaning cost base ss one bs seed+
        MomentsReadoutProgram.uniformReadoutBudget (baseWidth p t) d n u J W entries.length+1)
      ((machine regs (emptyCore e) (bucketStream base (Product.bytes seed) (bucketsInput bs))).withPC
        (some (denseProgram produce).entry))
      ((machine rr (emptyCore e) (Function.update (bucketStream base (Product.bytes entries) []) 102 bits)).withPC none) := by
  dsimp only
  let e := Product.environment p t M cache table degree width u J
  let entries := bucketsRun p t M cache table u J meaning base ss one bs seed
  let high := bucketStream base (Product.bytes entries) []
  obtain ⟨na,ha,r1,h1⟩ := command_eval produce p t M cache hz table degree width hd hw u J
    meaning cost validFrame contract one seed ss bs base regs hsupports hone hclean h162 h170 h177 hv
  obtain ⟨nr,hr,r2,h2⟩ := readout_machine_eval p t M cache table entries zero degree width shape u J W r1 high
    hd hw hshape hk (by simp [high,bucketStream,h102]) (by simp [high,bucketStream])
    (by simp [high,bucketStream,h190]) (by simp [high,bucketStream,h191]) (by
      intro i hi
      have hn163 : i ≠ 163 := by intro h; subst i; norm_num [readoutWorkPorts,Fin.ext_iff] at hi
      have hn166 : i ≠ 166 := by intro h; subst i; norm_num [readoutWorkPorts,Fin.ext_iff] at hi
      simpa [high,bucketStream,hn163,hn166] using hwork i hi)
  dsimp [entries] at hr
  refine ⟨r2,na+nr+1,by omega,?_⟩
  exact compiled_halt_trace (h1.seq h2) 163 102

theorem dense_output_length {n d : ℕ} (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (entries : List (Product.Entry n (baseWidth p t) d))
    (zero : RingProgram.Code (Word (baseWidth p t)) d) (u J : ℕ) :
    (MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J).length = J*(d*baseWidth p t) :=
  MomentsReadoutProgram.outputBits_length p t M cache entries u zero 0 J

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
