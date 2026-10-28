import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceState
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssemblyCost

namespace OAI.Algorithms

/-! Actual per-descriptor weight construction inside the moment source loop.
The exponent is read from the current X stack. The point bank and support are
parsed from the reusable, unweighted template on every call. -/

namespace SubexponentialSAT.SubexpMomentSourceProgram

open BitProgram StructuredCalls

def pointDescriptor {D : ℕ} (coordinates : Fin D → Word) (support : List (Fin D)) : Descriptor :=
  ⟨(List.ofFn coordinates).flatten,
    Encoding.encodeList id (SubexpWeightGather.supportBits support)⟩

def descriptorBudget (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (support : List (Fin ctx.dimension)) (records : List SubexpWeightControl.WeightRecord) : ℕ :=
  7*ctx.target.length+12+SubexpWeightGather.supportBudget a ctx.width ctx.target support+
    SubexpWeightControl.scanSteps ctx.target.length records+2+
      SubexpWeightLiteralProgram.overhead ctx.dimension ctx.target.length

def captureBudget (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (coordinates : Fin ctx.dimension → Word) (support : List (Fin ctx.dimension))
    (records : List SubexpWeightControl.WeightRecord) : ℕ :=
  17*(pointDescriptor coordinates support).bank.length+
    15*(pointDescriptor coordinates support).support.length+31+
      descriptorBudget ctx a support records

theorem descriptor_call_eval (ctx : Context) (r : Fin 8 → Bool)
    (a : Fin ctx.dimension → ℕ) (coordinates : Fin ctx.dimension → Word)
    (support : List (Fin ctx.dimension)) (input captured : Word)
    (buffers : SubexpBlockAssembly.Buffers)
    (hX : ctx.exponent = SymbolicCost.unaryWords (List.ofFn a))
    (hI : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension)
    (hn : support.Nodup) (hwidth : ∀ i, (coordinates i).length = ctx.width.length)
    (hpad : ctx.width.length ≤ ctx.target.length) (hunit : ctx.unit.length = ctx.target.length)
    (hunitValue : (BinaryArithmetic.toNat ctx.unit : ZMod (BinaryArithmetic.toNat ctx.modulus)) = 1)
    (hmLength : ctx.modulus.length ≤ ctx.target.length+1)
    (hm : 0 < BinaryArithmetic.toNat ctx.modulus)
    (hcapacity : BinaryArithmetic.toNat ctx.modulus ≤ 2^ctx.target.length) :
    ∃ n rf output records,
      n ≤ descriptorBudget ctx a support records ∧
      List.Forall₂ (SubexpWeightGather.GoodRecord a coordinates ctx.target) support.reverse records ∧
      Eval (.call (ProgramLinking.liftProgram SubexpWeightDescriptorProgram.program id descriptorPorts)) n
        (state ctx r input buffers [] (pointDescriptor coordinates support).bank
          (pointDescriptor coordinates support).support captured)
        (state ctx rf input buffers
          (SubexpScalarLiteralProgram.rawLiteral ctx.dimension
            (SubexpQuarticMarshal.marshalBits output ctx.target))
          (pointDescriptor coordinates support).bank [] captured) ∧
      output.length = ctx.target.length ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat ctx.modulus)) =
        Separation.coordinateWeight support.toFinset id a
          (fun i => (BinaryArithmetic.toNat (coordinates i) : ZMod (BinaryArithmetic.toNat ctx.modulus))) := by
  obtain ⟨rf,output,records,hgood,⟨n,hbound,ht⟩,hlen,hvalue⟩ :=
    SubexpWeightDescriptorProgram.program_execute r a coordinates ctx.width ctx.target
      ctx.modulus ctx.unit [] support hn hwidth hpad hunit hunitValue hmLength hm hcapacity
  simp only [List.append_nil] at ht
  rw [←hX,←hI] at ht
  let d := state ctx r input buffers [] (pointDescriptor coordinates support).bank
    (pointDescriptor coordinates support).support captured
  have h := eval_call_from_state SubexpWeightDescriptorProgram.program id descriptorPorts d
    Function.injective_id descriptorPorts_injective
    (by simpa only [d,descriptor_project,pointDescriptor] using ht)
  refine ⟨n,rf,output,records,hbound,hgood,?_,hlen,hvalue⟩
  simpa only [d,pointDescriptor,descriptor_embed] using h

/-- Read both descriptor fields, compute the current exponent's weight, and
return the actual raw constant-polynomial literal. All buffers, context data,
the source suffix, and captured source are preserved. -/
theorem weightCapture_eval (ctx : Context) (r : Fin 8 → Bool)
    (a : Fin ctx.dimension → ℕ) (coordinates : Fin ctx.dimension → Word)
    (support : List (Fin ctx.dimension)) (rest captured : Word)
    (buffers : SubexpBlockAssembly.Buffers)
    (hX : ctx.exponent = SymbolicCost.unaryWords (List.ofFn a))
    (hI : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension)
    (hn : support.Nodup) (hwidth : ∀ i, (coordinates i).length = ctx.width.length)
    (hpad : ctx.width.length ≤ ctx.target.length) (hunit : ctx.unit.length = ctx.target.length)
    (hunitValue : (BinaryArithmetic.toNat ctx.unit : ZMod (BinaryArithmetic.toNat ctx.modulus)) = 1)
    (hmLength : ctx.modulus.length ≤ ctx.target.length+1)
    (hm : 0 < BinaryArithmetic.toNat ctx.modulus)
    (hcapacity : BinaryArithmetic.toNat ctx.modulus ≤ 2^ctx.target.length) :
    ∃ n rf output records,
      n ≤ captureBudget ctx a coordinates support records ∧
      List.Forall₂ (SubexpWeightGather.GoodRecord a coordinates ctx.target) support.reverse records ∧
      Eval weightCapture n
        (state ctx r (encodeDescriptor (pointDescriptor coordinates support) ++ rest)
          buffers [] [] [] captured)
        (state ctx rf rest buffers
          (SubexpScalarLiteralProgram.rawLiteral ctx.dimension
            (SubexpQuarticMarshal.marshalBits output ctx.target)) [] [] captured) ∧
      output.length = ctx.target.length ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat ctx.modulus)) =
        Separation.coordinateWeight support.toFinset id a
          (fun i => (BinaryArithmetic.toNat (coordinates i) : ZMod (BinaryArithmetic.toNat ctx.modulus))) := by
  let bank := (pointDescriptor coordinates support).bank
  let supp := (pointDescriptor coordinates support).support
  let r1 := flags r false false (r 2)
  let r2 := readRegs r1 0 1 none
  let r3 := flags r2 false false (r2 2)
  let r4 := readRegs r3 0 1 none
  have h1 := base_eval ctx r (Encoding.frame bank ++ (Encoding.frame supp ++ rest))
    (Encoding.frame supp ++ rest) buffers buffers [] bank [] [] captured false false (r 2)
    (SubexpBlockAssembly.capture_measured (r 0) (r 1) (r 2) bank
      (Encoding.frame supp ++ rest) ctx.zero ctx.one buffers)
  have h2 := move_bank_eval ctx r1 (Encoding.frame supp ++ rest) buffers bank captured
  have h3 := base_eval ctx r2 (Encoding.frame supp ++ rest) rest buffers buffers [] supp bank []
    captured false false (r2 2)
    (SubexpBlockAssembly.capture_measured (r2 0) (r2 1) (r2 2) supp rest ctx.zero ctx.one buffers)
  have h4 := move_support_eval ctx r3 rest buffers supp bank captured
  obtain ⟨nd,rd,output,records,hnd,hgood,hd,hlen,hvalue⟩ :=
    descriptor_call_eval ctx r4 a coordinates support rest captured buffers hX hI hn
      hwidth hpad hunit hunitValue hmLength hm hcapacity
  have hc := clear_bank_eval ctx rd rest buffers
    (SubexpScalarLiteralProgram.rawLiteral ctx.dimension
      (SubexpQuarticMarshal.marshalBits output ctx.target)) bank captured
  have h := Eval.seq h1 (Eval.seq h2 (Eval.seq h3 (Eval.seq h4 (Eval.seq hd hc))))
  refine ⟨9*bank.length+7+1+(6*bank.length+6+
    (9*supp.length+7+1+(6*supp.length+6+(nd+(2*bank.length+3))))),
    readRegs rd 0 1 none,output,records,?_,hgood,?_,hlen,hvalue⟩
  · dsimp only [captureBudget]
    change 9*bank.length+7+1+(6*bank.length+6+
      (9*supp.length+7+1+(6*supp.length+6+(nd+(2*bank.length+3))))) ≤
      17*bank.length+15*supp.length+31+descriptorBudget ctx a support records
    omega
  · simpa only [weightCapture,encodeDescriptor,List.append_assoc,bank,supp,r1,r2,r3,r4] using h

theorem weightFrame_eval (ctx : Context) (r : Fin 8 → Bool)
    (a : Fin ctx.dimension → ℕ) (coordinates : Fin ctx.dimension → Word)
    (support : List (Fin ctx.dimension)) (rest captured : Word)
    (buffers : SubexpBlockAssembly.Buffers) (i : Fin 7)
    (hX : ctx.exponent = SymbolicCost.unaryWords (List.ofFn a))
    (hI : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension)
    (hn : support.Nodup) (hwidth : ∀ j, (coordinates j).length = ctx.width.length)
    (hpad : ctx.width.length ≤ ctx.target.length) (hunit : ctx.unit.length = ctx.target.length)
    (hunitValue : (BinaryArithmetic.toNat ctx.unit : ZMod (BinaryArithmetic.toNat ctx.modulus)) = 1)
    (hmLength : ctx.modulus.length ≤ ctx.target.length+1)
    (hm : 0 < BinaryArithmetic.toNat ctx.modulus)
    (hcapacity : BinaryArithmetic.toNat ctx.modulus ≤ 2^ctx.target.length) :
    ∃ n rf output records,
      n ≤ captureBudget ctx a coordinates support records+
        40*SubexpSymbolicCost.indexBits ctx.dimension+160*ctx.target.length+82 ∧
      List.Forall₂ (SubexpWeightGather.GoodRecord a coordinates ctx.target) support.reverse records ∧
      Eval (weightFrame (SubexpBlockAssembly.bufferPort i)) n
        (state ctx r (encodeDescriptor (pointDescriptor coordinates support) ++ rest)
          buffers [] [] [] captured)
        (state ctx rf rest
          (SubexpBlockAssembly.emit i (Encoding.frame
            (SubexpScalarLiteralProgram.rawLiteral ctx.dimension
              (SubexpQuarticMarshal.marshalBits output ctx.target))) buffers) [] [] [] captured) ∧
      output.length = ctx.target.length ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat ctx.modulus)) =
        Separation.coordinateWeight support.toFinset id a
          (fun j => (BinaryArithmetic.toNat (coordinates j) : ZMod (BinaryArithmetic.toNat ctx.modulus))) := by
  obtain ⟨nc,rc,output,records,hnc,hgood,hc,hlen,hvalue⟩ :=
    weightCapture_eval ctx r a coordinates support rest captured buffers hX hI hn
      hwidth hpad hunit hunitValue hmLength hm hcapacity
  let lit := SubexpScalarLiteralProgram.rawLiteral ctx.dimension
    (SubexpQuarticMarshal.marshalBits output ctx.target)
  let next := SubexpBlockAssembly.emit i (Encoding.frame lit) buffers
  have hframeLocal := SubexpBlockAssembly.measured_result
    (SubexpBlockAssembly.appendFrame_eval 19 (SubexpBlockAssembly.bufferPort i)
      (by fin_cases i <;> decide) (by decide) (by fin_cases i <;> decide)
      (SubexpBlockAssembly.work (rc 0) (rc 1) (rc 2) rest ctx.zero ctx.one buffers lit []) rfl)
    (SubexpBlockAssembly.appendFrame_work i (rc 0) (rc 1) (rc 2) rest ctx.zero ctx.one lit buffers)
  have hf := base_eval ctx rc rest rest buffers next lit lit [] [] captured false false true hframeLocal
  let r1 := flags rc false false true
  have hclear := base_eval ctx r1 rest rest next next lit [] [] [] captured false false true
    (SubexpBlockAssembly.clearPayload_measured (r1 0) (r1 1) (r1 2)
      rest ctx.zero ctx.one lit next)
  have h := Eval.seq hc (Eval.seq hf hclear)
  have hlit : lit.length = 4*SubexpSymbolicCost.indexBits ctx.dimension+16*ctx.target.length+7 := by
    rw [SubexpWeightLiteralProgram.rawLiteral_length]
    simp only [SubexpQuarticMarshal.marshalBits,List.length_append,List.length_replicate,hlen]
    omega
  refine ⟨nc+(8*lit.length+7+1+(2*lit.length+3+1)),
    flags r1 false false true,output,records,?_,hgood,?_,hlen,hvalue⟩
  ·
    rw [hlit]
    omega
  · exact h

end SubexponentialSAT.SubexpMomentSourceProgram

end OAI.Algorithms
