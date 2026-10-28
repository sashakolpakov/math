import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyInput

namespace OAI.Algorithms

/-! Recover the native arithmetic invariants from the actual staged cache
words and an otherwise empty low workspace. No execution premise is used. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

def arithmeticCachePorts : List (Fin 256) := [5,10,104,192,193,194,201,202,203,204]

structure ArithmeticInput (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (s : Store) : Prop where
  modulus : s 194=M.bits
  lowModulus : s 5=s 194
  width : (s 202).length=baseWidth 3 t
  lowWidth : s 10=s 202
  zero : s 203=cache.zero.val
  table : s 201=RingTriple.tableEncoding (HornerProgram.modelTable t a M cache)
  degree : (s 204).length=d
  fullZero : s 104=List.replicate (d*baseWidth 3 t) false
  clean : ∀ i:Fin 256,i.val < 205 → i∉arithmeticCachePorts → s i=[]

variable {t d : ℕ} {a : RingModel.Data d}
  {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t} {s : Store}

theorem ArithmeticInput.pairReady (h : ArithmeticInput t a M cache s) :
    PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache) s (s 10) (fun _=>[]) := by
  constructor
  · intro j h8 h9
    fin_cases j <;>
      simp_all [RingCall.ports,RingCall.port,RingScan.serviceState,RingScan.serviceWorkState,
        RingScan.serviceTapes,h.modulus,h.lowWidth,h.zero,h.table]
    all_goals exact h.clean _ (by decide) (by decide)
  · intro i
    fin_cases i <;>
      simp [SubexpConvolutionPair.lowPort,SubexpJetCellProgram.scalarPorts,
        DensePolynomialLoop.ready,DensePolynomialLoop.state,DensePolynomialLoop.stackArray,Fin.addCases,
        h.lowModulus,h.modulus,h.lowWidth]
    all_goals first
      | exact h.lowModulus.trans h.modulus
      | exact h.lowWidth
      | (apply h.clean <;> decide)

  · simp [h.fullZero]
  · simpa only [h.lowWidth] using h.width
  · exact h.degree
  · exact h.clean 120 (by decide) (by decide)
  · intro j hlo hhi
    apply h.clean j (by omega)
    intro hj
    simp only [arithmeticCachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hj
    rcases hj with hj|hj|hj|hj|hj|hj|hj|hj|hj|hj <;> subst j <;> omega

theorem ArithmeticInput.scalarReady (h : ArithmeticInput t a M cache s) :
    HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) s := by
  refine ⟨⟨h.clean 120 (by decide) (by decide),?_⟩,h.modulus,h.width,h.zero,h.table,h.degree⟩
  intro i
  fin_cases i <;>
    simp [ReconstructionProgram.RingAdapter.ports,ReconstructionProgram.RingAdapter.finalNative,
      ReconstructionProgram.RingAdapter.nativeStacks]
  all_goals exact h.clean _ (by decide) (by decide)

theorem ArithmeticInput.buffers (h : ArithmeticInput t a M cache s) :
    ∀ i,s (bufferPorts i)=[] := by
  intro i
  apply h.clean
  · fin_cases i <;> decide
  · fin_cases i <;> decide

private theorem lowScratch_not_arithmeticCachePorts :
    ∀ i : Fin 256, i∈lowScratch → i∉arithmeticCachePorts := by
  intro i hi ha
  simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
    coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
  simp [arithmeticCachePorts] at ha
  omega

/-- The caller supplies the preserved masters and high-workspace emptiness;
the remaining native preconditions follow from the staged low cache words. -/
theorem LowInput.of_staged {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
    {rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)}
    (h : ArithmeticInput t a M cache s)
    (hB : 0 < baseWidth 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzero : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1=
      List.replicate (d*baseWidth 3 t) false)
    (hrows : s 205=Encoding.encodeList Fixed.encode (rows.map Prod.fst))
    (hchoice : s 206=rows.map Prod.snd)
    (h207 : s 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (h208 : s 208=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (h209 : s 209=RingProgram.flat theta)
    (h210 : (s 210).length=N) (h211 : (s 211).length=d*baseWidth 3 t)
    (h212 : (s 212).length=rows.length) (h213 : s 213=List.replicate J true)
    (he : ∀ i∈lowScratch,205 ≤ i.val → s i=[]) :
    LowInput t a M cache J N theta rows s := by
  refine ⟨hB,hz,h.pairReady,h.scalarReady,h.buffers,
    h.clean 121 (by decide) (by decide),h.clean 122 (by decide) (by decide),hzero,
    hrows,hchoice,h207,h208,h209,h210,h211,h212,h213,h.fullZero,?_⟩
  intro i hi
  by_cases hl : i.val < 205
  · exact h.clean i hl (lowScratch_not_arithmeticCachePorts i hi)
  · exact he i hi (by omega)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
