import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyLow

namespace OAI.Algorithms

/-! Input-only contract for the closed native low-variable worker. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- This record describes only the actual incoming words, arithmetic caches,
and empty work tapes. It contains no evaluation or execution oracle. -/
structure LowInput (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (s : Store) : Prop where
  widthPositive : 0 < baseWidth 3 t
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  pairReady : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache) s (s 10) (fun _=>[])
  scalarReady : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) s
  buffersEmpty : ∀ i,s (bufferPorts i)=[]
  empty121 : s 121=[]
  empty122 : s 122=[]
  zeroBits : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1=
    List.replicate (d*baseWidth 3 t) false
  sourceRows : s 205=Encoding.encodeList Fixed.encode (rows.map Prod.fst)
  choices : s 206=rows.map Prod.snd
  zeroWord : s 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  oneWord : s 208=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  thetaWord : s 209=RingProgram.flat theta
  sourceCount : (s 210).length=N
  wordWidth : (s 211).length=d*baseWidth 3 t
  ambientCount : (s 212).length=rows.length
  targetCount : s 213=List.replicate J true
  widthZeros : s 104=List.replicate (d*baseWidth 3 t) false
  workEmpty : ∀ i∈lowScratch,s i=[]

theorem LowInput.run {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
    {rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)} {s : Store}
    (h : LowInput t a M cache J N theta rows s) :
    ExecutesIn prepareLow (lowBudget s rows.length N J t d) s
      (Function.update s 217 (lowOutput t a M cache J N theta rows (s 217))) :=
  prepareLow_run t a M cache h.widthPositive h.zeroCanonical s J N (s 10) (fun _=>[])
    h.pairReady h.scalarReady h.buffersEmpty h.empty121 h.empty122 h.zeroBits theta rows
    h.sourceRows h.choices h.zeroWord h.oneWord h.thetaWord h.sourceCount h.wordWidth
    h.ambientCount h.targetCount h.widthZeros h.workEmpty

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
