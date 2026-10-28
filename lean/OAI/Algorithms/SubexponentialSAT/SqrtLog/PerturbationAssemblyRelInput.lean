import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyFactorInput

namespace OAI.Algorithms

/-! Common physical input invariant, independent of whichever exact source
arrays are returned by the next native source execution. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

structure StagedInput (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d) (s : OuterStore) (n : ℕ) : Prop where
  arithmetic : ArithmeticInput t a M cache (projectInner s)
  widthPositive : 0 < baseWidth 3 t
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  zeroBits : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1=
    List.replicate (d*baseWidth 3 t) false
  choicesLength : (s 546).length=n
  zeroWord : s 547=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  oneWord : s 548=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  thetaWord : s 549=RingProgram.flat theta
  sourceCount : (s 550).length=N
  wordWidth : (s 551).length=d*baseWidth 3 t
  ambientCount : s 552=List.replicate n true
  targetCount : s 553=List.replicate J true
  workEmpty : ∀ i∈lowScratch,205 ≤ i.val → s (innerPort i)=[]

def pairChoice {B d N : ℕ} (xs : List (Fixed.Array B d N)) (choice : List Bool) := xs.zip choice

theorem pairChoice_length {B d N : ℕ} (xs : List (Fixed.Array B d N)) (choice : List Bool)
    (h : xs.length=choice.length) : (pairChoice xs choice).length=xs.length := by
  simp [pairChoice,List.length_zip,h]

theorem pairChoice_rows {B d N : ℕ} (xs : List (Fixed.Array B d N)) (choice : List Bool)
    (h : xs.length=choice.length) : (pairChoice xs choice).map Prod.fst=xs := by
  rw [←List.unzip_fst]
  exact congrArg Prod.fst (List.unzip_zip h)

theorem pairChoice_choices {B d N : ℕ} (xs : List (Fixed.Array B d N)) (choice : List Bool)
    (h : xs.length=choice.length) : (pairChoice xs choice).map Prod.snd=choice := by
  rw [←List.unzip_snd]
  exact congrArg Prod.snd (List.unzip_zip h)

variable {t d : ℕ} {a : RingModel.Data d}
  {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
  {J N : ℕ} {theta : Coeff (baseWidth 3 t) d} {s : OuterStore} {n : ℕ}

theorem StagedInput.factorInput (h : StagedInput t a M cache J N theta s n)
    (xs : List (Fixed.Array (baseWidth 3 t) d N)) (hx : xs.length=n) :
    FactorInput t a M cache J N theta (fun _=>pairChoice xs (s 546)) s n := by
  have hc : xs.length=(s 546).length := hx.trans h.choicesLength.symm
  refine ⟨h.arithmetic,h.widthPositive,h.zeroCanonical,h.zeroBits,?_,?_,h.zeroWord,h.oneWord,
    h.thetaWord,h.sourceCount,h.wordWidth,h.ambientCount,h.targetCount,h.workEmpty⟩
  · intro j hj
    exact (pairChoice_length xs (s 546) hc).trans hx
  · intro j hj
    exact (pairChoice_choices xs (s 546) hc).symm

theorem StagedInput.rowInput (h : StagedInput t a M cache J N theta s n)
    (xs : List (Fixed.Array (baseWidth 3 t) d N)) (hx : xs.length=n)
    (j : ℕ) (hj : j < n) (acc : List Bool) :
    LowInput t a M cache J N theta (pairChoice xs (s 546))
      (projectInner (literalSourceState (literalReady s (List.replicate j true) acc)
        j (Encoding.encodeList Fixed.encode xs))) := by
  have hh := (h.factorInput xs hx).lowInput j hj acc
  simpa only [sourceWords,pairChoice_rows xs (s 546) (hx.trans h.choicesLength.symm)] using hh

theorem StagedInput.scratch (h : StagedInput t a M cache J N theta s n)
    (i : Fin 256) (hi : i∈lowScratch) : s (innerPort i)=[] := by
  by_cases hlo : i.val < 205
  · apply h.arithmetic.clean i hlo
    intro ha
    simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
      coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
    simp [arithmeticCachePorts] at ha
    omega
  · exact h.workEmpty i hi (by omega)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
