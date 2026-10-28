import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyInputReady
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyNativeFactor

namespace OAI.Algorithms

/-! One invariant of the physically staged masters yields every per-literal
low-worker precondition. No beta, shifted polynomial, or output table occurs
as an input hypothesis. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem ArithmeticInput.frame_low {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {s u : Store} (h : ArithmeticInput t a M cache s)
    (hf : ∀ i:Fin 256,i.val < 205 → u i=s i) : ArithmeticInput t a M cache u := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hf 194 (by decide)] using h.modulus
  · simpa only [hf 5 (by decide),hf 194 (by decide)] using h.lowModulus
  · simpa only [hf 202 (by decide)] using h.width
  · simpa only [hf 10 (by decide),hf 202 (by decide)] using h.lowWidth
  · simpa only [hf 203 (by decide)] using h.zero
  · simpa only [hf 201 (by decide)] using h.table
  · simpa only [hf 204 (by decide)] using h.degree
  · simpa only [hf 104 (by decide)] using h.fullZero
  · intro i hi hn
    exact (hf i hi).trans (h.clean i hi hn)

structure FactorInput (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : FactorRows t N (d:=d)) (s : OuterStore) (n : ℕ) : Prop where
  arithmetic : ArithmeticInput t a M cache (projectInner s)
  widthPositive : 0 < baseWidth 3 t
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  zeroBits : RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1=
    List.replicate (d*baseWidth 3 t) false
  rowsLength : ∀ j,j < n → (rows j).length=n
  choices : ∀ j,j < n → s 546=(rows j).map Prod.snd
  zeroWord : s 547=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  oneWord : s 548=RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  thetaWord : s 549=RingProgram.flat theta
  sourceCount : (s 550).length=N
  wordWidth : (s 551).length=d*baseWidth 3 t
  ambientCount : s 552=List.replicate n true
  targetCount : s 553=List.replicate J true
  workEmpty : ∀ i∈lowScratch,205 ≤ i.val → s (innerPort i)=[]

theorem FactorInput.lowInput {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {J N : ℕ} {theta : Coeff (baseWidth 3 t) d}
    {rows : FactorRows t N (d:=d)} {s : OuterStore} {n : ℕ}
    (h : FactorInput t a M cache J N theta rows s n) (j : ℕ) (hj : j < n)
    (acc : List Bool) : LowInput t a M cache J N theta (rows j)
      (projectInner (literalSourceState (literalReady s (List.replicate j true) acc)
        j (sourceWords (rows j)))) := by
  let u := literalSourceState (literalReady s (List.replicate j true) acc)
    j (sourceWords (rows j))
  have hf : ∀ i:Fin 256,i≠205 → i≠215 → i≠229 → i≠233 →
      projectInner u i=projectInner s i := by
    intro i h205 h215 h229 h233
    have hn : innerPort i≠545 ∧ innerPort i≠555 ∧ innerPort i≠569 ∧ innerPort i≠573 := by
      exact ⟨fun he=>h205 (innerPort_injective he),fun he=>h215 (innerPort_injective he),
        fun he=>h229 (innerPort_injective he),fun he=>h233 (innerPort_injective he)⟩
    simp [u,literalSourceState,literalReady,projectInner,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2]
  have ha : ArithmeticInput t a M cache (projectInner u) := h.arithmetic.frame_low (by
    intro i hi
    apply hf i
    all_goals intro he; subst i; norm_num at hi)
  change LowInput t a M cache J N theta (rows j) (projectInner u)
  apply LowInput.of_staged ha h.widthPositive h.zeroCanonical h.zeroBits
  · simp [u,literalSourceState,projectInner,innerPort,sourceWords]
  · rw [hf 206 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.choices j hj
  · rw [hf 207 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.zeroWord
  · rw [hf 208 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.oneWord
  · rw [hf 209 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.thetaWord
  · rw [hf 210 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.sourceCount
  · rw [hf 211 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.wordWidth
  · rw [hf 212 (by decide) (by decide) (by decide) (by decide)]
    change (s 552).length=(rows j).length
    simp [h.ambientCount,h.rowsLength j hj]
  · rw [hf 213 (by decide) (by decide) (by decide) (by decide)]
    simpa [projectInner,innerPort,Function.comp_def] using h.targetCount
  · intro i hi hlarge
    have hn : i ≠ 205 ∧ i ≠ 215 ∧ i ≠ 229 ∧ i ≠ 233 := by
      simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
        coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
      omega
    exact (hf i hn.1 hn.2.1 hn.2.2.1 hn.2.2.2).trans (h.workEmpty i hi hlarge)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
