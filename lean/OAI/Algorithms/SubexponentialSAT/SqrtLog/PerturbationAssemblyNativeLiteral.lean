import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyLiteral
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyInput

namespace OAI.Algorithms

/-! Native source-to-literal composition. The source premise is the execution
of one fixed finite source command; all beta, shift, and emission services are
fully discharged by LowInput.run. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def sourceWords {B d N : ℕ} (rows : List (Fixed.Array B d N × Bool)) : List Bool :=
  Encoding.encodeList Fixed.encode (rows.map Prod.fst)

def literalSourceState (s : OuterStore) (j : ℕ) (words : List Bool) : OuterStore :=
  Function.update (Function.update s 555 (Encoding.encodeNat j)) 545 words

theorem sourceState_other (s : OuterStore) (j : ℕ) (words : List Bool)
    (i : Fin 256) (h205 : i≠205) (h215 : i≠215) :
    projectInner (literalSourceState s j words) i=projectInner s i := by
  have h545 : innerPort i≠545 := by
    change innerPort i≠innerPort 205
    exact fun h=>h205 (innerPort_injective h)
  have h555 : innerPort i≠555 := by
    change innerPort i≠innerPort 215
    exact fun h=>h215 (innerPort_injective h)
  simp [literalSourceState,projectInner,h545,h555]

def nativeLiteralValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool)) (s : OuterStore) (j : ℕ) : List Bool :=
  if (s 574).getD j false then
    Encoding.frame (originKey rows.length)++
      Encoding.frame (if (s 575).getD j false then s 548 else s 547)
  else lowOutput t a M cache J N theta rows []

def nativePayloadBudget (s : OuterStore) (j n W Ksource Klow : ℕ) : ℕ :=
  10*j+9*(s 574).length+18 + (10*j+42*n+29*W+109)+Ksource+Klow+1

/-- One actual original-variable entry. The coefficient rows are produced by
source, never supplied as a pre-existing table to this program. -/
theorem nativeLiteral_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool))
    (s : OuterStore) (source : OuterCode) (j Ksource : ℕ)
    (hj : s 573=List.replicate j true)
    (h545 : s 545=[]) (h555 : s 555=[]) (h557 : s 557=[])
    (hm : (s 575).length=rows.length)
    (he : ∀ i∈entryScratch,s (innerPort i)=[])
    (hsource : ExecutesOuter source Ksource
      (Function.update s 555 (Encoding.encodeNat j))
      (literalSourceState s j (sourceWords rows)))
    (hinput : LowInput t a M cache J N theta rows
      (projectInner (literalSourceState s j (sourceWords rows)))) :
    ExecutesOuter (literalIteration source)
      (7*j+nativePayloadBudget s j rows.length (d*baseWidth 3 t) Ksource
        (lowBudget (projectInner (literalSourceState s j (sourceWords rows))) rows.length N J t d)+
        22*(j+1)+19*(nativeLiteralValue t a M cache J N theta rows s j).length+
        2*(sourceWords rows).length+54) s
      (Function.update s 569 (Encoding.frame (Encoding.encodeNat j)++
        Encoding.frame (nativeLiteralValue t a M cache J N theta rows s j)++s 569)) := by
  let keyed := Function.update s 555 (Encoding.encodeNat j)
  let input := literalSourceState s j (sourceWords rows)
  let low := lowOutput t a M cache J N theta rows []
  let physicalRows := if (s 574).getD j false then [] else sourceWords rows
  have hs217 : (projectInner input) 217=[] := by
    simpa [input,literalSourceState,projectInner,Function.comp_def,innerPort] using h557
  have hlow : ExecutesIn prepareLow (lowBudget (projectInner input) rows.length N J t d)
      (projectInner input) (Function.update (projectInner input) 217 low) := by
    have hs217' : projectInner (literalSourceState s j (sourceWords rows)) 217=[] := hs217
    simpa only [low,hs217'] using hinput.run
  have horg : ∀ i∈originScratch,keyed (innerPort i)=[] := by
    intro i hi
    have hne : i ≠ 205 ∧ i ≠ 215 := by
      simp [originScratch] at hi
      omega
    have h := hinput.workEmpty i (by simp [lowScratch,hi])
    rw [sourceState_other s j (sourceWords rows) i hne.1 hne.2] at h
    have h555' : innerPort i≠555 := by
      change innerPort i≠innerPort 215
      exact fun e=>hne.2 (innerPort_injective e)
    simpa [keyed,projectInner,Function.comp_def,h555'] using h
  have hc220 : keyed 560=[] := by
    have h := hinput.workEmpty 220 (by simp [lowScratch,PerturbationBetaProgram.workPorts])
    simpa [literalSourceState,projectInner,Function.comp_def,innerPort,keyed] using h
  have hz : (keyed 547).length=d*baseWidth 3 t := by
    have h := congrArg List.length hinput.zeroWord
    simpa [literalSourceState,projectInner,Function.comp_def,innerPort,keyed] using h
  have ho : (keyed 548).length=d*baseWidth 3 t := by
    have h := congrArg List.length hinput.oneWord
    simpa [literalSourceState,projectInner,Function.comp_def,innerPort,keyed] using h
  have hn : (keyed 552).length=rows.length := by
    simpa [literalSourceState,projectInner,Function.comp_def,innerPort,keyed] using hinput.ambientCount
  have hp := literalPayload_run keyed source rows.length (d*baseWidth 3 t) Ksource
    (lowBudget (projectInner input) rows.length N J t d) (sourceWords rows) low hn
    (by simpa [keyed] using hm) hz ho hc220 horg hsource hlow
  have hp' : ExecutesOuter (literalPayload source)
      (nativePayloadBudget s j rows.length (d*baseWidth 3 t) Ksource
        (lowBudget (projectInner input) rows.length N J t d)) keyed
      (Function.update (Function.update keyed 545 physicalRows) 557
        (nativeLiteralValue t a M cache J N theta rows s j)) := by
    convert hp using 1
    · simp [nativePayloadBudget,keyed,hj]
    · cases hb:(s 574).getD j false <;>
        change (s 574)[j]?.getD false = _ at hb
      all_goals simp [physicalRows,nativeLiteralValue,keyed,hj,hb,low,h557]
      all_goals
        funext i
        by_cases hi : i=545 <;> by_cases hj' : i=557 <;>
          simp [Function.update_apply,hi,hj',h545]
  have h := literalIteration_run s source j _ physicalRows
    (nativeLiteralValue t a M cache J N theta rows s j) hj h545 h555 h557 he hp'
  apply h.mono
  have hw : physicalRows.length ≤ (sourceWords rows).length := by
    dsimp [physicalRows]
    split <;> simp
  dsimp only [input]
  omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
