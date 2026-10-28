import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyNativeLiteral
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyTable

namespace OAI.Algorithms

/-! One complete selected-factor incidence slice, from the executed source
provider through all original variables to the interpreter's raw table ABI. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (t : ℕ) {d : ℕ} (a : RingModel.Data d)
  (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
  (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)

abbrev FactorRows := ℕ → List (Fixed.Array (baseWidth 3 t) d N × Bool)

def literalBudget (rows : List (Fixed.Array (baseWidth 3 t) d N × Bool))
    (s : OuterStore) (j Ksource : ℕ) : ℕ :=
  7*j+nativePayloadBudget s j rows.length (d*baseWidth 3 t) Ksource
    (lowBudget (projectInner (literalSourceState s j (sourceWords rows))) rows.length N J t d)+
    22*(j+1)+19*(nativeLiteralValue t a M cache J N theta rows s j).length+
    2*(sourceWords rows).length+54

def factorBodyBudget (rows : FactorRows t N (d:=d)) (s : OuterStore) (n Ksource : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n,literalBudget t a M cache J N theta (rows j) s j Ksource

def factorPayload (rows : FactorRows t N (d:=d)) (s : OuterStore) : ℕ → List Bool :=
  fun j => nativeLiteralValue t a M cache J N theta (rows j) s j

/-- The only program service parameter is the actual finite source provider.
Its premise is an execution trace from an empty source destination. Beta,
shifted coefficients, sparse dictionary, and incidence table are all outputs. -/
theorem nativeFactor_run (rows : FactorRows t N (d:=d)) (s : OuterStore)
    (source : OuterCode) (n Ksource : ℕ)
    (hcount : s 552=List.replicate n true)
    (hrows : ∀ j,j < n → (rows j).length=n)
    (h460 : s 460=[]) (h545 : s 545=[]) (h555 : s 555=[]) (h557 : s 557=[])
    (h561 : s 561=[]) (h569 : s 569=[]) (h573 : s 573=[]) (h585 : s 585=[])
    (hhigh : (s 575).length=n)
    (he : ∀ i∈entryScratch,s (innerPort i)=[])
    (hsource : ∀ j,j < n → ∀ acc, ExecutesOuter source Ksource
      (Function.update (literalReady s (List.replicate j true) acc) 555 (Encoding.encodeNat j))
      (literalSourceState (literalReady s (List.replicate j true) acc) j (sourceWords (rows j))))
    (hinput : ∀ j,j < n → ∀ acc, LowInput t a M cache J N theta (rows j)
      (projectInner (literalSourceState (literalReady s (List.replicate j true) acc)
        j (sourceWords (rows j))))) :
    ExecutesOuter (prepareFactor source)
      (7*n+n*(factorBodyBudget t a M cache J N theta rows s n Ksource+2)+
        6*(tableResult (factorPayload t a M cache J N theta rows s) n []).length+15) s
      (Function.update s 561 (Squarefree.Program.lookupRecords
        (HashCircuitProgram.incidenceEntries
          (fun (_ : Unit) (v : Fin n)=>factorPayload t a M cache J N theta rows s v.val) ()))) := by
  rw [← tableResult_incidence]
  apply prepareFactor_run s source (factorPayload t a M cache J N theta rows s)
    (factorBodyBudget t a M cache J N theta rows s n Ksource) n hcount
    h460 h573 h569 h561 h585
  intro j hj acc
  let current := literalReady s (List.replicate j true) acc
  have hec : ∀ i∈entryScratch,current (innerPort i)=[] := by
    intro i hi
    have hn : innerPort i ≠ 573 ∧ innerPort i ≠ 569 := by
      simp [entryScratch] at hi
      constructor <;> intro h
      all_goals
        have hv := congrArg Fin.val h
        simp [innerPort] at hv
        omega
    simpa [current,literalReady,Function.update_apply,hn.1,hn.2] using he i hi
  have h := nativeLiteral_run t a M cache J N theta (rows j) current source j Ksource
    (by simp [current,literalReady])
    (by simpa [current,literalReady] using h545)
    (by simpa [current,literalReady] using h555)
    (by simpa [current,literalReady] using h557)
    (by simpa [current,literalReady,hrows j hj] using hhigh) hec
    (hsource j hj acc) (hinput j hj acc)
  have hv : nativeLiteralValue t a M cache J N theta (rows j) current j=
      factorPayload t a M cache J N theta rows s j := by
    simp [nativeLiteralValue,factorPayload,current,literalReady]
  have hc : literalBudget t a M cache J N theta (rows j) current j Ksource=
      literalBudget t a M cache J N theta (rows j) s j Ksource := by
    simp [literalBudget,nativePayloadBudget,lowBudget,PerturbationBetaProgram.runBudget,
      PerturbationBetaProgram.initBudget,targetBudget,projectInner,
      innerPort,literalSourceState,current,literalReady,nativeLiteralValue]
  change ExecutesOuter (literalIteration source)
    (literalBudget t a M cache J N theta (rows j) current j Ksource) current
    (Function.update current 569 (Encoding.frame (Encoding.encodeNat j)++
      Encoding.frame (nativeLiteralValue t a M cache J N theta (rows j) current j)++current 569)) at h
  rw [hc,hv] at h
  have hout : Function.update current 569 (Encoding.frame (Encoding.encodeNat j)++
      Encoding.frame (factorPayload t a M cache J N theta rows s j)++current 569)=
      literalReady s (List.replicate j true)
        (tableRecord (factorPayload t a M cache J N theta rows s) j++acc) := by
    simp [current,literalReady,tableRecord,List.append_assoc]
  rw [hout] at h
  apply h.mono
  unfold factorBodyBudget
  exact Finset.single_le_sum
    (f := fun k => literalBudget t a M cache J N theta (rows k) s k Ksource)
    (fun _ _=>Nat.zero_le _) (Finset.mem_range.mpr hj)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
