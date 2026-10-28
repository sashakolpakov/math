import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyRelInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyRelLiteral
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyFactorBounds

namespace OAI.Algorithms

/-! Native literal execution with the exact source array witness returned by
that call. The persistent input contains only source metadata and arithmetic
masters; beta and shifted coefficients are computed by prepareLow. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

def payloadRelation (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d) (n : ℕ)
    (Rows : ℕ → List (Fixed.Array (baseWidth 3 t) d N) → Prop)
    (s : OuterStore) (j : ℕ) (payload : List Bool) : Prop :=
  if (s 574).getD j false then
    payload=Encoding.frame (originKey n)++
      Encoding.frame (if (s 575).getD j false then s 548 else s 547)
  else ∃ xs,xs.length=n ∧ Rows j xs ∧
    payload=lowOutput t a M cache J N theta (pairChoice xs (s 546)) []

theorem nativeLiteral_rel (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d) (n : ℕ)
    (Rows : ℕ → List (Fixed.Array (baseWidth 3 t) d N) → Prop)
    (s : OuterStore) (source : OuterCode) (j Ksource : ℕ) (acc : List Bool)
    (h : StagedInput t a M cache J N theta s n) (hj : j < n)
    (h545 : s 545=[]) (h555 : s 555=[]) (h557 : s 557=[])
    (hm : (s 575).length=n)
    (hsource : (s 574).getD j false=false → ∀ regs : Fin 16 → Bool,
      ∃ xs k rf,xs.length=n ∧ Rows j xs ∧ k ≤ Ksource ∧
      Eval source k
        (⟨regs,Function.update (literalReady s (List.replicate j true) acc)
          555 (Encoding.encodeNat j)⟩ : OuterData)
        (⟨rf,literalSourceState (literalReady s (List.replicate j true) acc)
          j (Encoding.encodeList Fixed.encode xs)⟩ : OuterData))
    (regs : Fin 16 → Bool) :
    ∃ payload k rf,
      k ≤ literalWorkPolynomial n N J t d
        ((s 532).length+(s 533).length+(s 583).length) (s 574).length Ksource ∧
      payload.length ≤ incidenceBitsBound n J (d*baseWidth 3 t) ∧
      payloadRelation t a M cache J N theta n Rows s j payload ∧
      Eval (literalIteration source) k
        (⟨regs,literalReady s (List.replicate j true) acc⟩ : OuterData)
        (⟨rf,literalReady s (List.replicate j true)
          (Encoding.frame (Encoding.encodeNat j)++Encoding.frame payload++acc)⟩ : OuterData) := by
  let current := literalReady s (List.replicate j true) acc
  let keyed := Function.update current 555 (Encoding.encodeNat j)
  let W := d*baseWidth 3 t
  let Lrows := n*(2*(N*W)+2)+1
  let Lpayload := incidenceBitsBound n J W
  let Klow := lowWorkPolynomial n N J t d
    ((s 532).length+(s 533).length+(s 583).length)
  let Kpayload := 10*j+9*(s 574).length+18+(10*j+42*n+29*W+109)+Ksource+Klow+1
  have he : ∀ i∈entryScratch,current (innerPort i)=[] := by
    intro i hi
    have hn : innerPort i≠573 ∧ innerPort i≠569 := by
      constructor <;> intro heq <;>
        have hv := congrArg Fin.val heq <;>
        simp [innerPort, entryScratch] at hv hi <;> omega
    have hilow : i ∈ lowScratch := by
      simp only [entryScratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [lowScratch, originScratch, targetScratch]
    simpa [current,literalReady,Function.update_apply,hn.1,hn.2] using
      h.scratch i hilow
  have ho : ∀ i∈originScratch,keyed (innerPort i)=[] := by
    intro i hi
    have hn : innerPort i≠573 ∧ innerPort i≠569 ∧ innerPort i≠555 := by
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [innerPort, originScratch] at hv hi
        omega
      constructor <;> intro heq <;>
        have hv := congrArg Fin.val heq <;>
        simp [innerPort, originScratch] at hv hi <;> omega
    simpa [keyed,current,literalReady,Function.update_apply,hn.1,hn.2.1,hn.2.2] using
      h.scratch i (by simp [lowScratch, hi])
  have h220 : keyed 560=[] := by
    simpa [keyed,current,literalReady,innerPort] using h.scratch 220 (by decide)
  have hz : (keyed 547).length=W := by
    simpa [keyed,current,literalReady,W] using congrArg List.length h.zeroWord
  have h1 : (keyed 548).length=W := by
    simpa [keyed,current,literalReady,W] using congrArg List.length h.oneWord
  have hp : ∀ r : Fin 16 → Bool, ∃ words payload k rf,k ≤ Kpayload ∧
      words.length ≤ Lrows ∧ payload.length ≤ Lpayload ∧
      payloadRelation t a M cache J N theta n Rows s j payload ∧
      Eval (literalPayload source) k (⟨r,keyed⟩ : OuterData)
        (⟨rf,Function.update (Function.update keyed 545 words) 557 payload⟩ : OuterData) := by
    intro r
    suffices hs : ∃ words payload k rf,
        k ≤ 10*(keyed 573).length+9*(keyed 574).length+18+
          (10*(keyed 573).length+42*n+29*W+109)+Ksource+Klow+1 ∧
        words.length ≤ Lrows ∧ payload.length ≤ Lpayload ∧
        payloadRelation t a M cache J N theta n Rows s j payload ∧
        Eval (literalPayload source) k (⟨r,keyed⟩ : OuterData)
          (⟨rf,Function.update (Function.update keyed 545 words) 557 payload⟩ : OuterData) by
      simpa [Kpayload,keyed,current,literalReady] using hs
    refine literalPayload_rel keyed source n W Ksource Klow Lrows Lpayload
      (payloadRelation t a M cache J N theta n Rows s j)
      (by simp [keyed,current,literalReady,h.ambientCount])
      (by simpa [keyed,current,literalReady] using hm) hz h1
      (by simpa [keyed,current,literalReady] using h545)
      (by simpa [keyed,current,literalReady] using h557) h220 ho ?_ ?_ ?_ r
    · intro hb rs
      have hb' : (s 574).getD j false=false := by simpa [keyed,current,literalReady] using hb
      obtain ⟨xs,ns,rf,hx,hRows,hns,hes⟩ := hsource hb' rs
      let pairs := pairChoice xs (s 546)
      have hlen : pairs.length=n := (pairChoice_length xs (s 546)
        (hx.trans h.choicesLength.symm)).trans hx
      have hi := h.rowInput xs hx j hj acc
      have hlow := hi.run
      have h217 : (projectInner (literalSourceState current j (Encoding.encodeList Fixed.encode xs))) 217=[] := by
        simp [projectInner,literalSourceState,current,literalReady,innerPort,h557]
      have hpairlen : (pairChoice xs (s 546)).length=n := hlen
      have hE : ((projectInner (literalSourceState current j (Encoding.encodeList Fixed.encode xs))) 192).length+
          ((projectInner (literalSourceState current j (Encoding.encodeList Fixed.encode xs))) 193).length+
          ((projectInner (literalSourceState current j (Encoding.encodeList Fixed.encode xs))) 243).length=
          (s 532).length+(s 533).length+(s 583).length := by
        simp [projectInner,literalSourceState,current,literalReady,innerPort]
      have hlb : lowBudget (projectInner (literalSourceState current j
          (Encoding.encodeList Fixed.encode xs))) n N J t d ≤ Klow := by
        have hb := hi.budget_bound
        rw [hpairlen, hE] at hb
        simpa only [current, Klow] using hb
      have hrun : ExecutesIn prepareLow Klow
          (projectInner (Function.update keyed 545 (Encoding.encodeList Fixed.encode xs)))
          (Function.update (projectInner (Function.update keyed 545 (Encoding.encodeList Fixed.encode xs)))
            217 (lowOutput t a M cache J N theta pairs [])) := by
        rw [hpairlen] at hlow
        have h217' : (projectInner (literalSourceState
            (literalReady s (List.replicate j true) acc) j
            (Encoding.encodeList Fixed.encode xs))) 217=[] := by
          simpa only [current] using h217
        rw [h217'] at hlow
        have hh := hlow.mono hlb
        change ExecutesIn prepareLow Klow
          (projectInner (literalSourceState (literalReady s (List.replicate j true) acc) j
            (Encoding.encodeList Fixed.encode xs)))
          (Function.update (projectInner (literalSourceState
            (literalReady s (List.replicate j true) acc) j
            (Encoding.encodeList Fixed.encode xs))) 217
            (lowOutput t a M cache J N theta (pairChoice xs (s 546)) []))
        exact hh
      refine ⟨Encoding.encodeList Fixed.encode xs,lowOutput t a M cache J N theta pairs [],
        ns,rf,hns,?_,?_,?_,hes,hrun⟩
      · have hs := sourceWords_length pairs
        simpa [sourceWords,pairs,pairChoice_rows xs (s 546) (hx.trans h.choicesLength.symm),
          hlen,Lrows,W] using hs.le
      · simpa [Lpayload,W,hlen] using lowOutput_length t a M cache J N theta pairs []
      · simp only [payloadRelation,hb',Bool.false_eq_true,ite_false]
        exact ⟨xs,hx,hRows,rfl⟩
    · intro hb
      have hb' : (s 574).getD j false=true := by simpa [keyed,current,literalReady] using hb
      simp only [payloadRelation,hb',ite_true]
      simp [keyed,current,literalReady]
    · have hk : (originKey n).length=n+2 := by
        simp [originKey,PerturbationEmitProgram.keyBits,PerturbationProgram.Key.bits]
      have hw : (if (keyed 575).getD (keyed 573).length false then keyed 548 else keyed 547).length=W := by
        split
        · exact h1
        · exact hz
      simp only [List.length_append,Encoding.length_frame,hw,hk]
      unfold Lpayload incidenceBitsBound
      omega
  obtain ⟨payload,k,rf,hk,hlen,hgood,heval⟩ := literalIteration_rel current source j Kpayload
    Lrows Lpayload (payloadRelation t a M cache J N theta n Rows s j)
    (by simp [current,literalReady])
    (by simpa [current,literalReady] using h545)
    (by simpa [current,literalReady] using h555)
    (by simpa [current,literalReady] using h557) he hp regs
  refine ⟨payload,k,rf,?_,hlen,hgood,?_⟩
  · dsimp only [Kpayload,Klow,Lpayload,Lrows,W] at hk
    unfold literalWorkPolynomial
    dsimp only
    omega
  · simpa [current,literalReady,List.append_assoc] using heval

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
