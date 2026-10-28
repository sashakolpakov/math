import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalarFromCountsDefinitions

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

private theorem binomial_ports_cover (j : Fin 40)
    (h : j=2 ∨ j=8 ∨ j=10 ∨ (12 ≤ j.val ∧ j.val ≤ 28)) :
    j∈Set.range binomialPorts := by
  have hc : ∀ k : Fin 40, k=2 ∨ k=8 ∨ k=10 ∨ (12 ≤ k.val ∧ k.val ≤ 28) →
      k∈Set.range binomialPorts := by decide
  exact hc j h

private theorem numerator_ports_cover (j : Fin 40)
    (h : j.val ≤ 4 ∨ j=9 ∨ j=11 ∨ (12 ≤ j.val ∧ j.val ≤ 27) ∨ j=37 ∨ j=38) :
    j∈Set.range numeratorPorts := by
  have hc : ∀ k : Fin 40, k.val ≤ 4 ∨ k=9 ∨ k=11 ∨ (12 ≤ k.val ∧ k.val ≤ 27) ∨ k=37 ∨ k=38 →
      k∈Set.range numeratorPorts := by decide
  exact hc j h

private theorem binomial_project (c : Saved) (regs : Fin 9 → Bool)
    (h n rc ac : List Bool) :
    projectState regs8 binomialPorts (state c regs [] h n rc ac [] [] ([],[])) =
      LayoutBinomialProgram.finalState (regs ∘ regs8) h rc c.width [] [] [] := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [state,binomialPorts]

private theorem binomial_embed (c : Saved) (regs : Fin 9 → Bool) (rf : Fin 8 → Bool)
    (h n rc ac bp bn : List Bool) :
    ∃ rout, embedState regs8 binomialPorts (state c regs [] h n rc ac [] [] ([],[]))
      (LayoutBinomialProgram.finalState rf [] [] c.width [] bp bn) =
      state c rout [] [] n [] ac bp bn ([],[]) := by
  let start := state c regs [] h n rc ac [] [] ([],[])
  let target := embedState regs8 binomialPorts start
    (LayoutBinomialProgram.finalState rf [] [] c.width [] bp bn)
  refine ⟨target.regs,?_⟩
  apply embedState_eq_of_ports regs8 binomialPorts _ _ _ regs8_injective binomialPorts_injective
  · intro i; exact embedState_register regs8 binomialPorts start
      (LayoutBinomialProgram.finalState rf [] [] c.width [] bp bn) regs8_injective i
  · intro i hi; exact embedState_register_frame regs8 binomialPorts start
      (LayoutBinomialProgram.finalState rf [] [] c.width [] bp bn) i hi
  · intro i; fin_cases i <;> simp [state,binomialPorts,LayoutBinomialProgram.finalState]
  · intro i hi
    have hn := fun hj => hi (binomial_ports_cover i hj)
    fin_cases i <;> first | exact (hn (by decide)).elim | simp [state]

private theorem numerator_project (c : Saved) (cache : Cache) (regs : Fin 9 → Bool)
    (n ac : List Bool)
    (hp : cache.Hpositive.flatten=c.hp) (hn : cache.Hnegative.flatten=c.hn)
    (hw : cache.width=c.width) (hpower : cache.power=c.power) :
    projectState id numeratorPorts
      (state c regs [] [] n [] ac cache.Bpositive.flatten cache.Bnegative.flatten ([],[])) =
      numeratorState cache regs n ac [] ([],[]) := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [state,numeratorPorts,hp,hn,hw,hpower]

private theorem numerator_embed (c : Saved) (cache : Cache) (regs rf : Fin 9 → Bool)
    (n ac : List Bool) (result : WordPair)
    (hp : cache.Hpositive.flatten=c.hp) (hn : cache.Hnegative.flatten=c.hn)
    (hw : cache.width=c.width) (hpower : cache.power=c.power) :
    embedState id numeratorPorts
      (state c regs [] [] n [] ac cache.Bpositive.flatten cache.Bnegative.flatten ([],[]))
      (numeratorState cache rf [] [] [] result) =
      state c rf [] [] [] [] [] cache.Bpositive.flatten cache.Bnegative.flatten result := by
  apply embedState_eq_of_ports id numeratorPorts _ _ _ Function.injective_id numeratorPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; fin_cases i <;> simp [state,numeratorPorts,numeratorState,hp,hn,hw,hpower]
  · intro i hi
    have hnone := fun hj => hi (numerator_ports_cover i hj)
    fin_cases i <;> first | exact (hnone (by decide)).elim | simp [state]

theorem binomial_eval (c : Saved) (regs : Fin 9 → Bool) (h n rc ac : List Bool)
    (hw : h.length+1 ≤ c.width.length) :
    ∃ t ≤ binomialCost h.length rc.length c.width.length,
    ∃ (rf : Fin 9 → Bool) (words : List (List Bool)), Eval binomial t
      (state c regs [] h n rc ac [] [] ([],[]))
      (state c rf [] [] n [] ac words.flatten (List.replicate (rc.length*c.width.length) false) ([],[])) ∧
      words.length=rc.length ∧ (∀ x∈words,x.length=c.width.length) ∧
      words.map BinaryArithmetic.toNat=(List.range rc.length).map h.length.choose := by
  obtain ⟨rf,words,⟨t,ht,he⟩,hlen,hword,hval⟩ :=
    LayoutBinomialProgram.finalProgram_runsIn (regs ∘ regs8) h rc c.width hw
  have hh := eval_call_from_state LayoutBinomialProgram.finalProgram regs8 binomialPorts
    (state c regs [] h n rc ac [] [] ([],[])) regs8_injective binomialPorts_injective
    (by simpa only [binomial_project] using he)
  obtain ⟨rout,hrout⟩ := binomial_embed c regs rf h n rc ac words.flatten
    (List.replicate (rc.length*c.width.length) false)
  rw [hrout] at hh
  exact ⟨t,ht,rout,words,hh,hlen,hword,hval⟩

theorem numerator_eval (c : Saved) (cache : Cache) (regs : Fin 9 → Bool)
    (n ac : List Bool) (A R d h Q : ℕ)
    (hp : cache.Hpositive.flatten=c.hp) (hn : cache.Hnegative.flatten=c.hn)
    (hw : cache.width=c.width) (hpower : cache.power=c.power)
    (hc : n.length=R-d) (ha : ac.length=A)
    (hu : cache.Uniform) (hf : cache.Fits (R-d)) (hv : cache.Values A R h) (hm : cache.Totals A R h)
    (hAQ : A ≤ Q) (hQ : 1 ≤ Q) (hhQ : h ≤ Q) :
    ∃ t ≤ numeratorPrepareCost (R-d) A c.width.length (pairLength c.power)+
      numeratorFoldCost (R-d) c.width.length (pairLength c.power)+1,
    ∃ rf result, Eval numerator t
      (state c regs [] [] n [] ac cache.Bpositive.flatten cache.Bnegative.flatten ([],[]))
      (state c rf [] [] [] [] [] cache.Bpositive.flatten cache.Bnegative.flatten result) ∧
      pairValue result=LayoutCoefficientAlgorithm.scalarSum A R d h ∧
      wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-d)*termGrowth (2*c.width.length+pairLength c.power) := by
  obtain ⟨rf,result,⟨t,ht,he⟩,hval,htotal,hlen⟩ :=
    numeratorProgram_runsIn cache regs n ac A R d h Q hc ha hu hf hv hm hAQ hQ hhQ
  have hh := eval_call_from_state numeratorProgram id numeratorPorts
    (state c regs [] [] n [] ac cache.Bpositive.flatten cache.Bnegative.flatten ([],[]))
    Function.injective_id numeratorPorts_injective
    (by simpa only [numerator_project c cache regs n ac hp hn hw hpower] using he)
  rw [numerator_embed c cache regs rf n ac result hp hn hw hpower] at hh
  refine ⟨t,?_,rf,result,hh,hval,htotal,?_⟩
  · simpa only [hw,hpower] using ht
  · simpa only [hw,hpower] using hlen

/-- Given the reusable H and power caches, the runtime unchanged/transposed
counts suffice to build all remaining operands and evaluate the numerator. -/
theorem program_runsIn (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (regs : Fin 9 → Bool) (a h : List Bool) (R d Q : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : wordTotal power=2^(R-1))
    (hwidth : h.length+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) (hhQ : h.length ≤ Q) :
    let c := unsignedSaved Hwords width power R a
    ∃ rf result,
      RunsIn program (totalCost a.length R d h.length width.length (pairLength power))
        ((state c regs (List.replicate (d+1) true) h [] [] [] [] [] ([],[])).withPC (some program.entry))
        ((state c rf [] [] [] [] [] [] [] result).withPC none) ∧
      pairValue result=LayoutCoefficientAlgorithm.scalarSum a.length R d h.length ∧
      wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-d)*termGrowth (2*width.length+pairLength power) := by
  intro c
  obtain ⟨r₁,h₁⟩ := copies_eval c regs (List.replicate (d+1) true) h
  obtain ⟨t₂,ht₂,r₂,h₂⟩ := count_eval c r₁ h c.r c.a R d
  obtain ⟨t₃,ht₃,r₃,Bwords,h₃,blen,bwords,bvalues⟩ :=
    binomial_eval c r₂ h (List.replicate (R-d) true) c.r c.a hwidth
  have crlen : c.r.length=R := by simp [c,unsignedSaved]
  have calen : c.a.length=a.length := rfl
  have cwlen : c.width.length=width.length := rfl
  rw [crlen] at ht₃ blen bvalues
  change t₃ ≤ binomialCost h.length R width.length at ht₃
  let cache := unsignedCache Hwords Bwords width power R
  obtain ⟨hu,hfit,hv,hm⟩ := unsignedCache_contract Hwords Bwords width power a.length R d h.length
    hlen blen hwords bwords hvalues bvalues hp hpt
  obtain ⟨t₄,ht₄,r₄,result,h₄,hv₄,hm₄,hl₄⟩ :=
    numerator_eval c cache r₃ (List.replicate (R-d) true) c.a a.length R d h.length Q
      rfl (by simp [cache,unsignedCache,c,unsignedSaved]) rfl rfl
      (by simp) rfl hu hfit hv hm hAQ hQ hhQ
  change t₄ ≤ numeratorPrepareCost (R-d) a.length width.length (pairLength power)+
    numeratorFoldCost (R-d) width.length (pairLength power)+1 at ht₄
  have bn : cache.Bnegative.flatten=List.replicate (R*width.length) false := by
    simp [cache,unsignedCache]
  have bp : cache.Bpositive.flatten=Bwords.flatten := rfl
  rw [bp,bn] at h₄
  have h₃' : Eval binomial t₃
      (state c r₂ [] h (List.replicate (R-d) true) c.r c.a [] [] ([],[]))
      (state c r₃ [] [] (List.replicate (R-d) true) [] c.a Bwords.flatten (List.replicate (R*width.length) false) ([],[])) := by
    simpa only [crlen, cwlen] using h₃
  obtain ⟨rf,h₅⟩ := cleanup_eval c r₄ Bwords.flatten (List.replicate (R*width.length) false) result
  have bflat : Bwords.flatten.length=R*width.length := by
    rw [List.length_flatten]
    have he : Bwords.map List.length=Bwords.map (fun _ => width.length) := by
      apply List.map_congr_left
      exact bwords
    rw [he]
    simp [blen]
  refine ⟨rf,result,⟨_,?_,compiled_halt_trace (h₁.seq (h₂.seq (h₃'.seq (h₄.seq h₅)))) 7 37⟩,hv₄,hm₄,hl₄⟩
  simp only [crlen,calen,bflat,List.length_replicate]
  unfold totalCost
  omega

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
