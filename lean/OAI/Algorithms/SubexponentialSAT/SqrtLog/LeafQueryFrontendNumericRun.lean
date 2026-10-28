import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendConvert
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendConstants

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram


def numericStage (k : ℕ) : Code := .seq (copies [(709,340),(707,342)])
  (.seq (loadBits 346 k.bits) convertStatistics)

def numericInput (ambient clauses : List Bool) (k free occ arity factors mass : ℕ) : Input :=
  ⟨BinaryArithmetic.toNat ambient,free,BinaryArithmetic.toNat clauses,k,factors,occ,arity,mass⟩

theorem numericStage_eval (a : Data) (ambient clauses : List Bool)
    (k free occ arity factors mass : ℕ)
    (ha : a.stacks 709=ambient) (hm : a.stacks 707=clauses)
    (hz : emptyRange a 340 417) (ht : a.stacks 679=[]) (ht' : a.stacks 647=[])
    (hfree : a.stacks 626=List.replicate free true)
    (hocc : a.stacks 627=List.replicate occ true)
    (harity : a.stacks 642=List.replicate arity true)
    (hfactors : a.stacks 613=List.replicate factors true)
    (hmass : a.stacks 628=List.replicate mass true) :
    ∃ n b l w, Eval (numericStage k) n a b ∧
      projectState r9 bank b=Execute.state (b.regs ∘ r9) w ∧
      Circuit.Shape (Layout.initialModel (numericInput ambient clauses k free occ arity factors mass) l) w ∧
      n ≤ 7*ambient.length+5+7*clauses.length+5+2*k.bits.length+1+
        conversionCost free+conversionCost occ+conversionCost arity+conversionCost factors+conversionCost mass ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 417 ≤ i.val) →
        i≠626 → i≠627 → i≠642 → i≠613 → i≠628 → i≠647 → b.stacks i=a.stacks i) := by
  let cs : List (Fin 768 × Fin 768) := [(709,340),(707,342)]
  let c := copiesState cs a
  have hc := copies_eval cs a (copies_ready_of_clean cs a (by simp [cs]) ht)
  have hcf (i : Fin 768) (h0 : i≠340) (h2 : i≠342) : c.stacks i=a.stacks i := by
    apply copies_frame
    simp [cs,Ne.symm h0,Ne.symm h2]
  have hc340 : c.stacks 340=ambient := by
    simp [c,cs,copiesState,copied_stack,ha,hz 340 (by decide) (by decide)]
  have hc342 : c.stacks 342=clauses := by
    simp [c,cs,copiesState,copied_stack,hm,hz 342 (by decide) (by decide)]
  have hc346 : c.stacks 346=[] := (hcf 346 (by decide) (by decide)).trans (hz 346 (by decide) (by decide))
  obtain ⟨rl,hl⟩ := loadBits_eval c 346 k.bits
  rw [hc346,List.append_nil] at hl
  let d : Data := ⟨rl,Function.update c.stacks 346 k.bits⟩
  have hdf (i : Fin 768) (h0 : i≠340) (h2 : i≠342) (h6 : i≠346) : d.stacks i=a.stacks i := by
    simpa [d,h6] using hcf i h0 h2
  have hd647 : d.stacks 647=[] := (hdf 647 (by decide) (by decide) (by decide)).trans ht'
  have hd626 : d.stacks 626=List.replicate free true := (hdf 626 (by decide) (by decide) (by decide)).trans hfree
  have hd627 : d.stacks 627=List.replicate occ true := (hdf 627 (by decide) (by decide) (by decide)).trans hocc
  have hd642 : d.stacks 642=List.replicate arity true := (hdf 642 (by decide) (by decide) (by decide)).trans harity
  have hd613 : d.stacks 613=List.replicate factors true := (hdf 613 (by decide) (by decide) (by decide)).trans hfactors
  have hd628 : d.stacks 628=List.replicate mass true := (hdf 628 (by decide) (by decide) (by decide)).trans hmass
  have hdz (i : Fin 768) (hi : 340 ≤ i.val ∧ i.val < 417) (h0 : i≠340) (h2 : i≠342) (h6 : i≠346) : d.stacks i=[] :=
    (hdf i h0 h2 h6).trans (hz i hi.1 hi.2)
  obtain ⟨nb,b,hb,hnb,hv1,hl1,hv3,hl3,hv4,hl4,hv5,hl5,hv7,hl7,hb647,hbf⟩ :=
    convertStatistics_eval d free occ arity factors mass hd647
      hd626 (hdz 341 (by decide) (by decide) (by decide) (by decide))
      hd627 (hdz 343 (by decide) (by decide) (by decide) (by decide))
      hd642 (hdz 344 (by decide) (by decide) (by decide) (by decide))
      hd613 (hdz 345 (by decide) (by decide) (by decide) (by decide))
      hd628 (hdz 347 (by decide) (by decide) (by decide) (by decide))
  let w : Bank.Words := fun i => b.stacks (bank (Bank.port i))
  let l : Fin 8 → ℕ := fun i => (w (i.castAdd 56)).length
  have hb0 : b.stacks 340=ambient := by
    rw [hbf 340 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [d] using hc340
  have hb2 : b.stacks 342=clauses := by
    rw [hbf 342 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [d] using hc342
  have hb6 : b.stacks 346=k.bits := by
    rw [hbf 346 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [d]
  have hbz (i : Fin 768) (hi : 348 ≤ i.val ∧ i.val < 417) : b.stacks i=[] := by
    have hi0 : i≠340 := by intro h; subst i; omega
    have hi2 : i≠342 := by intro h; subst i; omega
    have hi6 : i≠346 := by intro h; subst i; omega
    rw [hbf i (by intro h; subst i; omega) (by intro h; subst i; omega)
      (by intro h; subst i; omega) (by intro h; subst i; omega)
      (by intro h; subst i; omega) (by intro h; subst i; omega)
      (by intro h; subst i; omega) (by intro h; subst i; omega)
      (by intro h; subst i; omega) (by intro h; subst i; omega)
      (by intro h; subst i; omega)]
    exact hdz i (by omega) hi0 hi2 hi6
  have hp : projectState r9 bank b=Execute.state (b.regs ∘ r9) w := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases hi : i.val < 64
      · simp [Bank.state,hi,w,Bank.port]
      · have hzi := hbz (bank i) (by dsimp [bank,block]; omega)
        simpa [projectState,Execute.state,Bank.state,hi] using hzi
  have hshape : Circuit.Shape (Layout.initialModel (numericInput ambient clauses k free occ arity factors mass) l) w := by
    constructor
    · intro i
      by_cases hi : i.val < 8
      · obtain ⟨j,rfl⟩ : ∃ j : Fin 8, i=j.castAdd 56 := ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
        fin_cases j <;>
          simp_all [w,bank,block,Bank.port,Layout.initialModel,Layout.initialValues,numericInput,
            ArithmeticExpressionSupport.bits_value]
      · have hzi := hbz (bank (Bank.port i)) (by dsimp [bank,block,Bank.port]; omega)
        simp [w,hzi,Layout.initialModel,Layout.initialValues,numericInput
]
        split <;> omega
    · intro i
      by_cases hi : i.val < 8
      · simp [Layout.initialModel,hi,l]
      · have hzi := hbz (bank (Bank.port i)) (by dsimp [bank,block,Bank.port]; omega)
        simp [Layout.initialModel,hi,w,hzi]
  refine ⟨copiesCost cs a+(2*k.bits.length+1+nb),b,l,w,hc.seq (hl.seq hb),hp,hshape,?_,?_⟩
  · have hcost : copiesCost cs a=7*ambient.length+5+7*clauses.length+5 := by
      simp [copiesCost,cs,copied_stack,ha,hm]
      omega
    rw [hcost]
    omega
  · intro i hi h626 h627 h642 h613 h628 h647
    rw [hbf i h626 (by intro h; subst i; omega) h627 (by intro h; subst i; omega)
      h642 (by intro h; subst i; omega) h613 (by intro h; subst i; omega)
      h628 (by intro h; subst i; omega) h647]
    exact hdf i (by intro h; subst i; omega) (by intro h; subst i; omega) (by intro h; subst i; omega)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
