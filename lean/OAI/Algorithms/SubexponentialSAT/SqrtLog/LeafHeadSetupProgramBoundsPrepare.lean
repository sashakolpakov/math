import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramStorageBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgramSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-! Fixed polynomial cost of actual head-ID, support-mask, and factor-ID
preparation. Bounds include the real isolated-bank copy/cleanup costs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

 theorem wordBound_mono {r s A B : ℕ} {a : State r s} (h : WordBound A a) (hab : A ≤ B) :
    WordBound B a := fun i => (h i).trans hab

 theorem runsIn_wordBound {r s l t A : ℕ} {p : Program r s l}
    {a b : State r s} (h : RunsIn p t (a.withPC (some p.entry)) (b.withPC none))
    (ha : WordBound A a) : WordBound (A+t) b := by
  obtain ⟨u,hu,ht⟩ := h
  intro i
  have hb := SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le ht i
  change (b.stacks i).length ≤ (a.stacks i).length+u at hb
  exact hb.trans (Nat.add_le_add (ha i) hu)

 def preparationSize (n N : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : ℕ :=
  n+N+rows.flatten.length+rows.length+low.length+W+z+2

 theorem selectedHeads_length (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ) :
    (selectedHeads n rows low z).length ≤ n :=
  HeadIdentifierProgram.count_le _ _

 theorem quadratic_ids (n s : ℕ) (hn : n ≤ s) (hs : 1 ≤ s) : n*(2*n+2)+1 ≤ 5*s^2 := by
  have hsq := Nat.mul_self_le_mul_self hn
  nlinarith only [hn,hs,hsq]

 theorem head_local_bound (n : ℕ) (rows : List (List Bool)) (low : List Bool)
    (W z s : ℕ) (hn : n ≤ s) (hr : rows.flatten.length ≤ s) (hl : low.length ≤ s)
    (hW : W ≤ s) (hz : z ≤ s) (hs : 1 ≤ s) :
    WordBound (5*s^2) (HeadIdentifierProgram.FullTable.result n rows low W z) := by
  have hsmall : s ≤ 5*s^2 := by nlinarith only [hs]
  have hi := (HeadIdentifierProgram.encodedIds_length_bound
    (HeadIdentifierProgram.predicate rows low z) n).trans (quadratic_ids n s hn hs)
  have hc := (HeadIdentifierProgram.count_le (HeadIdentifierProgram.predicate rows low z) n).trans hn
  intro i
  by_cases h0 : i=0
  · subst i
    exact hi
  by_cases h1 : i=1
  · subst i
    simpa [HeadIdentifierProgram.FullTable.result,HeadIdentifierProgram.zeros] using hc.trans hsmall
  simp only [HeadIdentifierProgram.FullTable.result,Function.update_of_ne h0,Function.update_of_ne h1]
  simp only [HeadIdentifierProgram.FullTable.baseStacks]
  split_ifs <;> (try simp only [List.length_replicate, List.length_nil]) <;> omega

 theorem factor_local_bound (n N : ℕ) (rows : List (List Bool)) (W z s : ℕ)
    (hn : n ≤ s) (hN : N ≤ s) (hr : rows.flatten.length ≤ s)
    (hW : W ≤ s) (hz : z ≤ s) (hs : 1 ≤ s) :
    WordBound (5*s^2) (LeafHeadFactorsProgram.result rows n N W z) := by
  have hsmall : s ≤ 5*s^2 := by nlinarith only [hs]
  have hi := LeafHeadFactorsProgram.encodedIds_length_bound
    (LeafHeadFactorsProgram.predicate rows n z) N
  have hi' : (SubexponentialSAT.ProgramEncoding.encodeRecords
      ((LeafHeadFactorsProgram.chosenIds (LeafHeadFactorsProgram.predicate rows n z) N).map
        SubexponentialSAT.Encoding.encodeNat)).length ≤ 5*s^2 := by
    apply hi.trans
    simpa only [Nat.mul_comm,Nat.add_comm] using quadratic_ids N s hN hs
  have hc : LeafHeadFactorsProgram.count (LeafHeadFactorsProgram.predicate rows n z) N ≤ N := by
    simpa [LeafHeadFactorsProgram.count,LeafHeadFactorsProgram.chosenIds] using
      List.length_filter_le (LeafHeadFactorsProgram.predicate rows n z) (List.range N)
  intro i
  by_cases h0 : i=0
  · subst i; exact hi'
  by_cases h1 : i=1
  · subst i
    simpa [LeafHeadFactorsProgram.result,LeafHeadFactorsProgram.zeros] using (hc.trans hN).trans hsmall
  simp only [LeafHeadFactorsProgram.result,Function.update_of_ne h0,Function.update_of_ne h1]
  simp only [LeafHeadFactorsProgram.baseStacks]
  split_ifs <;> (try simp only [List.length_replicate, List.length_nil]) <;> omega

 theorem scatter_local_bound (regs : Fin 8 → Bool) (n : ℕ) (rows : List (List Bool))
    (low : List Bool) (z s : ℕ) (hn : n ≤ s) (hs : 1 ≤ s) :
    WordBound (5*s^2) (HeadScatterProgram.result regs (selectedHeads n rows low z)
      (List.replicate (selectedHeads n rows low z).length true) n) := by
  have hsmall : s ≤ 5*s^2 := by nlinarith only [hs]
  have hi := (HeadIdentifierProgram.encodedIds_length_bound
    (HeadIdentifierProgram.predicate rows low z) n).trans (quadratic_ids n s hn hs)
  have hc := (selectedHeads_length n rows low z).trans hn
  have hm := HeadScatterProgram.mask_length n (selectedHeads n rows low z)
    (List.replicate (selectedHeads n rows low z).length true)
    (HeadIdentifierProgram.chosenIds_bound _ _)
  intro i
  fin_cases i <;> simp only [HeadScatterProgram.result,Matrix.cons_val_succ',Matrix.cons_val_zero',
    List.length_nil,List.length_replicate,HeadScatterProgram.unary] <;>
    first | exact hi | omega

 theorem prepareHead_bound (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z A : ℕ)
    (ha : WordBound A a) (hsize : n ≤ rows.length) :
    let s := preparationSize n N rows low W z
    WordBound (A+5*s^2) (preparedHead a regs n N rows low W z) ∧
    prepareHeadCost a regs n N rows low W z ≤ 100000*(A+s^3+1) := by
  let s := preparationSize n N rows low W z
  let B := A+5*s^2
  have hs : 1 ≤ s := by dsimp [s,preparationSize]; omega
  have hn : n ≤ s := by dsimp [s,preparationSize]; omega
  have hN : N ≤ s := by dsimp [s,preparationSize]; omega
  have hr : rows.flatten.length ≤ s := by dsimp [s,preparationSize]; omega
  have hl : low.length ≤ s := by dsimp [s,preparationSize]; omega
  have hW : W ≤ s := by dsimp [s,preparationSize]; omega
  have hz : z ≤ s := by dsimp [s,preparationSize]; omega
  have hsmall : s ≤ 5*s^2 := by nlinarith only [hs]
  have ha' : WordBound B a := wordBound_mono ha (by dsimp [B]; omega)
  have hh : WordBound B (HeadIdentifierProgram.FullTable.result n rows low W z) :=
    wordBound_mono (head_local_bound n rows low W z s hn hr hl hW hz hs) (by dsimp [B]; omega)
  have hhead : WordBound B (headResult a n rows low W z) :=
    returned_wordBound id (by decide) headInputs headOutputs a _ B
      headInputs_protected headOutputs_protected (by decide) (by decide) ha' hh
  let b := headResult a n rows low W z
  have hbl : (b.stacks 651).length ≤ s := by
    rw [headResult_count]
    simpa [zeros] using (HeadIdentifierProgram.count_le _ n).trans hn
  have hcountLocal : WordBound B (PackingHeadProgramPrepareCount.state (fun _=>false) []
      (List.replicate (b.stacks 651).length true)) := by
    intro i; fin_cases i <;> simp [PackingHeadProgramPrepareCount.state] ;
      exact hbl.trans (hsmall.trans (by dsimp [B]; omega))
  have hcount : WordBound B (countResult b) :=
    returned_wordBound countRegs (by decide) countInputs countOutputs b _ B
      countInputs_protected countOutputs_protected (by decide) (by decide) hhead hcountLocal
  let c := countResult b
  let js := selectedHeads n rows low z
  have hscatterLocal : WordBound B (HeadScatterProgram.result regs js (List.replicate js.length true) n) :=
    wordBound_mono (scatter_local_bound regs n rows low z s hn hs) (by dsimp [B]; omega)
  have hscatter : WordBound B (scatterResult c regs n js) :=
    returned_wordBound scatterRegs (by decide) scatterInputs scatterOutputs c _ B
      scatterInputs_protected scatterOutputs_protected (by decide) (by decide) hcount hscatterLocal
  let d := scatterResult c regs n js
  have hf : WordBound B (LeafHeadFactorsProgram.result rows n N W z) :=
    wordBound_mono (factor_local_bound n N rows W z s hn hN hr hW hz hs) (by dsimp [B]; omega)
  have hfactor : WordBound B (factorResult d n N rows W z) :=
    returned_wordBound id (by decide) factorInputs factorOutputs d _ B
      factorInputs_protected factorOutputs_protected (by decide) (by decide) hscatter hf
  refine ⟨hfactor,?_⟩
  have ch := stageCost_linear id (by decide) headInputs headOutputs a _
    (HeadIdentifierProgram.FullTable.budget n rows.length W low.length z) B
    headInputs_protected headOutputs_protected (by decide) (by decide) ha' hh
  have cc := stageCost_linear countRegs (by decide) countInputs countOutputs b _
    (4*(b.stacks 651).length+4) B countInputs_protected countOutputs_protected
    (by decide) (by decide) hhead hcountLocal
  have cs := stageCost_linear scatterRegs (by decide) scatterInputs scatterOutputs c _
    (100*(n+1)*(js.length+1)) B scatterInputs_protected scatterOutputs_protected
    (by decide) (by decide) hcount hscatterLocal
  have cf := stageCost_linear id (by decide) factorInputs factorOutputs d _
    (LeafHeadFactorsProgram.budget n N rows.length W z) B
    factorInputs_protected factorOutputs_protected (by decide) (by decide) hscatter hf
  have hch : HeadIdentifierProgram.FullTable.budget n rows.length W low.length z ≤ 300*s^3 :=
    (HeadIdentifierProgram.FullTable.budget_polynomial n rows.length W low.length z hsize).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [s,preparationSize]; omega) 3))
  have hcf : LeafHeadFactorsProgram.budget n N rows.length W z ≤ 1000*s^3 :=
    (LeafHeadFactorsProgram.budget_polynomial n N rows.length W z).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [s,preparationSize]; omega) 3))
  have hjs : js.length ≤ s := (selectedHeads_length n rows low z).trans hn
  have hcs : 100*(n+1)*(js.length+1) ≤ 400*s^2 := by
    calc
      _ ≤ 100*(s+1)*(s+1) := by gcongr
      _ ≤ 400*s^2 := by nlinarith only [hs]
  have h23 : s^2 ≤ s^3 := pow_le_pow_right₀ hs (by decide)
  change headCost a n rows low W z+countCost b+scatterCost c regs n js+factorCost d n N rows W z ≤ _
  change headCost a n rows low W z ≤ _ at ch
  change countCost b ≤ _ at cc
  change scatterCost c regs n js ≤ _ at cs
  change factorCost d n N rows W z ≤ _ at cf
  norm_num [headInputs,headOutputs,countInputs,countOutputs,scatterInputs,scatterOutputs,
    factorInputs,factorOutputs] at ch cc cs cf
  dsimp [B] at ch cc cs cf
  nlinarith only [ch,cc,cs,cf,hch,hcf,hcs,hbl,hsmall,h23]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
