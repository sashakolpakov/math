import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStart
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramConstruct
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramInitial

namespace OAI.Algorithms

/-! The complete native startup and sparse-code construction boundary. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem StartReady.transport {a b : Data} {n m B : ℕ} (h : StartReady a n m B)
    (hw : WorkerEmpty b)
    (hf : ∀ i : Fin 896, 768 ≤ i.val → i.val < 800 → i≠777 → b.stacks i=a.stacks i) :
    StartReady b n m B := by
  constructor
  · exact hw
  · intro j h0 h5 h6 h9
    have hv : (LeafProgram.HashParameters.ports.hash.stack j).val=768+j.val := by
      fin_cases j <;> rfl
    have hj : LeafProgram.HashParameters.ports.hash.stack j≠777 := by
      intro he
      have hh:=congrArg Fin.val he
      have : j.val=9 := by omega
      exact h9 (Fin.ext this)
    change b.stacks (LeafProgram.HashParameters.ports.hash.stack j)=[]
    rw [hf _ (by omega) (by have:=j.isLt; omega) hj]
    exact h.hash j h0 h5 h6 h9
  · rw [hf 785 (by decide) (by decide) (by decide)]; exact h.ambient
  · rw [hf 782 (by decide) (by decide) (by decide)]; exact h.clauses
  · rw [hf 786 (by decide) (by decide) (by decide)]; exact h.occurrence
  · rw [hf 768 (by decide) (by decide) (by decide)]; exact h.count
  · rw [hf 773 (by decide) (by decide) (by decide)]; exact h.depth
  · rw [hf 774 (by decide) (by decide) (by decide)]; exact h.rounds
  · rw [hf 783 (by decide) (by decide) (by decide),hf 768 (by decide) (by decide) (by decide)]
    exact h.width

abbrev initialCode : Cmd 40 896 := .seq start constructCode

theorem initialCode_eval (a : Data) (W : ℕ) (records : List (List Bool)) (B : ℕ)
    (hW : WordBound W a) (hempty : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i=[])
    (hformula : a.stacks 784=Encoding.encodeList id records) (hm : records≠[])
    (hB : 0 < B) (hBv : BinaryArithmetic.toNat (a.stacks 786)=B) :
    ∃ steps b, ∃ (countWord qword Dword : List Bool)
      (s : SparseCode.SuppliedShifts records.length B) (Q : SparseCode.SuppliedLocal records.length B),
      Eval initialCode steps a b ∧
      steps ≤ startBudget W records + constructBudget (W+startBudget W records)
        (b.stacks 782) (a.stacks 786) qword Dword countWord s Q ∧
      qword.length ≤ (b.stacks 782).length+(a.stacks 786).length+11 ∧
      Dword.length ≤ 4*(b.stacks 782).length+2*(a.stacks 786).length+30 ∧
      countWord.length ≤ W+startBudget W records ∧
      StartReady b (BinaryArithmetic.toNat (a.stacks 785)) records.length B ∧
      b.stacks 783=countWord ∧
      b.stacks 777=HashSelectProgram.candidateEncoding
        (LeafScopeResourceBounds.initialPayloads countWord.length (CodeRowsProgram.serializedRows records.length s Q)) ∧
      WalshExistence.Good (SparseCode.gapDenom records.length B) s ∧
      SparseCode.HasDistance Q (SparseCode.degree records.length B/(100*B*SparseCode.logSize records.length)+1) ∧
      (∀ i : Fin 896, 784 ≤ i.val → i.val < 800 → b.stacks i=a.stacks i) := by
  obtain ⟨ns,hns,p,hep,hp,hpf⟩ := start_eval a W records hW hempty hformula hm
  have hp' : StartReady p (BinaryArithmetic.toNat (a.stacks 785)) records.length B := by
    simpa only [hBv] using hp
  have hpW : WordBound (W+startBudget W records) p :=
    SubexpSetupBoundSpec.wordBound_mono (SubexpSetupBoundSpec.eval_wordBound hW hep) (by omega)
  have hm' : 0 < records.length := by
    cases records with
    | nil => simp at hm
    | cons => simp
  have hcapacity : 3*records.length ≤ 2^(p.stacks 768).length :=
    (HashFamilyPayload.countWord_width_sufficient (p.stacks 768)
      (by simpa only [CounterPrograms.value_eq_toNat] using hp'.count)).le
  obtain ⟨nc,b,qword,Dword,s,Q,hec,hnc,hql,hDl,hs,hQ,hrows,hw,hcf⟩ :=
    constructCode_eval p records.length B (W+startBudget W records)
      hm' hB hp'.worker hpW hp'.clauses hp'.occurrence hcapacity
  have cf (i : Fin 896) (hi : 768 ≤ i.val) (hj : i.val < 800) (hn : i≠777) :
      b.stacks i=p.stacks i := hcf i hi hn (Or.inl hj)
  have hb := hp'.transport hw cf
  have hBword : p.stacks 786=a.stacks 786 := hpf 786 (by decide)
  have hmword : b.stacks 782=p.stacks 782 := cf 782 (by decide) (by decide) (by decide)
  refine ⟨ns+nc,b,p.stacks 768,qword,Dword,s,Q,hep.seq hec,?_,?_,?_,hpW 768,hb,?_,?_,hs,hQ,?_⟩
  · rw [hBword] at hnc
    rw [hmword]
    omega
  · simpa only [hmword,hBword] using hql
  · simpa only [hmword,hBword] using hDl
  · exact (cf 783 (by decide) (by decide) (by decide)).trans hp'.width
  · rw [hrows,LeafScopeResourceBounds.initialPayloads_encoding]
    rfl
  · intro i hi hj
    exact (cf i (by omega) hj (by intro he; have hv:=congrArg Fin.val he; change i.val=777 at hv; omega)).trans (hpf i hi)

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
