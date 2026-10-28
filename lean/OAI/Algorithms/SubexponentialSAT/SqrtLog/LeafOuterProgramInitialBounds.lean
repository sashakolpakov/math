import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramReady

namespace OAI.Algorithms

/-! Physical metadata lengths retained across the actual construction.
These are the padded words used by the native cost, not canonical replacements. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem initialCode_eval_with_lengths (a : Data) (W : ℕ) (records : List (List Bool)) (B : ℕ)
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
      (b.stacks 782).length ≤ W+startBudget W records ∧
      (a.stacks 786).length ≤ W+startBudget W records ∧
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
  have hm' : 0 < records.length := List.length_pos_iff.mpr hm
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
  refine ⟨ns+nc,b,p.stacks 768,qword,Dword,s,Q,hep.seq hec,?_,?_,?_,hpW 768,?_,?_,hb,?_,?_,hs,hQ,?_⟩
  · rw [hBword] at hnc
    rw [hmword]
    omega
  · simpa only [hmword,hBword] using hql
  · simpa only [hmword,hBword] using hDl
  · rw [hmword]; exact hpW 782
  · exact (hW 786).trans (Nat.le_add_right _ _)
  · exact (cf 783 (by decide) (by decide) (by decide)).trans hp'.width
  · rw [hrows,LeafScopeResourceBounds.initialPayloads_encoding]
    rfl
  · intro i hi hj
    exact (cf i (by omega) hj (by intro he; have hv:=congrArg Fin.val he; change i.val=777 at hv; omega)).trans (hpf i hi)


end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
