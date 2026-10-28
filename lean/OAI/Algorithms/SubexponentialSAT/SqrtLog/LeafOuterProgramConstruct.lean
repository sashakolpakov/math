import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramParameters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramSerialize

namespace OAI.Algorithms

/-! Unconditional native initial-code construction from m and B. The only
semantic witnesses are the matrices actually found by the two finite searches.
The bound retains the explicit native search and serializer budgets. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem WorkerEmpty.get {a : Data} (h : WorkerEmpty a) (i : Fin 896) (hi : i.val < 768) :
    a.stacks i = [] := h ⟨i.val,hi⟩

theorem Metadata.transport {m B : ℕ} {a b : Data} (h : Metadata m B a)
    (hf : ∀ i : Fin 896, 800 ≤ i.val → i.val ≤ 814 → b.stacks i = a.stacks i) :
    Metadata m B b := by
  constructor
  · rw [hf 800 (by decide) (by decide)]; exact h.q
  · intro j
    rw [hf (binaryMetadataPort j) (by simp [binaryMetadataPort]; omega)
      (by simp [binaryMetadataPort]; omega)]
    exact h.binary j
  · intro j
    rw [hf (unaryMetadataPort j) (by simp [unaryMetadataPort]; omega)
      (by simp [unaryMetadataPort]; omega)]
    exact h.unary j

def parameterBound (m B W : ℕ) (mword Bword : List Bool) : ℕ :=
  10000*(W+CodeParametersProgram.fullBudget m B mword.length Bword.length+2)
def localBound (m B W cp : ℕ) : ℕ :=
  10000*(W+cp+CodeSearchProgram.localProgramBudget (SparseCode.localRows m B)
    (SparseCode.degree m B) (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1)+1)
def graphBound (m B W cp cl : ℕ) (qword Dword : List Bool) : ℕ :=
  10000*(W+cp+cl+CodeSearchProgram.graphProgramBudget (SparseCode.degree m B)
    (SparseCode.dimension m B) qword.length Dword.length+1)
def serializerBound {m B : ℕ} (W cp cl cg : ℕ) (mword Dword width : List Bool)
    (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) : ℕ :=
  10000*(W+cp+cl+cg+CodeRowsProgram.cost Dword mword width s Q+1)
def constructBudget {m B : ℕ} (W : ℕ) (mword Bword qword Dword width : List Bool)
    (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B) : ℕ :=
  let cp := parameterBound m B W mword Bword
  let cl := localBound m B W cp
  let cg := graphBound m B W cp cl qword Dword
  cp+cl+cg+serializerBound W cp cl cg mword Dword width s Q

theorem constructCode_eval (a : Data) (m B W : ℕ) (hm : 0 < m) (hB : 0 < B)
    (hw : WorkerEmpty a) (hW : WordBound W a)
    (hmv : BinaryArithmetic.toNat (a.stacks 782)=m)
    (hBv : BinaryArithmetic.toNat (a.stacks 786)=B)
    (hcap : 3*m ≤ 2^(a.stacks 768).length) :
    ∃ steps b qword Dword, ∃ (s : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B),
      Eval constructCode steps a b ∧
      steps ≤ constructBudget W (a.stacks 782) (a.stacks 786) qword Dword (a.stacks 768) s Q ∧
      qword.length ≤ (a.stacks 782).length+(a.stacks 786).length+11 ∧
      Dword.length ≤ 4*(a.stacks 782).length+2*(a.stacks 786).length+30 ∧
      WalshExistence.Good (SparseCode.gapDenom m B) s ∧
      SparseCode.HasDistance Q (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1) ∧
      b.stacks 777 = CodeRowsProgram.rowStream (a.stacks 768).length m s Q ∧
      WorkerEmpty b ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 777 → (i.val < 800 ∨ 816 < i.val) →
        b.stacks i = a.stacks i) := by
  let cp := parameterBound m B W (a.stacks 782) (a.stacks 786)
  let cl := localBound m B W cp
  obtain ⟨np,hnp,p,hep,hwp,_,hmp,hql,hDl,hpf⟩ := parameters_eval a hm hB hw hmv hBv hW
  have hnp' : np ≤ cp := hnp
  have hpW : WordBound (W+cp) p := SubexpSetupBoundSpec.wordBound_mono
    (SubexpSetupBoundSpec.eval_wordBound hW hep) (by omega)
  have pu0 := hmp.unary 0
  have pu1 := hmp.unary 1
  have pu2 := hmp.unary 2
  have pu3 := hmp.unary 3
  change p.stacks 808 = List.replicate (SparseCode.degree m B) true at pu0
  change p.stacks 809 = List.replicate (SparseCode.localRows m B) true at pu1
  change p.stacks 810 = List.replicate (SparseCode.localRows m B*SparseCode.degree m B) true at pu2
  change p.stacks 811 = List.replicate (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1) true at pu3
  obtain ⟨nl,l,Q,hel,hnl,hQ,hlQ,hwl,hlf⟩ := localCode_eval
    (SparseCode.degree m B) B (SparseCode.logSize m) (SparseCode.localRows m B) (W+cp)
    hB (SparseCode.logSize_pos m) (SparseCode.degree_le_power m B)
    (SparseCode.localRows_lower hB) p hpW (WorkerEmpty.get hwp) pu1 pu3 pu0 pu2
  have hnl' : nl ≤ cl := hnl
  have hlW : WordBound (W+cp+cl) l := SubexpSetupBoundSpec.wordBound_mono
    (SubexpSetupBoundSpec.eval_wordBound hpW hel) (by omega)
  have hlm : Metadata m B l := hmp.transport (by
    intro i hi hj
    apply hlf i (by omega)
    intro h; have hv:=congrArg Fin.val h; change i.val=815 at hv; omega)
  have lu0 := hlm.unary 0
  have lu4 := hlm.unary 4
  have lu5 := hlm.unary 5
  have lb0 := hlm.binary 0
  change l.stacks 808 = List.replicate (SparseCode.degree m B) true at lu0
  change l.stacks 812 = List.replicate (SparseCode.dimension m B) true at lu4
  change l.stacks 813 = List.replicate (SparseCode.dimension m B*SparseCode.degree m B) true at lu5
  change BinaryArithmetic.toNat (l.stacks 801) = SparseCode.degree m B at lb0
  have lu5' : l.stacks 813=List.replicate (SparseCode.degree m B*SparseCode.dimension m B) true := by
    simpa only [Nat.mul_comm] using lu5
  have hsize : SparseCode.dimension m B=0 ∨
      8*SparseCode.gapDenom m B^2*(SparseCode.dimension m B+1) ≤ SparseCode.degree m B := by
    by_cases h : SparseCode.dimension m B=0
    · exact Or.inl h
    · exact Or.inr (SparseCode.walsh_degree_bound hm hB h)
  obtain ⟨ng,g,s,heg,hng,hs,hgs,hwg,hgf⟩ := graphCode_eval
    (SparseCode.degree m B) (SparseCode.dimension m B) (SparseCode.gapDenom m B) (W+cp+cl)
    (SparseCode.gapDenom_pos m hB) hsize l hlW (WorkerEmpty.get hwl) lu0 lu4 lu5' hlm.q lb0
  have hl800 : l.stacks 800=p.stacks 800 := hlf 800 (by decide) (by decide)
  have hl801 : l.stacks 801=p.stacks 801 := hlf 801 (by decide) (by decide)
  let cg := graphBound m B W cp cl (p.stacks 800) (p.stacks 801)
  have hng' : ng ≤ cg := by simpa only [cg,graphBound,hl800,hl801] using hng
  have hgW : WordBound (W+cp+cl+cg) g := SubexpSetupBoundSpec.wordBound_mono
    (SubexpSetupBoundSpec.eval_wordBound hlW heg) (by omega)
  have hgm : Metadata m B g := hlm.transport (by
    intro i hi hj
    apply hgf i (by omega)
    intro h; have hv:=congrArg Fin.val h; change i.val=816 at hv; omega)
  have gf (i : Fin 896) (hi : 768 ≤ i.val) (hlt : i.val < 800) :
      g.stacks i=a.stacks i := by
    rw [hgf i hi (by intro h; have hv:=congrArg Fin.val h; change i.val=816 at hv; omega),
      hlf i hi (by intro h; have hv:=congrArg Fin.val h; change i.val=815 at hv; omega),hpf i hi (Or.inl hlt)]
  have g801 : g.stacks 801=p.stacks 801 := (hgf 801 (by decide) (by decide)).trans hl801
  have gQ : g.stacks 815=CodeSearchProgram.matrixFrames Q :=
    (hgf 815 (by decide) (by decide)).trans hlQ
  have gu0 := hgm.unary 0
  have gu1 := hgm.unary 1
  have gu4 := hgm.unary 4
  have gu6 := hgm.unary 6
  have pb0 := hmp.binary 0
  change g.stacks 808 = List.replicate (SparseCode.degree m B) true at gu0
  change g.stacks 809 = List.replicate (SparseCode.localRows m B) true at gu1
  change g.stacks 812 = List.replicate (SparseCode.dimension m B) true at gu4
  change g.stacks 814 = List.replicate (2^SparseCode.dimension m B) true at gu6
  change BinaryArithmetic.toNat (p.stacks 801) = SparseCode.degree m B at pb0
  obtain ⟨nz,b,hez,hnz,hbrows,hwb,hbf⟩ := serialize_eval g (W+cp+cl+cg) hgW
    (p.stacks 801) (a.stacks 782) (a.stacks 768) s Q (WorkerEmpty.get hwg) g801
    (gf 782 (by decide) (by decide)) (gf 768 (by decide) (by decide))
    gu0 gu1 gu6 hgs gQ gu4 pb0 hmv hcap
  refine ⟨np+(nl+(ng+nz)),b,p.stacks 800,p.stacks 801,s,Q,
    hep.seq (hel.seq (heg.seq hez)),?_,hql,hDl,hs,hQ,hbrows,hwb,?_⟩
  · change np+(nl+(ng+nz)) ≤ cp+cl+cg+serializerBound (W) cp cl cg _ _ _ s Q
    change nz ≤ serializerBound W cp cl cg _ _ _ s Q at hnz
    omega
  · intro i hi h777 hout
    rw [hbf i hi h777,hgf i hi (by intro h; have hv:=congrArg Fin.val h; change i.val=816 at hv; omega),
      hlf i hi (by intro h; have hv:=congrArg Fin.val h; change i.val=815 at hv; omega)]
    exact hpf i hi (by omega)

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
