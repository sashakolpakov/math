import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramSearch

namespace OAI.Algorithms

/-! Physical serialization of the two matrices found by the native searches.
The supplied matrix values occur only in the correctness assertion; the
program reads their saved bit encodings from the actual output tapes. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem serializer_prepared {r D t : ℕ} (a : Data) (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (hw : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hd : a.stacks 801 = dword) (hm : a.stacks 782 = mword) (hb : a.stacks 768 = width)
    (hD : a.stacks 808 = List.replicate D true)
    (ht : a.stacks 809 = List.replicate t true)
    (hN : a.stacks 814 = List.replicate (2^r) true)
    (hs : a.stacks 816 = CodeSearchProgram.matrixFrames shifts)
    (hQ : a.stacks 815 = CodeSearchProgram.matrixFrames Q)
    (hr : a.stacks 812 = List.replicate r true) :
    projectState regs16 stacks64 (routesState rowInputs a) =
      CodeRowsProgram.inputState ((routesState rowInputs a).regs ∘ regs16)
        dword mword width shifts Q := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    have hz : a.stacks (stacks64 i) = [] := hw _ (by simp only [stacks64,Fin.val_castAdd]; omega)
    by_cases h3 : i=3
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h4 : i=4
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h5 : i=5
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h6 : i=6
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h7 : i=7
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h8 : i=8
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h9 : i=9
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h10 : i=10
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    by_cases h11 : i=11
    · subst i; simp [rowInputs,routesState,routed,stacks64,hd,hm,hb,hD,ht,hN,hs,hQ,hr]
    have v3 : i.val≠3 := fun h => h3 (Fin.ext h)
    have v4 : i.val≠4 := fun h => h4 (Fin.ext h)
    have v5 : i.val≠5 := fun h => h5 (Fin.ext h)
    have v6 : i.val≠6 := fun h => h6 (Fin.ext h)
    have v7 : i.val≠7 := fun h => h7 (Fin.ext h)
    have v8 : i.val≠8 := fun h => h8 (Fin.ext h)
    have v9 : i.val≠9 := fun h => h9 (Fin.ext h)
    have v10 : i.val≠10 := fun h => h10 (Fin.ext h)
    have v11 : i.val≠11 := fun h => h11 (Fin.ext h)
    have hf : ∀ p ∈ rowInputs, p.2≠stacks64 i := by
      intro p hp
      simp only [rowInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> intro h <;>
        have hv := congrArg Fin.val h <;> simp only [stacks64,Fin.val_castAdd] at hv <;> omega
    change (routesState rowInputs a).stacks (stacks64 i)=_
    rw [routes_frame rowInputs a (stacks64 i) hf,hz]
    simp only [ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,
      ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_right h11]

theorem serialize_eval {r D t m : ℕ} (a : Data) (W : ℕ) (hW : WordBound W a)
    (dword mword width : List Bool) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3)
    (hw : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hd : a.stacks 801 = dword) (hm : a.stacks 782 = mword) (hb : a.stacks 768 = width)
    (hD : a.stacks 808 = List.replicate D true)
    (ht : a.stacks 809 = List.replicate t true)
    (hN : a.stacks 814 = List.replicate (2^r) true)
    (hs : a.stacks 816 = CodeSearchProgram.matrixFrames shifts)
    (hQ : a.stacks 815 = CodeSearchProgram.matrixFrames Q)
    (hr : a.stacks 812 = List.replicate r true)
    (hdv : BinaryArithmetic.toNat dword = D) (hmv : BinaryArithmetic.toNat mword = m)
    (hcap : 3*m ≤ 2^width.length) :
    ∃ steps b, Eval serialize steps a b ∧
      steps ≤ 10000*(W+CodeRowsProgram.cost dword mword width shifts Q+1) ∧
      b.stacks 777 = CodeRowsProgram.rowStream width.length m shifts Q ∧
      (∀ i : Fin 768, b.stacks (workerStack i) = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 777 → b.stacks i = a.stacks i) := by
  have hp := serializer_prepared a dword mword width shifts Q hw hd hm hb hD ht hN hs hQ hr
  obtain ⟨rf,hrun⟩ := CodeRowsProgram.program_runsIn
    ((routesState rowInputs a).regs ∘ regs16) dword mword width shifts Q hdv hmv hcap
  rw [← hp] at hrun
  obtain ⟨steps,hsteps,he⟩ := stage_bounded_eval rowInputs rowOutputs
    CodeRowsProgram.program regs16 stacks64 (Fin.castAdd_injective 16 24)
    (Fin.castAdd_injective 64 832)
    (by intro i h; have hh := congrArg Fin.val h; simp [stacks64] at hh; omega)
    rowInputs_valid rowOutputs_valid (by decide) (by decide) a W hW (hw 767 (by decide))
    _ _ hrun
  let out := CodeRowsProgram.outputState (m:=m) rf dword mword width shifts Q
  refine ⟨steps,stageResult rowInputs rowOutputs regs16 stacks64 a out,he,hsteps,?_,
    stageResult_empty _ _ _ _ _ _,?_⟩
  · rw [show rowOutputs = [(12,777)] from rfl,single_saved _ _ _ _ _ _ _ (by decide)]
    have hh := embedState_stack regs16 stacks64 (routesState rowInputs a) out
      (Fin.castAdd_injective 64 832) 12
    change ((embedState regs16 stacks64 (routesState rowInputs a) out).stacks 12) =
      CodeRowsProgram.rowStream width.length m shifts Q
    simpa only [show stacks64 12 = (12 : Fin 896) from rfl, out,
      CodeRowsProgram.outputState, Function.update_self] using hh
  · intro i hi h777
    apply stageResult_frame _ _ _ _ _ _ i hi
    · intro p hp
      simp only [rowInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> intro h <;>
        have hh := congrArg Fin.val h <;> simp only at hh <;> omega
    · intro p hp
      simp only [rowOutputs,List.mem_singleton] at hp
      subst p
      exact Ne.symm h777
    · intro j h
      have hh := congrArg Fin.val h
      simp only [stacks64,Fin.val_castAdd] at hh
      omega

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
