import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramSearchCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStage

namespace OAI.Algorithms

/-! Both searches are actual finite machines. Their successful matrices are
saved outside the worker before all search storage is physically cleared. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem single_saved {r s : ℕ} (inputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) (source dest : Fin 896) (hd : 768 ≤ dest.val) :
    (stageResult inputs [(source,dest)] register stack a out).stacks dest =
      (stageReturned inputs register stack a out).stacks source := by
  rw [stageResult,clearWorker_frame _ dest hd]
  simp [stageSaved,routesState,routed]

theorem local_prepared (a : Data) (t D d : ℕ)
    (hw : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (ht : a.stacks 809 = List.replicate t true)
    (hd : a.stacks 811 = List.replicate d true)
    (hD : a.stacks 808 = List.replicate D true)
    (he : a.stacks 810 = List.replicate (t*D) true) :
    CodeSearchProgram.LocalProgramReady t D d
      (projectState regs20 stacks32 (routesState localInputs a)) := by
  constructor
  · intro i h19 h20
    let j := stacks32 (CodeSearchProgram.localSearchStacks i)
    have hv : j.val = i.val := rfl
    have hn19 : i.val ≠ 19 := by intro h; exact h19 (Fin.ext h)
    have hn20 : i.val ≠ 20 := by intro h; exact h20 (Fin.ext h)
    have hf : ∀ p ∈ localInputs, p.2 ≠ j := by
      intro p hp
      simp only [localInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl <;> intro h <;>
        have hh := congrArg Fin.val h <;> simp only at hh <;> omega
    exact (routes_frame localInputs a j hf).trans (hw j (by omega))
  · simpa [projectState,localInputs,routesState,routed,stacks32] using ht
  · simpa [projectState,localInputs,routesState,routed,stacks32] using hd
  · simpa [projectState,localInputs,routesState,routed,stacks32] using hD
  · simpa [projectState,localInputs,routesState,routed,stacks32] using he

theorem localCode_eval (D B ell t W : ℕ) (hB : 0 < B) (hell : 0 < ell)
    (hD : D ≤ 2^ell) (ht : D ≤ 8*B*t) (a : Data) (hW : WordBound W a)
    (hw : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hrows : a.stacks 809 = List.replicate t true)
    (hdist : a.stacks 811 = List.replicate (D/(100*B*ell)+1) true)
    (hdim : a.stacks 808 = List.replicate D true)
    (hentries : a.stacks 810 = List.replicate (t*D) true) :
    ∃ steps b, ∃ (Q : Fin t → Fin D → SparseCode.F3),
      Eval localCode steps a b ∧
      steps ≤ 10000*(W+CodeSearchProgram.localProgramBudget t D (D/(100*B*ell)+1)+1) ∧
      SparseCode.HasDistance Q (D/(100*B*ell)+1) ∧
      b.stacks 815 = CodeSearchProgram.matrixFrames Q ∧
      (∀ i : Fin 768, b.stacks (workerStack i) = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 815 → b.stacks i = a.stacks i) := by
  have ha := local_prepared a t D (D/(100*B*ell)+1) hw hrows hdist hdim hentries
  obtain ⟨out,Q,hQ,hout,hrun⟩ := CodeSearchProgram.localProgram_distance D B ell t
    hB hell hD ht _ ha
  obtain ⟨steps,hsteps,he⟩ := stage_bounded_eval localInputs localOutputs
    CodeSearchProgram.localProgram regs20 stacks32 (Fin.castAdd_injective 20 20)
    (Fin.castAdd_injective 32 864) (by intro i h; have hh := congrArg Fin.val h; simp [stacks32] at hh; omega)
    localInputs_valid localOutputs_valid (by decide) (by decide) a W hW (hw 767 (by decide))
    out _ hrun
  refine ⟨steps,stageResult localInputs localOutputs regs20 stacks32 a out,Q,
    he,hsteps,hQ,?_,stageResult_empty _ _ _ _ _ _,?_⟩
  · rw [show localOutputs = [(18,815)] from rfl,single_saved _ _ _ _ _ _ _ (by decide)]
    exact (embedState_stack regs20 stacks32 (routesState localInputs a) out
      (Fin.castAdd_injective 32 864) 18).trans hout
  · intro i hi h815
    apply stageResult_frame _ _ _ _ _ _ i hi
    · intro p hp
      simp only [localInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl <;> intro h <;>
        have hh := congrArg Fin.val h <;> simp only at hh <;> omega
    · intro p hp
      simp only [localOutputs,List.mem_singleton] at hp
      subst p
      exact Ne.symm h815
    · intro j h
      have hh := congrArg Fin.val h
      simp only [stacks32,Fin.val_castAdd] at hh
      omega

theorem graph_prepared (a : Data) (D r q : ℕ) (qword Dword : List Bool)
    (hw : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hD : a.stacks 808 = List.replicate D true)
    (hq : a.stacks 800 = qword) (hDw : a.stacks 801 = Dword)
    (hr : a.stacks 812 = List.replicate r true)
    (he : a.stacks 813 = List.replicate (D*r) true)
    (hqv : BinaryArithmetic.toNat qword = q) (hDv : BinaryArithmetic.toNat Dword = D) :
    CodeSearchProgram.GraphProgramReady D r q qword Dword
      (projectState regs20 stacks44 (routesState graphInputs a)) := by
  constructor
  · intro i h30 h31 h32
    let j := stacks44 (CodeSearchProgram.graphSearchStacks i)
    have hv : j.val = i.val := rfl
    have hn30 : i.val ≠ 30 := by intro h; exact h30 (Fin.ext h)
    have hn31 : i.val ≠ 31 := by intro h; exact h31 (Fin.ext h)
    have hn32 : i.val ≠ 32 := by intro h; exact h32 (Fin.ext h)
    have hf : ∀ p ∈ graphInputs, p.2 ≠ j := by
      intro p hp
      simp only [graphInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> intro h <;>
        have hh := congrArg Fin.val h <;> simp only at hh <;> omega
    exact (routes_frame graphInputs a j hf).trans (hw j (by omega))
  · simpa [projectState,graphInputs,routesState,routed,stacks44] using hD
  · simpa [projectState,graphInputs,routesState,routed,stacks44] using hq
  · simpa [projectState,graphInputs,routesState,routed,stacks44] using hDw
  · simpa [projectState,graphInputs,routesState,routed,stacks44] using hr
  · simpa [projectState,graphInputs,routesState,routed,stacks44] using he
  · exact hqv
  · exact hDv

theorem graphCode_eval (D r q W : ℕ) (hq : 1 ≤ q)
    (hsize : r=0 ∨ 8*q^2*(r+1) ≤ D) (a : Data) (hW : WordBound W a)
    (hw : ∀ i : Fin 896, i.val < 768 → a.stacks i = [])
    (hD : a.stacks 808 = List.replicate D true)
    (hr : a.stacks 812 = List.replicate r true)
    (he : a.stacks 813 = List.replicate (D*r) true)
    (hqv : BinaryArithmetic.toNat (a.stacks 800) = q)
    (hDv : BinaryArithmetic.toNat (a.stacks 801) = D) :
    ∃ steps b, ∃ (s : Fin D → Cayley.Cube r),
      Eval graphCode steps a b ∧
      steps ≤ 10000*(W+CodeSearchProgram.graphProgramBudget D r
        (a.stacks 800).length (a.stacks 801).length+1) ∧
      WalshExistence.Good q s ∧ b.stacks 816 = CodeSearchProgram.matrixFrames s ∧
      (∀ i : Fin 768, b.stacks (workerStack i) = []) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 816 → b.stacks i = a.stacks i) := by
  have ha := graph_prepared a D r q (a.stacks 800) (a.stacks 801) hw hD rfl rfl hr he hqv hDv
  obtain ⟨out,s,hs,hout,hrun⟩ := CodeSearchProgram.graphProgram_runsIn _ ha hq hsize
  obtain ⟨steps,hsteps,heval⟩ := stage_bounded_eval graphInputs graphOutputs
    CodeSearchProgram.graphProgram regs20 stacks44 (Fin.castAdd_injective 20 20)
    (Fin.castAdd_injective 44 852) (by intro i h; have hh := congrArg Fin.val h; simp [stacks44] at hh; omega)
    graphInputs_valid graphOutputs_valid (by decide) (by decide) a W hW (hw 767 (by decide))
    out _ hrun
  refine ⟨steps,stageResult graphInputs graphOutputs regs20 stacks44 a out,s,
    heval,hsteps,hs,?_,stageResult_empty _ _ _ _ _ _,?_⟩
  · rw [show graphOutputs = [(29,816)] from rfl,single_saved _ _ _ _ _ _ _ (by decide)]
    exact (embedState_stack regs20 stacks44 (routesState graphInputs a) out
      (Fin.castAdd_injective 44 852) 29).trans hout
  · intro i hi h816
    apply stageResult_frame _ _ _ _ _ _ i hi
    · intro p hp
      simp only [graphInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> intro h <;>
        have hh := congrArg Fin.val h <;> simp only at hh <;> omega
    · intro p hp
      simp only [graphOutputs,List.mem_singleton] at hp
      subst p
      exact Ne.symm h816
    · intro j h
      have hh := congrArg Fin.val h
      simp only [stacks44,Fin.val_castAdd] at hh
      omega

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
