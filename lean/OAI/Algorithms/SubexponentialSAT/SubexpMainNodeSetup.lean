import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodePreclear
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeHeader
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeReduction
import OAI.Algorithms.SubexponentialSAT.SubexpMainNodeInitialization
import OAI.Algorithms.SubexponentialSAT.SubexpProcedureCompose

namespace OAI.Algorithms

/-! The actual row-to-node handoff. Old evaluator work is cleared while
source caches and row/node masters survive. The target header and reduction
are copied physically, then the closed node initializer constructs its
dimension, index, exponent, raw-literal, lookup, and slot data. -/

namespace SubexponentialSAT.SubexpMainNodeSetup

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation master ordinary)

attribute [local simp] Fin.coe_ofNat_eq_mod

noncomputable def cleared {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :=
  SubexpMainNodePreclear.result alloc a

noncomputable def headed {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :=
  SubexpMainNodeHeader.installed alloc (cleared alloc a)

noncomputable def prepared {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :=
  SubexpMainNodeReduction.installed alloc (headed alloc a)

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es :=
  SubexpProcedureCompose.sequence (SubexpMainNodePreclear.procedure er alloc)
    (SubexpProcedureCompose.sequence (SubexpMainNodeHeader.procedure er alloc)
      (SubexpProcedureCompose.sequence (SubexpMainNodeReduction.procedure er alloc)
        (SubexpMainNodeInitialization.procedure er alloc)))

theorem prepared_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (j : Fin (totalStacks es))
    (h91 : j ≠ ordinary alloc 91) (h319 : j ≠ ordinary alloc 319)
    (hh : ∀ i, SubexpMainNodeHeader.targetPort alloc i ≠ j) :
    (prepared alloc a).stacks j = (cleared alloc a).stacks j := by
  rw [prepared, SubexpMainNodeReduction.installed_frame alloc _ j h91 h319,
    headed, SubexpMainNodeHeader.installed_frame alloc _ j hh (Ne.symm h319)]

theorem prepared_empty {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 352) (hi : SubexpMainNodeInitialization.NeedsEmpty i) :
    (SubexpMainNodeInitialization.projected alloc (prepared alloc a)).stacks i = [] := by
  have hn := hi
  simp only [SubexpMainNodeInitialization.NeedsEmpty, Fin.ext_iff,
    Fin.coe_ofNat_eq_mod] at hn
  let j : Fin 672 := ⟨if i.val = 337 then 305 else i.val, by split_ifs <;> omega⟩
  have hj : SubexpMainNodePreclear.Selected j.val := by
    dsimp [j, SubexpMainNodePreclear.Selected]
    split_ifs <;> omega
  have h91 : ordinary alloc j ≠ ordinary alloc 91 := by
    intro he
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
    change j.val = 91 at hv
    dsimp [j] at hv
    split_ifs at hv <;> omega
  have h319 : ordinary alloc j ≠ ordinary alloc 319 := by
    intro he
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
    change j.val = 319 at hv
    dsimp [j] at hv
    split_ifs at hv <;> omega
  have hh (k : Fin 4) : SubexpMainNodeHeader.targetPort alloc k ≠ ordinary alloc j := by
    intro he
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
    fin_cases k <;> norm_num [SubexpMainNodeHeader.targetPort, ordinary, j] at hv
    all_goals split_ifs at hv <;> omega
  have hm : SubexpMainMomentPorts.stackMap alloc i = ordinary alloc j := by
    by_cases h337 : i.val = 337
    · have he : i = 337 := Fin.ext h337
      subst i
      rfl
    · have hlo : i.val < 256 := by omega
      have h5 : i ≠ 5 := by intro he; have hv := congrArg (fun q : Fin 352 => q.val) he; norm_num at hv; omega
      have h10 : i ≠ 10 := by intro he; have hv := congrArg (fun q : Fin 352 => q.val) he; norm_num at hv; omega
      simp only [SubexpMainMomentPorts.stackMap, ite_eq_right h5, ite_eq_right h10,
        SubexpMainMomentPorts.baseMap, dite_eq_left hlo, j, ite_eq_right h337]
  change (prepared alloc a).stacks (SubexpMainMomentPorts.stackMap alloc i) = []
  rw [hm, prepared_frame alloc a _ h91 h319 hh]
  exact SubexpMainNodePreclear.result_cleared alloc a _ hj

theorem prepared_persistent {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 32) :
    (prepared alloc a).stacks (persistent es i) = a.stacks (persistent es i) := by
  rw [prepared, SubexpMainNodeReduction.installed_persistent]
  have hb := alloc.enough.trans alloc.within
  rw [headed, SubexpMainNodeHeader.installed_frame alloc _ _]
  · exact SubexpMainNodePreclear.result_persistent alloc a i
  · intro j he
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
    fin_cases j <;> norm_num [SubexpMainNodeHeader.targetPort, ordinary, persistent] at hv <;> omega
  · intro he
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
    simp only [ordinary, persistent, Fin.val_natAdd] at hv
    omega

theorem prepared_master {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 32) : (prepared alloc a).stacks (master alloc i) = a.stacks (master alloc i) := by
  rw [prepared_frame alloc a (master alloc i)]
  · exact SubexpMainNodePreclear.result_master alloc a i
  · intro he
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
    simp only [SubexpLayoutPorts.master_val, ordinary] at hv
    omega
  · intro he
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
    simp only [SubexpLayoutPorts.master_val, ordinary] at hv
    omega
  · intro j he
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
    fin_cases j <;> norm_num [SubexpMainNodeHeader.targetPort, ordinary,
      SubexpLayoutPorts.master] at hv <;> omega

theorem prepared_header {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 4) :
    (prepared alloc a).stacks (SubexpMainNodeHeader.targetPort alloc i) =
      a.stacks (SubexpMainNodeHeader.sourcePort alloc i) := by
  rw [prepared, SubexpMainNodeReduction.installed_frame alloc _ _,
    headed, SubexpMainNodeHeader.installed_target]
  · fin_cases i
    · exact SubexpMainNodePreclear.result_persistent alloc a 28
    · exact SubexpMainNodePreclear.result_persistent alloc a 30
    · exact SubexpMainNodePreclear.result_persistent alloc a 31
    · exact SubexpMainNodePreclear.result_counter alloc a
  all_goals
    intro he
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
    fin_cases i <;> norm_num [SubexpMainNodeHeader.targetPort, ordinary] at hv

noncomputable def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (D : ℕ) : ℕ :=
  SubexpMainNodePreclear.runtimeBound alloc a +
    SubexpMainNodeHeader.runtimeBound alloc (cleared alloc a) +
    SubexpMainNodeReduction.runtimeBound alloc (headed alloc a) +
    SubexpMainNodeInitialization.runtimeBound alloc (prepared alloc a) D + 3

/-- Every node-initializer scratch premise follows from the actual clear
and copy prefix. The only input hypotheses are the retained width and D. -/
theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (D : ℕ)
    (hwidth : 0 < (a.stacks (persistent es 13)).length)
    (hD : a.stacks (master alloc 8) = List.replicate D true) :
    ∃ n ≤ runtimeBound alloc a D, ∃ b,
      Eval (procedure er alloc).invoke n a b ∧
      SubexpMainNodeInitialization.Result alloc (prepared alloc a) b D := by
  have hp := SubexpMainNodePreclear.execution alloc a
  obtain ⟨nh, hnh, hh⟩ := SubexpMainNodeHeader.execution alloc (cleared alloc a)
  have hr := SubexpMainNodeReduction.execution_exact alloc (headed alloc a)
  obtain ⟨ni, hni, b, hi, hb⟩ := SubexpMainNodeInitialization.execution alloc (prepared alloc a) D
    (prepared_empty alloc a) (by rw [prepared_persistent]; exact hwidth)
    ((prepared_master alloc a 8).trans hD)
  refine ⟨SubexpMainNodePreclear.runtimeBound alloc a +
    (nh + (SubexpMainNodeReduction.runtimeBound alloc (headed alloc a) + ni + 1) + 1) + 1,
    ?_, b, ?_, hb⟩
  · unfold runtimeBound
    omega
  · exact SubexpProcedureCompose.sequence_invoke _ _ hp
      (SubexpProcedureCompose.sequence_invoke _ _ hh
        (SubexpProcedureCompose.sequence_invoke _ _ hr hi))

end SubexponentialSAT.SubexpMainNodeSetup

end OAI.Algorithms
