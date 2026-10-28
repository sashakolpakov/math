import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBasisStage

namespace OAI.Algorithms

/-! Exact state and cost of the eleven physical basis-input copies and their cleanup. -/

namespace SubexponentialSAT.SubexpNodeBasisExecution

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpNodeBasisStage

def WorkEmpty (d : Data) : Prop := ∀ i : Fin 64, d.stacks (ports i) = []

def suppliedPorts : List (Fin 64) := [32,33,37,38,46,47,48,49,13,14,15]

theorem workspace_eq : workspace = suppliedPorts.map ports := rfl

theorem moves_target_bounds (m : Move) (hm : m ∈ moves) :
    138 ≤ m.2.val ∧ m.2.val < 188 := by
  simp only [moves, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem moves_source_bounds (m : Move) (hm : m ∈ moves) :
    m.1.val = 116 ∨ 256 ≤ m.1.val := by
  simp only [moves, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem moves_cross (a : Move) (ha : a ∈ moves) (b : Move) (hb : b ∈ moves) :
    a.1 ≠ b.2 := by
  have hs := moves_source_bounds a ha
  have ht := moves_target_bounds b hb
  intro he
  have hv := congrArg Fin.val he
  omega

theorem workspace_nodup : workspace.Nodup := by decide

theorem output_not_workspace : (201 : Fin 288) ∉ workspace := by decide

theorem work_target {d : Data} (h : WorkEmpty d) (m : Move) (hm : m ∈ moves) :
    d.stacks m.2 = [] := by
  have hb := moves_target_bounds m hm
  let i : Fin 64 := ⟨m.2.val - 138, by omega⟩
  have he : ports i = m.2 := by
    apply Fin.ext
    change 138 + (m.2.val - 138) = m.2.val
    omega
  simpa only [he] using h i

private theorem copied_target (ms : List Move) (d : Data)
    (hn : (ms.map Prod.snd).Nodup)
    (hc : ∀ a ∈ ms, ∀ b ∈ ms, a.1 ≠ b.2)
    (m : Move) (hm : m ∈ ms) :
    (copied ms d).stacks m.2 = d.stacks m.1 ++ d.stacks m.2 := by
  induction ms generalizing d with
  | nil => simp at hm
  | cons a ms ih =>
    have hnd := List.nodup_cons.mp hn
    have hcross : ∀ x ∈ ms, ∀ y ∈ ms, x.1 ≠ y.2 := by
      intro x hx y hy
      exact hc x (by simp [hx]) y (by simp [hy])
    rcases List.mem_cons.mp hm with he | hm
    · subst m
      rw [copied, copied_frame]
      · simp only [afterCopy, StackRoutines.copyStacks, Function.update_same]
      · intro b hb he
        exact hnd.1 (List.mem_map.mpr ⟨b, hb, he.symm⟩)
    · rw [copied, ih _ hnd.2 hcross hm]
      have hsrc := hc m (by simp [hm]) a (by simp)
      have hdst : m.2 ≠ a.2 := by
        intro he
        exact hnd.1 (List.mem_map.mpr ⟨m, hm, he⟩)
      simp only [afterCopy, StackRoutines.copyStacks,
        Function.update_of_ne hsrc, Function.update_of_ne hdst]

theorem copied_source {d : Data} (h : WorkEmpty d) (m : Move) (hm : m ∈ moves) :
    (copied moves d).stacks m.2 = d.stacks m.1 := by
  rw [copied_target moves d workspace_nodup moves_cross m hm, work_target h m hm,
    List.append_nil]

theorem copied_native_frame (d : Data) (i : Fin 64) (hi : i ∉ suppliedPorts) :
    (copied moves d).stacks (ports i) = d.stacks (ports i) := by
  apply copied_frame
  intro m hm he
  have hmem : m.2 ∈ workspace := List.mem_map.mpr ⟨m, hm, rfl⟩
  rw [workspace_eq] at hmem
  obtain ⟨j, hj, hjm⟩ := List.mem_map.mp hmem
  have hij : i = j := ports_injective (he.trans hjm.symm)
  exact hi (hij.symm ▸ hj)

private theorem copyCost_sum (ms : List Move) (d : Data)
    (hc : ∀ a ∈ ms, ∀ b ∈ ms, a.1 ≠ b.2) :
    copyCost ms d = (ms.map (fun m => 7 * (d.stacks m.1).length + 5)).sum := by
  induction ms generalizing d with
  | nil => rfl
  | cons a ms ih =>
    have hcross : ∀ x ∈ ms, ∀ y ∈ ms, x.1 ≠ y.2 := by
      intro x hx y hy
      exact hc x (by simp [hx]) y (by simp [hy])
    rw [copyCost, ih _ hcross]
    have hm : ms.map (fun m => 7 * ((afterCopy d a.1 a.2 0 1).stacks m.1).length + 5) =
        ms.map (fun m => 7 * (d.stacks m.1).length + 5) := by
      apply List.map_congr_left
      intro m hm
      have he := hc m (by simp [hm]) a (by simp)
      simp only [afterCopy, StackRoutines.copyStacks, Function.update_of_ne he]
    rw [hm]
    rfl

theorem cleared_stack (xs : List (Fin 288)) (d : Data) (i : Fin 288) :
    (cleared xs d).stacks i = if i ∈ xs then [] else d.stacks i := by
  induction xs generalizing d with
  | nil => simp [cleared]
  | cons j xs ih =>
    rw [cleared, ih]
    by_cases hi : i ∈ xs
    · simp [hi]
    · by_cases he : i = j
      · simp [he, clearOut]
      · simp [hi, he, clearOut]

private theorem clearCost_sum (xs : List (Fin 288)) (d : Data) (hn : xs.Nodup) :
    clearCost xs d = (xs.map (fun i => 2 * (d.stacks i).length + 3)).sum := by
  induction xs generalizing d with
  | nil => rfl
  | cons i xs ih =>
    have hnd := List.nodup_cons.mp hn
    rw [clearCost, ih _ hnd.2]
    have hm : xs.map (fun j => 2 * ((clearOut d i).stacks j).length + 3) =
        xs.map (fun j => 2 * (d.stacks j).length + 3) := by
      apply List.map_congr_left
      intro j hj
      have he : j ≠ i := by intro he; subst j; exact hnd.1 hj
      simp only [clearOut, Function.update_of_ne he]
    rw [hm]
    rfl

def inputVolume (d : Data) : ℕ := (moves.map (fun m => (d.stacks m.1).length)).sum

theorem copyCost_eq (d : Data) : copyCost moves d = 7 * inputVolume d + 55 := by
  rw [copyCost_sum moves d moves_cross]
  simp only [inputVolume, moves, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.mul_add]
  omega

theorem cleanupCost_eq {d e : Data} (h : WorkEmpty d) (bits : List Bool)
    (hs : e.stacks = Function.update (copied moves d).stacks 201 bits) :
    clearCost workspace e = 2 * inputVolume d + 33 := by
  rw [clearCost_sum workspace e workspace_nodup]
  have hm : workspace.map (fun i => 2 * (e.stacks i).length + 3) =
      moves.map (fun m => 2 * (d.stacks m.1).length + 3) := by
    unfold workspace
    rw [List.map_map]
    apply List.map_congr_left
    intro m hm
    have hb := moves_target_bounds m hm
    have he : m.2 ≠ (201 : Fin 288) := by intro he; have := congrArg Fin.val he; norm_num at this; omega
    simp only [Function.comp_apply, hs, Function.update_of_ne he, copied_source h m hm]
  rw [hm]
  simp only [inputVolume, moves, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.mul_add]
  omega

theorem embedded_stacks {d : Data} {out : Subexp.GlobalBasisProgram.Data}
    (bits : List Bool)
    (hs : out.stacks = Function.update (projectState id ports (copied moves d)).stacks 63 bits) :
    (embedState id ports (copied moves d) out).stacks =
      Function.update (copied moves d).stacks 201 bits := by
  change Function.extend ports out.stacks (copied moves d).stacks = _
  rw [hs, ProgramLinking.extend_update ports_injective]
  have hp := congrArg StructuredProgram.State.stacks
    (embedState_project id ports (copied moves d) Function.injective_id ports_injective)
  change Function.extend ports (projectState id ports (copied moves d)).stacks
    (copied moves d).stacks = (copied moves d).stacks at hp
  rw [hp]
  rfl

theorem cleaned_stacks {d e : Data} (h : WorkEmpty d) (bits : List Bool)
    (hs : e.stacks = Function.update (copied moves d).stacks 201 bits) :
    (cleared workspace e).stacks = Function.update d.stacks 201 bits := by
  funext i
  rw [cleared_stack]
  by_cases hi : i ∈ workspace
  · rw [ite_eq_left hi]
    have he : i ≠ 201 := by intro he; subst i; exact output_not_workspace hi
    rw [Function.update_of_ne he]
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hi
    exact (work_target h m hm).symm
  · rw [ite_eq_right hi, hs]
    by_cases he : i = 201
    · subst i; simp only [Function.update_same]
    · rw [Function.update_of_ne he, Function.update_of_ne he]
      apply copied_frame
      intro m hm him
      exact hi (List.mem_map.mpr ⟨m, hm, him.symm⟩)

end SubexponentialSAT.SubexpNodeBasisExecution

end OAI.Algorithms
