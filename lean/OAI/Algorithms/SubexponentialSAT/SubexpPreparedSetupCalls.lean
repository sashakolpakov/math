import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames

namespace OAI.Algorithms

/-!
# Fixed storage for prepared-quartic setup

Twenty-four work stacks are reused by the concrete arithmetic routines. Nine
cache stacks occupy ports 24 through 32; port 33 is the physical copy temporary.
This module only supplies the copying, cleanup, and frame rules. A call is
justified by an actual trace of its finite instruction table.
-/

namespace SubexponentialSAT.SubexpPreparedSetupCalls

open BitProgram StructuredCalls SubexpSetupStorage

abbrev Data := StructuredProgram.State 16 34
abbrev Command := Cmd 16 34
abbrev Cache := Fin 9

def cache (i : Cache) : Fin 34 := ⟨24 + i.val, by omega⟩
def temporary : Fin 34 := 33
def work {s : ℕ} (hs : s ≤ 24) (i : Fin s) : Fin 34 := i.castLE (by omega)
def registers {r : ℕ} (hr : r ≤ 9) (i : Fin r) : Fin 16 := i.castLE (by omega)
def ports {s : ℕ} (hs : s ≤ 24) : List (Fin 34) := List.ofFn (work hs)
def inputs {s : ℕ} (hs : s ≤ 24) (xs : List (Cache × Fin s)) :=
  xs.map (fun p => (cache p.1, work hs p.2))
def outputs {s : ℕ} (hs : s ≤ 24) (xs : List (Fin s × Cache)) :=
  xs.map (fun p => (work hs p.1, cache p.2))

theorem cache_injective : Function.Injective cache := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [cache] at this
  omega

theorem work_injective {s : ℕ} (hs : s ≤ 24) : Function.Injective (work hs) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 34 => x.val) h)

theorem registers_injective {r : ℕ} (hr : r ≤ 9) :
    Function.Injective (registers hr) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

theorem cache_ne_work {s : ℕ} (hs : s ≤ 24) (i : Cache) (j : Fin s) :
    cache i ≠ work hs j := by
  intro h
  have hv := congrArg Fin.val h
  change 24 + i.val = j.val at hv
  omega

theorem cache_ne_temporary (i : Cache) : cache i ≠ temporary := by
  intro h
  have hv := congrArg Fin.val h
  change 24 + i.val = 33 at hv
  omega

theorem work_ne_temporary {s : ℕ} (hs : s ≤ 24) (j : Fin s) :
    work hs j ≠ temporary := by
  intro h
  have hv := congrArg Fin.val h
  change j.val = 33 at hv
  omega

theorem work_mem_ports {s : ℕ} (hs : s ≤ 24) (j : Fin s) : work hs j ∈ ports hs := by
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

theorem cache_not_ports {s : ℕ} (hs : s ≤ 24) (i : Cache) : cache i ∉ ports hs := by
  intro h
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp h
  exact cache_ne_work hs i j hj.symm

theorem inputs_good {s : ℕ} (hs : s ≤ 24) (xs : List (Cache × Fin s)) :
    ∀ p ∈ inputs hs xs, p.1 ≠ p.2 ∧ p.1 ≠ temporary ∧ temporary ≠ p.2 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact ⟨cache_ne_work hs q.1 q.2, cache_ne_temporary q.1,
    (work_ne_temporary hs q.2).symm⟩

theorem outputs_good {s : ℕ} (hs : s ≤ 24) (xs : List (Fin s × Cache)) :
    ∀ p ∈ outputs hs xs, p.1 ≠ p.2 ∧ p.1 ≠ temporary ∧ temporary ≠ p.2 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact ⟨(cache_ne_work hs q.2 q.1).symm, work_ne_temporary hs q.1,
    (cache_ne_temporary q.2).symm⟩

abbrev stage {r s l : ℕ} (p : Program r s l) (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (ys : List (Fin s × Cache)) : Command :=
  isolated p (registers hr) (work hs) temporary (ports hs) (inputs hs xs) (outputs hs ys)

def prepared {s : ℕ} (hs : s ≤ 24) (xs : List (Cache × Fin s)) (a : Data) : Data :=
  prepareState temporary (ports hs) (inputs hs xs) a

noncomputable def middle {r s : ℕ} (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (a : Data) (out : StructuredProgram.State r s) : Data :=
  embedState (registers hr) (work hs) (prepared hs xs a) out

noncomputable def returned {r s : ℕ} (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (ys : List (Fin s × Cache))
    (a : Data) (out : StructuredProgram.State r s) : Data :=
  finishState (ports hs) (outputs hs ys) (middle hr hs xs a out)

noncomputable def stageCost {r s : ℕ} (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (ys : List (Fin s × Cache))
    (a : Data) (out : StructuredProgram.State r s) (t : ℕ) : ℕ :=
  prepareCost temporary (ports hs) (inputs hs xs) a +
    (t + finishCost (ports hs) (outputs hs ys) (middle hr hs xs a out))

theorem prepared_frame {s : ℕ} (hs : s ≤ 24) (xs : List (Cache × Fin s))
    (a : Data) (i : Cache) : (prepared hs xs a).stacks (cache i) = a.stacks (cache i) := by
  apply prepare_frame _ _ _ _ _ (cache_ne_temporary i) (cache_not_ports hs i)
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact cache_ne_work hs i q.2

theorem prepared_word {s : ℕ} (hs : s ≤ 24) (xs : List (Cache × Fin s))
    (a : Data) (hd : (xs.map Prod.snd).Nodup) (p : Cache × Fin s) (hp : p ∈ xs) :
    (prepared hs xs a).stacks (work hs p.2) = a.stacks (cache p.1) := by
  have hd' : ((inputs hs xs).map Prod.snd).Nodup := by
    simpa only [inputs, List.map_map, Function.comp_def] using
      (List.Nodup.map (work_injective hs) hd)
  have hc : ∀ q ∈ inputs hs xs,
      (beforeCopies temporary (ports hs) a).stacks q.2 = [] := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
      ite_eq_left (work_mem_ports hs z.2)]
  have hsep : ∀ q ∈ inputs hs xs, ∀ z ∈ inputs hs xs, q.1 ≠ z.2 := by
    intro q hq z hz
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact cache_ne_work hs q'.1 z'.2
  have hv := copyMany_value (inputs hs xs) (beforeCopies temporary (ports hs) a)
    hd' hc hsep (cache p.1, work hs p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  change (prepared hs xs a).stacks (work hs p.2) = _ at hv
  rw [hv]
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
    ite_eq_right (cache_not_ports hs p.1)]
  simp [cache_ne_temporary p.1]

theorem prepared_empty {s : ℕ} (hs : s ≤ 24) (xs : List (Cache × Fin s))
    (a : Data) (j : Fin s) (hj : ∀ p ∈ xs, j ≠ p.2) :
    (prepared hs xs a).stacks (work hs j) = [] := by
  have hn : ∀ p ∈ inputs hs xs, work hs j ≠ p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact fun he => hj q hq (work_injective hs he)
  unfold prepared prepareState
  rw [copyMany_frame _ _ _ hn]
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
    ite_eq_left (work_mem_ports hs j)]

theorem prepared_register {r s : ℕ} (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (a : Data) (j : Fin r) :
    (prepared hs xs a).regs (registers hr j) = false :=
  prepare_reg _ _ _ _ (j.castLE hr)

theorem prepared_eq {r s : ℕ} (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (a : Data) (start : StructuredProgram.State r s)
    (hd : (xs.map Prod.snd).Nodup) (hreg : ∀ j, start.regs j = false)
    (hw : ∀ p ∈ xs, start.stacks p.2 = a.stacks (cache p.1))
    (hz : ∀ j, (∀ p ∈ xs, j ≠ p.2) → start.stacks j = []) :
    project (registers hr) (work hs) (prepared hs xs a) = start := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    exact (prepared_register hr hs xs a j).trans (hreg j).symm
  · funext j
    by_cases hm : ∃ p ∈ xs, p.2 = j
    · obtain ⟨p, hp, rfl⟩ := hm
      exact (prepared_word hs xs a hd p hp).trans (hw p hp).symm
    · have hj : ∀ p ∈ xs, j ≠ p.2 := by
        intro p hp he
        exact hm ⟨p, hp, he.symm⟩
      exact (prepared_empty hs xs a j hj).trans (hz j hj).symm

theorem stage_eval {r s l : ℕ} (p : Program r s l) (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (ys : List (Fin s × Cache)) (a : Data)
    (start out : StructuredProgram.State r s) {t : ℕ}
    (hlocal : project (registers hr) (work hs) (prepared hs xs a) = start)
    (ht : Trace p t (start.withPC (some p.entry)) (out.withPC none)) :
    Eval (stage p hr hs xs ys) (stageCost hr hs xs ys a out t) a
      (returned hr hs xs ys a out) := by
  apply isolated_eval p (registers hr) (work hs) (registers_injective hr) (work_injective hs)
    temporary (ports hs) (inputs hs xs) (outputs hs ys) a out
    (inputs_good hs xs) (outputs_good hs ys)
  · rintro ⟨j, hj⟩
    exact work_ne_temporary hs j hj
  · change Trace p t
      ((project (registers hr) (work hs) (prepared hs xs a)).withPC (some p.entry))
      (out.withPC none)
    rw [hlocal]
    exact ht

theorem returned_word {r s : ℕ} (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (ys : List (Fin s × Cache)) (a : Data)
    (out : StructuredProgram.State r s) (hd : (ys.map Prod.snd).Nodup)
    (p : Fin s × Cache) (hp : p ∈ ys) :
    (returned hr hs xs ys a out).stacks (cache p.2) = out.stacks p.1 := by
  have hd' : ((outputs hs ys).map Prod.snd).Nodup := by
    simpa only [outputs, List.map_map, Function.comp_def] using
      (List.Nodup.map cache_injective hd)
  have hsep : ∀ q ∈ outputs hs ys, ∀ z ∈ outputs hs ys, q.1 ≠ z.2 := by
    intro q hq z hz
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact (cache_ne_work hs z'.2 q'.1).symm
  exact (finish_value (ports hs) (outputs hs ys) _ hd' hsep
    (work hs p.1, cache p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    (cache_not_ports hs p.2)).trans
      (embedState_stack (registers hr) (work hs) _ out (work_injective hs) p.1)

theorem returned_frame {r s : ℕ} (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (ys : List (Fin s × Cache)) (a : Data)
    (out : StructuredProgram.State r s) (i : Cache) (hne : ∀ p ∈ ys, i ≠ p.2) :
    (returned hr hs xs ys a out).stacks (cache i) = a.stacks (cache i) := by
  have hno : ∀ p ∈ outputs hs ys, cache i ≠ p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact fun he => hne q hq (cache_injective he)
  exact (finish_frame (ports hs) (outputs hs ys) _ (cache i) (cache_not_ports hs i) hno).trans
    ((embedState_stack_frame (registers hr) (work hs) _ out (cache i) (by
      rintro ⟨j, hj⟩; exact cache_ne_work hs i j hj.symm)).trans
        (prepared_frame hs xs a i))

theorem stageCost_mono {r s : ℕ} (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (ys : List (Fin s × Cache)) (a : Data)
    (out : StructuredProgram.State r s) {t u : ℕ} (h : t ≤ u) :
    stageCost hr hs xs ys a out t ≤ stageCost hr hs xs ys a out u := by
  unfold stageCost
  omega

end SubexponentialSAT.SubexpPreparedSetupCalls

end OAI.Algorithms
