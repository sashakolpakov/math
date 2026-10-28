import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

namespace OAI.Algorithms

/-! Frame and value rules for the actual setup copy/cleanup routines. -/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem copyMany_reg_zero {S : ℕ} (ps : List (Fin S × Fin S)) (a : Data S) (i : Fin 16)
    (hi : a.regs i = false) : (copyManyState ps a).regs i = false := by
  induction ps generalizing a with
  | nil => exact hi
  | cons p ps ih =>
    apply ih
    simp [copyState, readRegs, Function.update_apply, hi]

theorem copyMany_reg_frame {S : ℕ} (ps : List (Fin S × Fin S)) (a : Data S) (i : Fin 16)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : (copyManyState ps a).regs i = a.regs i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    exact (ih (copyState p.1 p.2 a)).trans
      (StackRoutines.readRegs_frame a.regs 0 1 i none h0 h1)

theorem clearMany_reg_frame {S : ℕ} (ps : List (Fin S)) (a : Data S) (i : Fin 16)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : (clearManyState ps a).regs i = a.regs i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    exact (ih (clearState p a)).trans
      (StackRoutines.readRegs_frame a.regs 0 1 i none h0 h1)

/-- Distinct empty destinations receive the original source words. The source
locations are disjoint from every destination, so earlier copies preserve them. -/
theorem copyMany_value {S : ℕ} (ps : List (Fin S × Fin S)) (a : Data S)
    (hdup : (ps.map Prod.snd).Nodup)
    (hclear : ∀ p ∈ ps, a.stacks p.2 = [])
    (hsep : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2)
    (p : Fin S × Fin S) (hp : p ∈ ps) :
    (copyManyState ps a).stacks p.2 = a.stacks p.1 := by
  induction ps generalizing a p with
  | nil => simp at hp
  | cons q qs ih =>
    have hd : q.2 ∉ qs.map Prod.snd ∧ (qs.map Prod.snd).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using hdup
    have hne : ∀ z ∈ qs, z.2 ≠ q.2 := by
      intro z hz he
      exact hd.1 (List.mem_map.mpr ⟨z, hz, he⟩)
    rcases List.mem_cons.mp hp with he | hp
    · subst p
      have hf := copyMany_frame qs (copyState q.1 q.2 a) q.2
        (fun z hz => (hne z hz).symm)
      change (copyManyState qs (copyState q.1 q.2 a)).stacks q.2 = _
      rw [hf]
      simp [copyState, StackRoutines.copyStacks, hclear q (by simp)]
    · have hc : ∀ z ∈ qs, (copyState q.1 q.2 a).stacks z.2 = [] := by
        intro z hz
        exact (copyState_frame q.1 q.2 z.2 a (hne z hz)).trans
          (hclear z (by simp [hz]))
      have hs : ∀ z ∈ qs, ∀ w ∈ qs, z.1 ≠ w.2 := by
        intro z hz w hw
        exact hsep z (by simp [hz]) w (by simp [hw])
      exact (ih (copyState q.1 q.2 a) hd.2 hc hs p hp).trans
        (copyState_frame q.1 q.2 p.1 a (hsep p (by simp [hp]) q (by simp)))

theorem prepare_reg {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (i : Fin 9) :
    (prepareState tmp ports inputs a).regs (i.castLE (by decide)) = false :=
  copyMany_reg_zero _ _ _ (resetWork_reg _ i)

theorem prepare_flag {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) :
    (prepareState tmp ports inputs a).regs 15 = a.regs 15 := by
  unfold prepareState beforeCopies
  rw [copyMany_reg_frame _ _ _ (by decide) (by decide), resetWork_flag,
    clearMany_reg_frame _ _ _ (by decide) (by decide),
    clearMany_reg_frame _ _ _ (by decide) (by decide)]

theorem finish_flag {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) :
    (finishState ports outputs a).regs 15 = a.regs 15 := by
  unfold finishState
  rw [resetWork_flag, clearMany_reg_frame _ _ _ (by decide) (by decide),
    copyMany_reg_frame _ _ _ (by decide) (by decide),
    clearMany_reg_frame _ _ _ (by decide) (by decide)]

theorem prepare_frame {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (ht : i ≠ tmp) (hp : i ∉ ports) (hi : ∀ p ∈ inputs, i ≠ p.2) :
    (prepareState tmp ports inputs a).stacks i = a.stacks i := by
  unfold prepareState beforeCopies
  rw [copyMany_frame _ _ _ hi, resetMany_stacks, clearMany_stacks,
    ite_eq_right hp, clearMany_stacks]
  simp [ht]

theorem finish_frame {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (hp : i ∉ ports) (ho : ∀ p ∈ outputs, i ≠ p.2) :
    (finishState ports outputs a).stacks i = a.stacks i := by
  have hmem : i ∉ outputs.map Prod.snd := by
    intro hi
    obtain ⟨p, hm, he⟩ := List.mem_map.mp hi
    exact ho p hm he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hp,
    copyMany_frame _ _ _ ho, clearMany_stacks, ite_eq_right hmem]

theorem finish_value {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S)
    (hdup : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (p : Fin S × Fin S) (hp : p ∈ outputs) (hport : p.2 ∉ ports) :
    (finishState ports outputs a).stacks p.2 = a.stacks p.1 := by
  have hc : ∀ q ∈ outputs, (clearManyState (outputs.map Prod.snd) a).stacks q.2 = [] := by
    intro q hq
    rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨q, hq, rfl⟩)]
  have hs : p.1 ∉ outputs.map Prod.snd := by
    intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    exact hsep p hp q hq he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hport,
    copyMany_value _ _ hdup hc hsep p hp, clearMany_stacks, ite_eq_right hs]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
