import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

namespace OAI.Algorithms

/-! One-output physical calls in the assignment-input workspace. -/

namespace SubexponentialSAT.Subexp.AssignmentInputCall

open BitProgram StructuredCalls SubexpSetupStorage

abbrev Data := State 16 48
abbrev Code := Cmd 16 48

def work : List (Fin 48) := List.ofFn (fun i : Fin 10 => ⟨12 + i.val, by omega⟩)

theorem mem_work (j : Fin 48) : j ∈ work ↔ 12 ≤ j.val ∧ j.val < 22 := by
  simp only [work, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    change 12 ≤ 12 + i.val ∧ 12 + i.val < 22
    have := i.isLt
    omega
  · rintro ⟨hlo, hhi⟩
    exact ⟨⟨j.val - 12, by omega⟩, Fin.ext (by simp; omega)⟩

def stack {s : ℕ} (hs : s ≤ 10) (i : Fin s) : Fin 48 := ⟨12 + i.val, by omega⟩
def register {r : ℕ} (hr : r ≤ 16) (i : Fin r) : Fin 16 := i.castLE hr

theorem stack_injective {s : ℕ} (hs : s ≤ 10) : Function.Injective (stack hs) := by
  intro i j h
  apply Fin.ext
  have h' := congrArg Fin.val h
  simpa [stack] using h'

theorem register_injective {r : ℕ} (hr : r ≤ 16) : Function.Injective (register hr) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 16 => x.val) h

theorem stack_mem {s : ℕ} (hs : s ≤ 10) (i : Fin s) : stack hs i ∈ work := by
  rw [mem_work]
  have := i.isLt
  simp only [stack, Fin.val_mk]
  omega

def Clean (a : Data) : Prop := (∀ j ∈ work, a.stacks j = []) ∧ a.stacks 31 = []

theorem beforeCopies_stacks (a : Data) (hc : Clean a) :
    (beforeCopies 31 work a).stacks = a.stacks := by
  funext j
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks]
  by_cases hw : j ∈ work
  · simp [hw, hc.1 j hw]
  · by_cases he : j = 31
    · subst j; simp [hw, hc.2]
    · simp [hw, he]

theorem prepare_one_stacks (a : Data) (hc : Clean a) (src dst : Fin 48)
    (hd : dst ∈ work) :
    (prepareState 31 work [(src, dst)] a).stacks =
      Function.update a.stacks dst (a.stacks src) := by
  simp [prepareState, copyManyState, copyState_stack, beforeCopies_stacks a hc,
    hc.1 dst hd]

theorem prepare_two_stacks (a : Data) (hc : Clean a) (src dst src' dst' : Fin 48)
    (hd : dst ∈ work) (hd' : dst' ∈ work) (hdd : dst' ≠ dst) (hsd : src' ≠ dst) :
    (prepareState 31 work [(src, dst), (src', dst')] a).stacks =
      Function.update (Function.update a.stacks dst (a.stacks src)) dst' (a.stacks src') := by
  simp [prepareState, copyManyState, copyState_stack, beforeCopies_stacks a hc,
    hc.1 dst hd, hc.1 dst' hd', hdd, hsd]

theorem prepare_one_local {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 10)
    (a : Data) (hc : Clean a) (src : Fin 48) (q : Fin s) (i : Fin s) :
    (project (register hr) (stack hs) (prepareState 31 work [(src, stack hs q)] a)).stacks i =
      if i = q then a.stacks src else [] := by
  change (prepareState 31 work [(src, stack hs q)] a).stacks (stack hs i) = _
  rw [prepare_one_stacks a hc src (stack hs q) (stack_mem hs q)]
  by_cases he : i = q
  · subst i; simp
  · have hne := fun h => he (stack_injective hs h)
    rw [Function.update_of_ne hne]
    simp [he, hc.1 _ (stack_mem hs i)]

theorem prepare_two_local {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 10)
    (a : Data) (hc : Clean a) (src src' : Fin 48) (q q' : Fin s)
    (hqq : q' ≠ q) (hsrc : src' ≠ stack hs q) (i : Fin s) :
    (project (register hr) (stack hs)
      (prepareState 31 work [(src, stack hs q), (src', stack hs q')] a)).stacks i =
      if i = q' then a.stacks src' else if i = q then a.stacks src else [] := by
  change (prepareState 31 work [(src, stack hs q), (src', stack hs q')] a).stacks
    (stack hs i) = _
  rw [prepare_two_stacks a hc src (stack hs q) src' (stack hs q')
    (stack_mem hs q) (stack_mem hs q') (fun h => hqq (stack_injective hs h)) hsrc]
  by_cases he' : i = q'
  · subst i; simp
  · have hne' := fun h => he' (stack_injective hs h)
    by_cases he : i = q
    · subst i
      rw [Function.update_of_ne hne']
      simp [he']
    · have hne := fun h => he (stack_injective hs h)
      rw [Function.update_of_ne hne', Function.update_of_ne hne]
      simp [he, he', hc.1 _ (stack_mem hs i)]

theorem prepare_regs (inputs : List (Fin 48 × Fin 48)) (a : Data) (j : Fin 16)
    (hj : j.val < 9) : (prepareState 31 work inputs a).regs j = false := by
  have hbefore : ∀ i : Fin 16, i.val < 9 → (beforeCopies 31 work a).regs i = false := by
    intro i hi
    exact resetWork_reg _ ⟨i.val, hi⟩
  suffices ∀ (b : Data), (∀ i : Fin 16, i.val < 9 → b.regs i = false) →
      (copyManyState inputs b).regs j = false from this _ hbefore
  induction inputs with
  | nil => intro b hb; exact hb j hj
  | cons p ps ih =>
      intro b hb
      apply ih (copyState p.1 p.2 b)
      intro i hi
      by_cases h0 : i = 0
      · subst i; simp [copyState, readRegs]
      · by_cases h1 : i = 1
        · subst i; simp [copyState, readRegs]
        · simpa [copyState, readRegs, h0, h1] using hb i hi

theorem prepare_frame (inputs : List (Fin 48 × Fin 48)) (a : Data)
    (hin : ∀ p ∈ inputs, p.2 ∈ work) (hc : Clean a) (j : Fin 48) (hj : j ∉ work) :
    (prepareState 31 work inputs a).stacks j = a.stacks j := by
  rw [prepareState, copyMany_frame inputs _ j]
  · simp only [beforeCopies, resetMany_stacks, clearMany_stacks, ite_eq_right hj]
    by_cases he : j = 31
    · subst j
      simp [hc.2]
    · simp [he]
  · intro p hp he
    exact hj (he.symm ▸ hin p hp)

theorem finish_one_stacks {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 10)
    (inputs : List (Fin 48 × Fin 48)) (a : Data) (out : State r s)
    (q : Fin s) (dst : Fin 48) (hd : dst ∉ work)
    (hin : ∀ p ∈ inputs, p.2 ∈ work) (hc : Clean a) :
    (finishState work [(stack hs q, dst)]
      (embedState (register hr) (stack hs) (prepareState 31 work inputs a) out)).stacks =
        Function.update a.stacks dst (out.stacks q) := by
  let middle := embedState (register hr) (stack hs) (prepareState 31 work inputs a) out
  have hqd : stack hs q ≠ dst := by
    intro he
    exact hd (he ▸ stack_mem hs q)
  have hq : middle.stacks (stack hs q) = out.stacks q :=
    embedState_stack _ _ _ _ (stack_injective hs) q
  funext j
  have hform : (finishState work [(stack hs q, dst)] middle).stacks j =
      if j ∈ work then [] else if j = dst then middle.stacks (stack hs q) else middle.stacks j := by
    by_cases he : j = dst <;>
      simp [finishState, resetMany_stacks, clearMany_stacks, copyManyState, copyState,
        StackRoutines.copyStacks, hqd, he]
  rw [hform]
  by_cases hw : j ∈ work
  · have hne : j ≠ dst := by intro he; exact hd (he ▸ hw)
    simp [hw, hne, hc.1 j hw]
  · have hf : middle.stacks j = a.stacks j := by
      rw [embedState_stack_frame]
      · exact prepare_frame inputs a hin hc j hw
      · rintro ⟨i, rfl⟩
        exact hw (stack_mem hs i)
    simp [hw, hf, hq, Function.update_apply]

abbrev call {r s l : ℕ} (p : Program r s l) (hr : r ≤ 16) (hs : s ≤ 10)
    (inputs : List (Fin 48 × Fin 48)) (q : Fin s) (dst : Fin 48) : Code :=
  isolated p (register hr) (stack hs) 31 work inputs [(stack hs q, dst)]

noncomputable def callCost {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 10)
    (inputs : List (Fin 48 × Fin 48)) (q : Fin s) (dst : Fin 48)
    (a : Data) (out : State r s) (ticks : ℕ) : ℕ :=
  prepareCost 31 work inputs a + (ticks + finishCost work [(stack hs q, dst)]
    (embedState (register hr) (stack hs) (prepareState 31 work inputs a) out))

theorem call_eval {r s l : ℕ} (p : Program r s l) (hr : r ≤ 16) (hs : s ≤ 10)
    (inputs : List (Fin 48 × Fin 48)) (q : Fin s) (dst : Fin 48)
    (a : Data) (out : State r s) {ticks : ℕ}
    (hd : dst ∉ work) (htmp : dst ≠ 31)
    (hin : ∀ x ∈ inputs, x.2 ∈ work)
    (hports : ∀ x ∈ inputs, x.1 ≠ x.2 ∧ x.1 ≠ 31 ∧ (31 : Fin 48) ≠ x.2)
    (hc : Clean a)
    (ht : Trace p ticks
      ((project (register hr) (stack hs) (prepareState 31 work inputs a)).withPC
        (some p.entry)) (out.withPC none)) :
    ∃ b, Eval (call p hr hs inputs q dst) (callCost hr hs inputs q dst a out ticks) a b ∧
      b.stacks = Function.update a.stacks dst (out.stacks q) ∧ Clean b := by
  have hframe : ¬ ∃ j, stack hs j = (31 : Fin 48) := by
    rintro ⟨j, h⟩
    have hm := stack_mem hs j
    rw [h, mem_work] at hm
    change 12 ≤ 31 ∧ 31 < 22 at hm
    omega
  have ho : ∀ x ∈ [(stack hs q, dst)], x.1 ≠ x.2 ∧ x.1 ≠ 31 ∧ (31 : Fin 48) ≠ x.2 := by
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    refine ⟨?_, ?_, Ne.symm htmp⟩
    · intro he
      change stack hs q = dst at he
      exact hd (he ▸ stack_mem hs q)
    · intro he; exact hframe ⟨q, he⟩
  have h := isolated_eval p (register hr) (stack hs) (register_injective hr)
    (stack_injective hs) 31 work inputs [(stack hs q, dst)] a out hports ho hframe ht
  have hout := finish_one_stacks hr hs inputs a out q dst hd hin hc
  refine ⟨_, h, hout, ?_⟩
  constructor
  · intro j hj
    have hne : j ≠ dst := by intro he; exact hd (he ▸ hj)
    rw [hout, Function.update_of_ne hne]
    exact hc.1 j hj
  · rw [hout, Function.update_of_ne (Ne.symm htmp)]
    exact hc.2

/-- A uniform bound on the contents of each physical stack. -/
def Within {r s : ℕ} (a : State r s) (B : ℕ) : Prop :=
  ∀ j, (a.stacks j).length ≤ B

theorem within_mono {r s : ℕ} {a : State r s} {B C : ℕ}
    (h : Within a B) (hBC : B ≤ C) : Within a C := fun j => (h j).trans hBC

theorem within_clear (port : Fin 48) (a : Data) (B : ℕ) (h : Within a B) :
    Within (clearState port a) B := by
  intro j
  by_cases hj : j = port
  · subst j; simp [clearState]
  · simpa [clearState, hj] using h j

theorem clearMany_bound (ports : List (Fin 48)) (a : Data) (B : ℕ) (h : Within a B) :
    Within (clearManyState ports a) B ∧ clearManyCost ports a ≤ ports.length * (2 * B + 3) := by
  induction ports generalizing a with
  | nil => exact ⟨h, by simp [clearManyCost]⟩
  | cons p ps ih =>
      obtain ⟨hs, ht⟩ := ih (clearState p a) (within_clear p a B h)
      refine ⟨hs, ?_⟩
      have hp := h p
      simp only [clearManyCost, List.length_cons]
      nlinarith

theorem within_copy (src dst : Fin 48) (a : Data) (B : ℕ) (h : Within a B) :
    Within (copyState src dst a) (2 * B) := by
  intro j
  by_cases hj : j = dst
  · subst j
    simp only [copyState_stack, Function.update_self, List.length_append]
    have hs := h src
    have hd := h dst
    omega
  · rw [copyState_frame src dst j a hj]
    exact (h j).trans (by omega)

theorem copyMany_bound (inputs : List (Fin 48 × Fin 48)) (a : Data) (B : ℕ)
    (h : Within a B) :
    Within (copyManyState inputs a) (2 ^ inputs.length * B) ∧
      copyManyCost inputs a ≤ inputs.length * (7 * 2 ^ inputs.length * B + 5) := by
  induction inputs generalizing a B with
  | nil => simpa [copyManyState, copyManyCost] using h
  | cons p ps ih =>
      obtain ⟨hs, ht⟩ := ih (copyState p.1 p.2 a) (2 * B) (within_copy p.1 p.2 a B h)
      constructor
      · simpa only [copyManyState, List.length_cons, pow_succ, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using hs
      · have hp := h p.1
        have hpow : 1 ≤ 2 ^ ps.length := one_le_pow₀ (by decide)
        have hpowB := Nat.mul_le_mul_right B hpow
        simp only [copyManyCost, List.length_cons, pow_succ]
        nlinarith

theorem within_reset (rs : List (Fin 16)) (a : Data) (B : ℕ) (h : Within a B) :
    Within (resetManyState rs a) B := by
  simpa only [Within, resetMany_stacks] using h

theorem prepare_bound (inputs : List (Fin 48 × Fin 48)) (a : Data) (B : ℕ)
    (hn : inputs.length ≤ 2) (h : Within a B) :
    Within (prepareState 31 work inputs a) (4 * B) ∧
      prepareCost 31 work inputs a ≤ 100 * (B + 1) := by
  obtain ⟨hc, hct⟩ := clearMany_bound [31] a B h
  obtain ⟨hw, hwt⟩ := clearMany_bound work (clearManyState [31] a) B hc
  have hb : Within (beforeCopies 31 work a) B := within_reset _ _ _ hw
  obtain ⟨hi, hit⟩ := copyMany_bound inputs (beforeCopies 31 work a) B hb
  have hpow : 2 ^ inputs.length ≤ 4 := by
    have : inputs.length = 0 ∨ inputs.length = 1 ∨ inputs.length = 2 := by omega
    rcases this with he | he | he <;> simp [he]
  constructor
  · exact within_mono hi (Nat.mul_le_mul_right B hpow)
  · have hlen : work.length = 10 := by simp [work]
    have hit' : copyManyCost inputs (beforeCopies 31 work a) ≤ 2 * (7 * 4 * B + 5) := by
      apply hit.trans
      exact Nat.mul_le_mul hn (by gcongr)
    simp only [List.length_singleton] at hct
    rw [hlen] at hwt
    unfold prepareCost
    nlinarith

theorem within_embed {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 10)
    (a : Data) (out : State r s) (B : ℕ) (ha : Within a B) (ho : Within out B) :
    Within (embedState (register hr) (stack hs) a out) B := by
  classical
  intro j
  by_cases hj : ∃ i, stack hs i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [embedState_stack _ _ _ _ (stack_injective hs)]
    exact ho i
  · rw [embedState_stack_frame _ _ _ _ j hj]
    exact ha j

theorem finish_bound (q dst : Fin 48) (a : Data) (B : ℕ) (h : Within a B) :
    finishCost work [(q, dst)] a ≤ 60 * (B + 1) := by
  obtain ⟨hc, hct⟩ := clearMany_bound [dst] a B h
  obtain ⟨hp, hpt⟩ := copyMany_bound [(q, dst)] (clearManyState [dst] a) B hc
  have hp' : Within (copyManyState [(q, dst)] (clearManyState [dst] a)) (2 * B) := by
    simpa using hp
  have hwt := (clearMany_bound work _ (2 * B) hp').2
  have hlen : work.length = 10 := by simp [work]
  rw [hlen] at hwt
  simp only [List.length_singleton, pow_one, Nat.one_mul] at hct hpt
  unfold finishCost
  simp only [List.map_cons, List.map_nil]
  nlinarith

theorem callCost_le {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 10)
    (inputs : List (Fin 48 × Fin 48)) (q : Fin s) (dst : Fin 48)
    (a : Data) (out : State r s) (ticks B : ℕ)
    (hn : inputs.length ≤ 2) (ha : Within a B) (ho : Within out B) :
    callCost hr hs inputs q dst a out ticks ≤ ticks + 400 * (B + 1) := by
  obtain ⟨hp, hpt⟩ := prepare_bound inputs a B hn ha
  have hm := within_embed hr hs (prepareState 31 work inputs a) out (4 * B) hp
    (within_mono ho (by omega))
  have hf := finish_bound (stack hs q) dst _ (4 * B) hm
  unfold callCost
  omega

end SubexponentialSAT.Subexp.AssignmentInputCall

end OAI.Algorithms
