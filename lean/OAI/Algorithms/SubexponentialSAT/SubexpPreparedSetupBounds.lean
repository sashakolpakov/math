import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedSetupCalls

namespace OAI.Algorithms

/-! Linear copy/cleanup overhead for the fixed prepared-ring call interface. -/

namespace SubexponentialSAT.SubexpPreparedSetupCalls

open BitProgram StructuredCalls SubexpSetupStorage

def StackBound {r s : ℕ} (a : StructuredProgram.State r s) (W : ℕ) : Prop :=
  ∀ i, (a.stacks i).length ≤ W

theorem clearMany_bound {S : ℕ} (ps : List (Fin S)) (a : SubexpSetupStorage.Data S)
    {W : ℕ} (ha : StackBound a W) : StackBound (clearManyState ps a) W := by
  intro i
  rw [clearMany_stacks]
  split
  · exact Nat.zero_le _
  · exact ha i

theorem clearManyCost_le {S : ℕ} (ps : List (Fin S)) (a : SubexpSetupStorage.Data S)
    {W : ℕ} (ha : StackBound a W) : clearManyCost ps a ≤ ps.length * (2 * W + 3) := by
  induction ps generalizing a with
  | nil => simp [clearManyCost]
  | cons p ps ih =>
    have hp : StackBound (clearState p a) W := clearMany_bound [p] a ha
    have hh := ih (clearState p a) hp
    have hh' := ha p
    simp only [clearManyCost, List.length_cons]
    rw [Nat.add_mul]
    omega

theorem copyManyCost_le {S : ℕ} (ps : List (Fin S × Fin S))
    (a : SubexpSetupStorage.Data S) {W : ℕ}
    (hsource : ∀ p ∈ ps, (a.stacks p.1).length ≤ W)
    (hsep : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2) :
    copyManyCost ps a ≤ ps.length * (7 * W + 5) := by
  induction ps generalizing a with
  | nil => simp [copyManyCost]
  | cons p ps ih =>
    have hp := hsource p (by simp)
    have hrest : ∀ q ∈ ps, ((copyState p.1 p.2 a).stacks q.1).length ≤ W := by
      intro q hq
      rw [copyState_frame _ _ _ _ (hsep q (by simp [hq]) p (by simp))]
      exact hsource q (by simp [hq])
    have hh := ih (copyState p.1 p.2 a) hrest
      (fun q hq z hz => hsep q (by simp [hq]) z (by simp [hz]))
    simp only [copyManyCost, List.length_cons]
    rw [Nat.add_mul]
    omega

theorem copyMany_bound {S : ℕ} (ps : List (Fin S × Fin S))
    (a : SubexpSetupStorage.Data S) {W : ℕ} (ha : StackBound a W)
    (hd : (ps.map Prod.snd).Nodup)
    (hc : ∀ p ∈ ps, a.stacks p.2 = [])
    (hsep : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2) :
    StackBound (copyManyState ps a) W := by
  intro i
  by_cases hm : ∃ p ∈ ps, p.2 = i
  · obtain ⟨p, hp, rfl⟩ := hm
    rw [copyMany_value ps a hd hc hsep p hp]
    exact ha p.1
  · rw [copyMany_frame]
    · exact ha i
    · intro p hp he
      exact hm ⟨p, hp, he.symm⟩

theorem beforeCopies_bound {S : ℕ} (tmp : Fin S) (ps : List (Fin S))
    (a : SubexpSetupStorage.Data S) {W : ℕ} (ha : StackBound a W) :
    StackBound (beforeCopies tmp ps a) W := by
  intro i
  change ((resetManyState workRegisters (clearManyState ps (clearManyState [tmp] a))).stacks i).length ≤ W
  rw [resetMany_stacks]
  exact clearMany_bound ps _ (clearMany_bound [tmp] a ha) i

theorem prepared_bound {s : ℕ} (hs : s ≤ 24) (xs : List (Cache × Fin s))
    (a : Data) {W : ℕ} (ha : StackBound a W) (hd : (xs.map Prod.snd).Nodup) :
    StackBound (prepared hs xs a) W := by
  apply copyMany_bound _ _ (beforeCopies_bound temporary (ports hs) a ha)
  · simpa only [inputs, List.map_map, Function.comp_def] using
      (List.Nodup.map (work_injective hs) hd)
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
      ite_eq_left (work_mem_ports hs q.2)]
  · intro p hp q hq
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact cache_ne_work hs p'.1 q'.2

theorem middle_bound {r s : ℕ} (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (a : Data) (out : StructuredProgram.State r s)
    {W : ℕ} (ha : StackBound a W) (hd : (xs.map Prod.snd).Nodup)
    (hout : StackBound out W) : StackBound (middle hr hs xs a out) W := by
  classical
  intro i
  by_cases hi : ∃ j, work hs j = i
  · obtain ⟨j, rfl⟩ := hi
    unfold middle
    rw [embedState_stack _ _ _ _ (work_injective hs)]
    exact hout j
  · unfold middle
    rw [embedState_stack_frame _ _ _ _ _ hi]
    exact prepared_bound hs xs a ha hd i

theorem prepareCost_le {s : ℕ} (hs : s ≤ 24) (xs : List (Cache × Fin s))
    (a : Data) {W : ℕ} (ha : StackBound a W) (hx : xs.length ≤ 4) :
    prepareCost temporary (ports hs) (inputs hs xs) a ≤
      25 * (2 * W + 3) + 9 + 4 * (7 * W + 5) := by
  have h1 := clearManyCost_le [temporary] a ha
  have h2 := clearManyCost_le (ports hs) (clearManyState [temporary] a)
    (clearMany_bound [temporary] a ha)
  have hp : (ports hs).length = s := by simp [ports]
  have hi : (inputs hs xs).length = xs.length := by simp [inputs]
  have h3 := copyManyCost_le (inputs hs xs) (beforeCopies temporary (ports hs) a)
    (fun p hp => beforeCopies_bound temporary (ports hs) a ha p.1) (by
      intro p hp q hq
      obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      exact cache_ne_work hs p'.1 q'.2)
  have h2' : clearManyCost (ports hs) (clearManyState [temporary] a) ≤
      24 * (2 * W + 3) := h2.trans (by rw [hp]; exact Nat.mul_le_mul_right _ hs)
  have h3' : copyManyCost (inputs hs xs) (beforeCopies temporary (ports hs) a) ≤
      4 * (7 * W + 5) := h3.trans (by rw [hi]; exact Nat.mul_le_mul_right _ hx)
  simp only [List.length_singleton, one_mul] at h1
  unfold prepareCost
  omega

theorem finish_one_bound {s : ℕ} (hs : s ≤ 24) (src : Fin s) (dst : Cache)
    (a : Data) {W : ℕ} (ha : StackBound a W) :
    StackBound (finishState (ports hs) (outputs hs [(src, dst)]) a) W := by
  have hc := clearMany_bound [cache dst] a ha
  have hcopy : StackBound
      (copyManyState [(work hs src, cache dst)] (clearManyState [cache dst] a)) W := by
    apply copyMany_bound _ _ hc (by simp)
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      rw [clearMany_stacks]; simp
    · intro p hp q hq
      simp only [List.mem_singleton] at hp hq
      subst p; subst q
      exact (cache_ne_work hs dst src).symm
  intro i
  change ((resetManyState workRegisters
    (clearManyState (ports hs)
      (copyManyState [(work hs src, cache dst)] (clearManyState [cache dst] a)))).stacks i).length ≤ W
  rw [resetMany_stacks]
  exact clearMany_bound (ports hs) _ hcopy i

theorem finish_one_cost_le {s : ℕ} (hs : s ≤ 24) (src : Fin s) (dst : Cache)
    (a : Data) {W : ℕ} (ha : StackBound a W) :
    finishCost (ports hs) (outputs hs [(src, dst)]) a ≤
      25 * (2 * W + 3) + (7 * W + 5) + 9 := by
  have hc := clearMany_bound [cache dst] a ha
  have hcopy : StackBound
      (copyManyState [(work hs src, cache dst)] (clearManyState [cache dst] a)) W := by
    apply copyMany_bound _ _ hc (by simp)
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      rw [clearMany_stacks]; simp
    · intro p hp q hq
      simp only [List.mem_singleton] at hp hq
      subst p; subst q
      exact (cache_ne_work hs dst src).symm
  have hclear := clearManyCost_le (ports hs) _ hcopy
  have hp : (ports hs).length = s := by simp [ports]
  have hclear' : clearManyCost (ports hs)
      (copyManyState [(work hs src, cache dst)] (clearManyState [cache dst] a)) ≤
      24 * (2 * W + 3) := hclear.trans (by rw [hp]; exact Nat.mul_le_mul_right _ hs)
  have hdst := ha (cache dst)
  have hsrc := hc (work hs src)
  simp only [finishCost, outputs, List.map_cons, List.map_nil,
    copyManyCost, clearManyCost, add_zero]
  change 2 * (a.stacks (cache dst)).length + 3 +
    (7 * ((clearManyState [cache dst] a).stacks (work hs src)).length + 5 +
      (clearManyCost (ports hs)
        (copyManyState [(work hs src, cache dst)] (clearManyState [cache dst] a)) + 9)) ≤ _
  omega

theorem stage_one_cost_le {r s : ℕ} (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (src : Fin s) (dst : Cache)
    (a : Data) (out : StructuredProgram.State r s) (t : ℕ) {W : ℕ}
    (ha : StackBound a W) (hd : (xs.map Prod.snd).Nodup) (hx : xs.length ≤ 4)
    (hout : StackBound out W) :
    stageCost hr hs xs [(src, dst)] a out t ≤ t + 200 * (W + 1) := by
  have hp := prepareCost_le hs xs a ha hx
  have hf := finish_one_cost_le hs src dst (middle hr hs xs a out)
    (middle_bound hr hs xs a out ha hd hout)
  unfold stageCost
  omega

theorem returned_one_bound {r s : ℕ} (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (src : Fin s) (dst : Cache)
    (a : Data) (out : StructuredProgram.State r s) {W : ℕ}
    (ha : StackBound a W) (hd : (xs.map Prod.snd).Nodup) (hout : StackBound out W) :
    StackBound (returned hr hs xs [(src, dst)] a out) W :=
  finish_one_bound hs src dst _ (middle_bound hr hs xs a out ha hd hout)

def cacheWords (a : Data) : Cache → List Bool := a.stacks ∘ cache

theorem returned_one_words {r s : ℕ} (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (src : Fin s) (dst : Cache)
    (a : Data) (out : StructuredProgram.State r s) :
    cacheWords (returned hr hs xs [(src, dst)] a out) =
      Function.update (cacheWords a) dst (out.stacks src) := by
  funext i
  by_cases hi : i = dst
  · subst i
    exact (returned_word hr hs xs [(src, dst)] a out (by simp) (src, dst) (by simp)).trans
      (by simp)
  · exact (returned_frame hr hs xs [(src, dst)] a out i (by simpa using hi)).trans
      (by simp [hi, cacheWords])

/-- The complete instruction count includes copies, clears, register resets,
and the supplied concrete callee execution. -/
theorem run_one {r s l : ℕ} (p : Program r s l) (hr : r ≤ 9) (hs : s ≤ 24)
    (xs : List (Cache × Fin s)) (src : Fin s) (dst : Cache) (a : Data)
    (start out : StructuredProgram.State r s) {W N : ℕ}
    (ha : StackBound a W) (hd : (xs.map Prod.snd).Nodup) (hx : xs.length ≤ 4)
    (hout : StackBound out W)
    (hlocal : project (registers hr) (work hs) (prepared hs xs a) = start)
    (ht : RunsIn p N (start.withPC (some p.entry)) (out.withPC none)) :
    ∃ n b, Eval (stage p hr hs xs [(src, dst)]) n a b ∧
      n ≤ N + 200 * (W + 1) ∧ StackBound b W ∧
      cacheWords b = Function.update (cacheWords a) dst (out.stacks src) := by
  obtain ⟨t, ht, htrace⟩ := ht
  refine ⟨stageCost hr hs xs [(src, dst)] a out t,
    returned hr hs xs [(src, dst)] a out,
    stage_eval p hr hs xs [(src, dst)] a start out hlocal htrace, ?_,
    returned_one_bound hr hs xs src dst a out ha hd hout,
    returned_one_words hr hs xs src dst a out⟩
  exact (stage_one_cost_le hr hs xs src dst a out t ha hd hx hout).trans
    (Nat.add_le_add_right ht _)

end SubexponentialSAT.SubexpPreparedSetupCalls

end OAI.Algorithms
