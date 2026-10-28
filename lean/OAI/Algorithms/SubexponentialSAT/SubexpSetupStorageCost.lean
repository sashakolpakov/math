import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStages

namespace OAI.Algorithms

/-!
# Cost of the concrete setup storage instructions

Copying and cleanup are charged by the lengths of the words physically read.
The final stage bound is linear in a common word bound; its coefficients depend
only on the statically allocated ports and copy lists.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

def WordBound {r s : ℕ} (B : ℕ) (a : State r s) : Prop :=
  ∀ i, (a.stacks i).length ≤ B

theorem clearState_wordBound {S : ℕ} (p : Fin S) (a : Data S) (B : ℕ)
    (ha : WordBound B a) : WordBound B (clearState p a) := by
  intro i
  by_cases hi : i = p
  · subst i
    simp [clearState]
  · simpa [clearState, hi] using ha i

theorem clearMany_wordBound {S : ℕ} (ps : List (Fin S)) (a : Data S) (B : ℕ)
    (ha : WordBound B a) : WordBound B (clearManyState ps a) := by
  intro i
  rw [clearMany_stacks]
  split
  · simp
  · exact ha i

theorem resetMany_wordBound {S : ℕ} (rs : List (Fin 16)) (a : Data S) (B : ℕ)
    (ha : WordBound B a) : WordBound B (resetManyState rs a) := by
  intro i
  simpa only [resetMany_stacks] using ha i

theorem clearManyCost_le {S : ℕ} (ps : List (Fin S)) (a : Data S) (B : ℕ)
    (ha : WordBound B a) : clearManyCost ps a ≤ ps.length * (2 * B + 3) := by
  induction ps generalizing a with
  | nil => simp [clearManyCost]
  | cons p ps ih =>
    have hc := ih (clearState p a) (clearState_wordBound p a B ha)
    have hp : 2 * (a.stacks p).length + 3 ≤ 2 * B + 3 := by
      have := ha p
      omega
    calc
      clearManyCost (p :: ps) a =
          (2 * (a.stacks p).length + 3) + clearManyCost ps (clearState p a) := rfl
      _ ≤ (2 * B + 3) + ps.length * (2 * B + 3) := Nat.add_le_add hp hc
      _ = (p :: ps).length * (2 * B + 3) := by simp only [List.length_cons]; ring

theorem copyManyCost_le {S : ℕ} (ps : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hsep : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2)
    (ha : ∀ p ∈ ps, (a.stacks p.1).length ≤ B) :
    copyManyCost ps a ≤ ps.length * (7 * B + 5) := by
  induction ps generalizing a with
  | nil => simp [copyManyCost]
  | cons p ps ih =>
    have hs : ∀ q ∈ ps, ∀ z ∈ ps, q.1 ≠ z.2 := by
      intro q hq z hz
      exact hsep q (List.mem_cons_of_mem _ hq) z (List.mem_cons_of_mem _ hz)
    have hb : ∀ q ∈ ps, ((copyState p.1 p.2 a).stacks q.1).length ≤ B := by
      intro q hq
      rw [copyState_frame _ _ _ _
        (hsep q (List.mem_cons_of_mem _ hq) p (List.mem_cons_self))]
      exact ha q (List.mem_cons_of_mem _ hq)
    have hc := ih (copyState p.1 p.2 a) hs hb
    have hp : 7 * (a.stacks p.1).length + 5 ≤ 7 * B + 5 := by
      have := ha p List.mem_cons_self
      omega
    calc
      copyManyCost (p :: ps) a =
          (7 * (a.stacks p.1).length + 5) + copyManyCost ps (copyState p.1 p.2 a) := rfl
      _ ≤ (7 * B + 5) + ps.length * (7 * B + 5) := Nat.add_le_add hp hc
      _ = (p :: ps).length * (7 * B + 5) := by simp only [List.length_cons]; ring

theorem copyMany_wordBound {S : ℕ} (ps : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (ps.map Prod.snd).Nodup)
    (hz : ∀ p ∈ ps, a.stacks p.2 = [])
    (hsep : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2)
    (ha : WordBound B a) : WordBound B (copyManyState ps a) := by
  intro i
  by_cases hm : ∃ p ∈ ps, p.2 = i
  · obtain ⟨p, hp, rfl⟩ := hm
    rw [copyMany_value ps a hd hz hsep p hp]
    exact ha p.1
  · have hi : ∀ p ∈ ps, i ≠ p.2 := by
      intro p hp he
      exact hm ⟨p, hp, he.symm⟩
    rw [copyMany_frame ps a i hi]
    exact ha i

theorem beforeCopies_wordBound {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (a : Data S) (B : ℕ) (ha : WordBound B a) :
    WordBound B (beforeCopies tmp ports a) :=
  resetMany_wordBound _ _ B
    (clearMany_wordBound ports _ B (clearMany_wordBound [tmp] a B ha))

theorem prepare_wordBound {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (inputs.map Prod.snd).Nodup)
    (hp : ∀ p ∈ inputs, p.2 ∈ ports)
    (hsep : ∀ p ∈ inputs, ∀ q ∈ inputs, p.1 ≠ q.2)
    (ha : WordBound B a) : WordBound B (prepareState tmp ports inputs a) := by
  apply copyMany_wordBound inputs _ B hd _ hsep (beforeCopies_wordBound tmp ports a B ha)
  intro p hm
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks, ite_eq_left (hp p hm)]

theorem prepareCost_le {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hsep : ∀ p ∈ inputs, ∀ q ∈ inputs, p.1 ≠ q.2)
    (ha : WordBound B a) :
    prepareCost tmp ports inputs a ≤
      (2 * B + 3) + (ports.length * (2 * B + 3) + (9 + inputs.length * (7 * B + 5))) := by
  have htmp := clearManyCost_le [tmp] a B ha
  have hports := clearManyCost_le ports (clearManyState [tmp] a) B
    (clearMany_wordBound [tmp] a B ha)
  have hcopy := copyManyCost_le inputs (beforeCopies tmp ports a) B hsep
    (fun p _ => beforeCopies_wordBound tmp ports a B ha p.1)
  simpa only [prepareCost, List.length_singleton, one_mul] using
    Nat.add_le_add htmp (Nat.add_le_add hports (Nat.add_le_add_left hcopy 9))

theorem finishCopies_wordBound {S : ℕ} (outputs : List (Fin S × Fin S))
    (a : Data S) (B : ℕ) (hd : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (ha : WordBound B a) :
    WordBound B (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)) := by
  apply copyMany_wordBound outputs _ B hd _ hsep
    (clearMany_wordBound (outputs.map Prod.snd) a B ha)
  intro p hp
  rw [clearMany_stacks, ite_eq_left (List.mem_map.mpr ⟨p, hp, rfl⟩)]

theorem finish_wordBound {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (ha : WordBound B a) : WordBound B (finishState ports outputs a) :=
  resetMany_wordBound _ _ B
    (clearMany_wordBound ports _ B (finishCopies_wordBound outputs a B hd hsep ha))

theorem finishCost_le {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (B : ℕ)
    (hd : (outputs.map Prod.snd).Nodup)
    (hsep : ∀ p ∈ outputs, ∀ q ∈ outputs, p.1 ≠ q.2)
    (ha : WordBound B a) :
    finishCost ports outputs a ≤ outputs.length * (2 * B + 3) +
      (outputs.length * (7 * B + 5) + (ports.length * (2 * B + 3) + 9)) := by
  have hout := clearManyCost_le (outputs.map Prod.snd) a B ha
  have hcopy := copyManyCost_le outputs (clearManyState (outputs.map Prod.snd) a) B hsep
    (fun p _ => clearMany_wordBound (outputs.map Prod.snd) a B ha p.1)
  have hports := clearManyCost_le ports
    (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)) B
    (finishCopies_wordBound outputs a B hd hsep ha)
  simpa only [finishCost, List.length_map] using
    Nat.add_le_add hout (Nat.add_le_add hcopy (Nat.add_le_add_right hports 9))

theorem embedState_wordBound {r s S : ℕ} (register : Fin r → Fin 16)
    (stack : Fin s → Fin S) (frame : Data S) (out : State r s) (B : ℕ)
    (hs : Function.Injective stack) (hf : WordBound B frame) (ho : WordBound B out) :
    WordBound B (embedState register stack frame out) := by
  intro i
  by_cases hm : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hm
    rw [embedState_stack register stack frame out hs j]
    exact ho j
  · rw [embedState_stack_frame register stack frame out i hm]
    exact hf i

end SubexponentialSAT.SubexpSetupStorage

namespace SubexponentialSAT.SubexpSetupProgram

open BitProgram StructuredCalls SubexpSetupStorage

/-- The allocation and copy-list lengths are fixed when the setup program is
fixed, so this overhead is linear in the runtime word bound. -/
def storageOverhead (ports inputs outputs B : ℕ) : ℕ :=
  (2 * ports + outputs + 1) * (2 * B + 3) + (inputs + outputs) * (7 * B + 5) + 18

theorem storageOverhead_linear (ports inputs outputs B : ℕ) :
    storageOverhead ports inputs outputs B ≤
      (6 * ports + 7 * inputs + 10 * outputs + 21) * (B + 1) := by
  have hclear : 2 * B + 3 ≤ 3 * (B + 1) := by omega
  have hcopy : 7 * B + 5 ≤ 7 * (B + 1) := by omega
  have hreset : 18 ≤ 18 * (B + 1) := by omega
  calc
    storageOverhead ports inputs outputs B ≤
        (2 * ports + outputs + 1) * (3 * (B + 1)) +
          (inputs + outputs) * (7 * (B + 1)) + 18 * (B + 1) :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left _ hclear) (Nat.mul_le_mul_left _ hcopy)) hreset
    _ = (6 * ports + 7 * inputs + 10 * outputs + 21) * (B + 1) := by ring

theorem inputCopies_separated (c : Config) {s : ℕ} (hs : s < helperSize c)
    (inputs : List (Fin (stackCount c) × Fin s))
    (hi : ∀ p ∈ inputs, Protected c p.1) :
    ∀ p ∈ inputCopies c hs inputs, ∀ q ∈ inputCopies c hs inputs, p.1 ≠ q.2 := by
  intro p hp q hq
  obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
  obtain ⟨q', _, rfl⟩ := List.mem_map.mp hq
  exact protected_ne_work c hs (hi p' hp') q'.2

theorem outputCopies_separated (c : Config) {s : ℕ} (hs : s < helperSize c)
    (outputs : List (Fin s × Fin (stackCount c)))
    (ho : ∀ p ∈ outputs, Protected c p.2) :
    ∀ p ∈ outputCopies c hs outputs, ∀ q ∈ outputCopies c hs outputs, p.1 ≠ q.2 := by
  intro p hp q hq
  obtain ⟨p', _, rfl⟩ := List.mem_map.mp hp
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
  exact (protected_ne_work c hs (ho q' hq') p'.1).symm

theorem prepared_wordBound (c : Config) {s : ℕ} (hs : s < helperSize c)
    (inputs : List (Fin (stackCount c) × Fin s)) (a : SetupState c) (B : ℕ)
    (hi : ∀ p ∈ inputs, Protected c p.1) (hd : (inputs.map Prod.snd).Nodup)
    (ha : WordBound B a) : WordBound B (prepared c hs inputs a) := by
  apply prepare_wordBound _ _ _ _ B _ _ (inputCopies_separated c hs inputs hi) ha
  · simpa only [inputCopies, List.map_map, Function.comp_def] using
      List.Nodup.map (workPort_injective c hs) hd
  · intro p hp
    obtain ⟨p', _, rfl⟩ := List.mem_map.mp hp
    exact work_mem_localPorts c hs p'.2

theorem stageCost_le (c : Config) {r s : ℕ} (register : Fin r → Fin 16)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c)
    (out : State r s) (t B : ℕ)
    (hi : ∀ p ∈ inputs, Protected c p.1) (ho : ∀ p ∈ outputs, Protected c p.2)
    (hdi : (inputs.map Prod.snd).Nodup) (hdo : (outputs.map Prod.snd).Nodup)
    (ha : WordBound B a) (hout : WordBound B out) :
    stageCost c register hs inputs outputs a out t ≤
      t + storageOverhead s inputs.length outputs.length B := by
  have hpre := prepareCost_le (temporary c) (localPorts c hs) (inputCopies c hs inputs) a B
    (inputCopies_separated c hs inputs hi) ha
  have hmid := embedState_wordBound register (workPort c hs) (prepared c hs inputs a) out B
    (workPort_injective c hs) (prepared_wordBound c hs inputs a B hi hdi ha) hout
  have hd : ((outputCopies c hs outputs).map Prod.snd).Nodup := by
    simpa only [outputCopies, List.map_map, Function.comp_def] using hdo
  have hfin := finishCost_le (localPorts c hs) (outputCopies c hs outputs)
    (embedState register (workPort c hs) (prepared c hs inputs a) out) B hd
    (outputCopies_separated c hs outputs ho) hmid
  simp only [localPorts, List.length_ofFn, inputCopies, outputCopies, List.length_map] at hpre hfin
  calc
    stageCost c register hs inputs outputs a out t ≤
        (2 * B + 3) + (s * (2 * B + 3) + (9 + inputs.length * (7 * B + 5))) +
          (t + (outputs.length * (2 * B + 3) +
            (outputs.length * (7 * B + 5) + (s * (2 * B + 3) + 9)))) :=
      Nat.add_le_add hpre (Nat.add_le_add_left hfin t)
    _ = t + storageOverhead s inputs.length outputs.length B := by
      unfold storageOverhead
      ring

theorem returned_wordBound (c : Config) {r s : ℕ} (register : Fin r → Fin 16)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c)
    (out : State r s) (B : ℕ)
    (hi : ∀ p ∈ inputs, Protected c p.1) (ho : ∀ p ∈ outputs, Protected c p.2)
    (hdi : (inputs.map Prod.snd).Nodup) (hdo : (outputs.map Prod.snd).Nodup)
    (ha : WordBound B a) (hout : WordBound B out) :
    WordBound B (returned c register hs inputs outputs a out) := by
  have hd : ((outputCopies c hs outputs).map Prod.snd).Nodup := by
    simpa only [outputCopies, List.map_map, Function.comp_def] using hdo
  exact finish_wordBound _ _ _ B hd (outputCopies_separated c hs outputs ho)
    (embedState_wordBound register (workPort c hs) (prepared c hs inputs a) out B
      (workPort_injective c hs) (prepared_wordBound c hs inputs a B hi hdi ha) hout)

end SubexponentialSAT.SubexpSetupProgram

end OAI.Algorithms
