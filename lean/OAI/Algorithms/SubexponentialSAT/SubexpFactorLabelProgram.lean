import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldRowPreparation
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorFrames

namespace OAI.Algorithms

/-!
# Physical base-p labels for one table row

The rank, modulus, and scope length are runtime data. The existing unranker
produces fixed-width little-endian digits; the actual ordered framer emits
the label list consumed by the factor-packet builder. All three masters are
preserved, and every work stack is cleared.
-/

namespace SubexponentialSAT.SubexpFactorLabelProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Word := List Bool
abbrev Data := State 8 17

def store (modulus rank arity digits todo output : Word) : Fin 17 → Word :=
  fun i => if i = 5 then modulus else if i = 12 then digits
    else if i = 13 then rank else if i = 14 then arity
    else if i = 15 then todo else if i = 16 then output else []

def state (regs : Fin 8 → Bool) (modulus rank arity digits todo output : Word) : Data :=
  ⟨regs, store modulus rank arity digits todo output⟩

def preparationPorts : Fin 15 ↪ Fin 17 := ⟨Fin.castAdd 2, Fin.castAdd_injective _ _⟩
def frameRegs : Fin 5 ↪ Fin 8 := ⟨Fin.castAdd 3, Fin.castAdd_injective _ _⟩
def framePorts : Fin 9 ↪ Fin 17 := ⟨![12, 5, 0, 15, 1, 2, 3, 4, 16], by decide⟩

abbrev prepare : Cmd 8 17 := .call
  (ProgramLinking.liftProgram SubexpFieldRowPreparation.program id preparationPorts)
abbrev copyArity : Cmd 8 17 := .call (StackRoutines.copyProgram 14 15 10 0 1)
abbrev frame : Cmd 8 17 := .call
  (ProgramLinking.liftProgram SubexpTaylorFrames.program frameRegs framePorts)
abbrev command : Cmd 8 17 := .seq prepare (.seq copyArity frame)
def program := compiled command (13 : Fin 17) 16

private theorem embed_prepare (regs oldRegs : Fin 8 → Bool)
    (modulus rank arity digits todo output : Word) :
    embedState id preparationPorts (state oldRegs modulus rank arity [] todo output)
      (SubexpFieldRowPreparation.data regs modulus rank arity [] [] digits) =
      state regs modulus rank arity digits todo output := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id preparationPorts.injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have hi15 : 15 ≤ i.val := by
      by_contra h
      have hlt : i.val < 15 := by omega
      exact hi ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    have hcases : i = 15 ∨ i = 16 := by
      have hil := i.isLt
      have hv : i.val = 15 ∨ i.val = 16 := by omega
      rcases hv with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hcases with rfl | rfl <;> rfl

theorem prepare_eval (regs : Fin 8 → Bool) (modulus rank arity : Word) :
    ∃ n ≤ SubexpFieldRowPreparation.budget modulus rank arity + 1, ∃ rf,
      Eval prepare n (state regs modulus rank arity [] [] [])
        (state rf modulus rank arity
          (SubexpBasePUnranking.digitWords modulus arity.length rank).flatten [] []) := by
  obtain ⟨rf, n, hn, ht⟩ :=
    SubexpFieldRowPreparation.program_runsIn regs modulus rank arity []
  have he := eval_call_lifted SubexpFieldRowPreparation.program id preparationPorts
    (state regs modulus rank arity [] [] [])
    Function.injective_id preparationPorts.injective ht
  refine ⟨n, hn, rf, ?_⟩
  simpa only [prepare, embed_prepare, List.append_nil] using he

theorem copyArity_eval (regs : Fin 8 → Bool) (modulus rank arity digits : Word) :
    Eval copyArity (7 * arity.length + 5)
      (state regs modulus rank arity digits [] [])
      (state (readRegs regs 0 1 none) modulus rank arity digits arity []) := by
  have he := SubexpScanPrimitives.copy_eval
    (state regs modulus rank arity digits [] [])
    (14 : Fin 17) 15 10 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  have hs : StackRoutines.copyStacks (14 : Fin 17) 15
      (store modulus rank arity digits [] []) = store modulus rank arity digits arity [] := by
    funext i
    by_cases h15 : i = 15
    · subst i
      simp [StackRoutines.copyStacks, store]
    · by_cases h14 : i = 14
      · subst i
        simp [StackRoutines.copyStacks, store]
      · simp [StackRoutines.copyStacks, store, h14, h15]
  have hsource : store modulus rank arity digits [] [] (14 : Fin 17) = arity := rfl
  simpa only [copyArity, SubexpScanPrimitives.afterCopy, state, hs, hsource] using he

private theorem embed_restricted {r s : ℕ} (register : Fin r → Fin 8)
    (stack : Fin s → Fin 17) (hr : Function.Injective register)
    (hs : Function.Injective stack) (d : Data) :
    embedState register stack d ⟨d.regs ∘ register, d.stacks ∘ stack⟩ = d := by
  apply embedState_eq_of_ports _ _ _ _ _ hr hs
  all_goals intros; rfl

private theorem frame_input (regs : Fin 8 → Bool) (modulus rank : Word)
    (k : ℕ) (digits : Word) :
    SubexpTaylorFrames.state (regs ∘ frameRegs)
      (SubexpTaylorFrames.data modulus k digits []) =
      ⟨(state regs modulus rank (List.replicate k true) digits (List.replicate k true) []).regs ∘ frameRegs,
        (state regs modulus rank (List.replicate k true) digits (List.replicate k true) []).stacks ∘ framePorts⟩ := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;> rfl

private theorem frame_output (regs : Fin 8 → Bool) (rf : Fin 5 → Bool)
    (modulus rank : Word) (k : ℕ) (digits output : Word) :
    embedState frameRegs framePorts
      (state regs modulus rank (List.replicate k true) digits (List.replicate k true) [])
      (SubexpTaylorFrames.state rf
        {SubexpTaylorFrames.data modulus 0 [] [] with output := output}) =
      state (Function.extend frameRegs rf regs) modulus rank (List.replicate k true) [] [] output := by
  apply embedState_eq_of_ports _ _ _ _ _ frameRegs.injective framePorts.injective
  · intro i
    exact frameRegs.injective.extend_apply rf regs i
  · intro i hi
    exact Function.extend_apply' _ _ _ hi
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h12 : i ≠ 12 := fun h => hi ⟨0, h.symm⟩
    have h15 : i ≠ 15 := fun h => hi ⟨3, h.symm⟩
    have h16 : i ≠ 16 := fun h => hi ⟨8, h.symm⟩
    simp [state, store, h12, h15, h16]

theorem chunks_flatten (B : ℕ) (words : List Word)
    (hw : ∀ w ∈ words, w.length = B) :
    SubexpTaylorFrames.chunks B words.length words.flatten = words := by
  induction words with
  | nil => rfl
  | cons w words ih =>
      have hlen := hw w (by simp)
      have ht := ih (fun v hv => hw v (by simp [hv]))
      change SubexpExponentProgram.padTake B (w ++ words.flatten) ::
        SubexpTaylorFrames.chunks B words.length ((w ++ words.flatten).drop B) = w :: words
      have htake : SubexpExponentProgram.padTake B (w ++ words.flatten) = w := by
        rw [← hlen]
        simp [SubexpExponentProgram.padTake]
      have hdrop : (w ++ words.flatten).drop B = words.flatten := by
        rw [← hlen]
        simp
      rw [htake, hdrop, ht]

theorem digitWords_width (modulus rank : Word) (k : ℕ) :
    ∀ w ∈ SubexpBasePUnranking.digitWords modulus k rank, w.length = modulus.length := by
  induction k generalizing rank with
  | zero => simp [SubexpBasePUnranking.digitWords]
  | succ k ih =>
      intro w hw
      simp only [SubexpBasePUnranking.digitWords, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact SubexpBasePUnranking.digit_length modulus rank
      · exact ih _ w hw

theorem frame_eval (regs : Fin 8 → Bool) (modulus rank : Word) (k : ℕ) :
    ∃ rf, Eval frame (k * (28 * modulus.length + 33) + 11)
      (state regs modulus rank (List.replicate k true)
        (SubexpBasePUnranking.digitWords modulus k rank).flatten (List.replicate k true) [])
      (state rf modulus rank (List.replicate k true) [] []
        (Encoding.encodeList id (SubexpBasePUnranking.digitWords modulus k rank))) := by
  let words := SubexpBasePUnranking.digitWords modulus k rank
  obtain ⟨rf, ht⟩ := SubexpTaylorFrames.program_trace modulus k words.flatten (regs ∘ frameRegs)
  have hdrop : words.flatten.drop (k * modulus.length) = [] := by
    apply List.drop_eq_nil_of_le
    exact le_of_eq (SubexpBasePUnranking.digitWords_flatten_length modulus rank k)
  have hchunks : SubexpTaylorFrames.chunks modulus.length k words.flatten = words := by
    simpa only [words, SubexpBasePUnranking.digitWords_length] using
      chunks_flatten modulus.length words (digitWords_width modulus rank k)
  rw [hdrop, hchunks] at ht
  have he := eval_call_lifted SubexpTaylorFrames.program frameRegs framePorts
    (state regs modulus rank (List.replicate k true) words.flatten (List.replicate k true) [])
    frameRegs.injective framePorts.injective ht
  refine ⟨Function.extend frameRegs rf regs, ?_⟩
  rw [frame_input, embed_restricted _ _ frameRegs.injective framePorts.injective,
    frame_output] at he
  exact he

def budget (modulus rank : Word) (k : ℕ) : ℕ :=
  SubexpFieldRowPreparation.budget modulus rank (List.replicate k true) + 1 +
    (7 * k + 5) + (k * (28 * modulus.length + 33) + 11) + 1

theorem program_runsIn (regs : Fin 8 → Bool) (modulus rank : Word) (k : ℕ) :
    ∃ rf, RunsIn program (budget modulus rank k)
      ((state regs modulus rank (List.replicate k true) [] [] []).withPC (some program.entry))
      ((state rf modulus rank (List.replicate k true) [] []
        (Encoding.encodeList id (SubexpBasePUnranking.digitWords modulus k rank))).withPC none) := by
  obtain ⟨np, hnp, rp, hp⟩ := prepare_eval regs modulus rank (List.replicate k true)
  simp only [List.length_replicate] at hp hnp
  have hc := copyArity_eval rp modulus rank (List.replicate k true)
    (SubexpBasePUnranking.digitWords modulus k rank).flatten
  simp only [List.length_replicate] at hc
  obtain ⟨rf, hf⟩ := frame_eval (readRegs rp 0 1 none) modulus rank k
  refine ⟨rf, np + ((7 * k + 5) + (k * (28 * modulus.length + 33) + 11)) + 1, ?_, ?_⟩
  · unfold budget
    omega
  · exact compiled_halt_trace (hp.seq (hc.seq hf)) 13 16

end SubexponentialSAT.SubexpFactorLabelProgram

end OAI.Algorithms
