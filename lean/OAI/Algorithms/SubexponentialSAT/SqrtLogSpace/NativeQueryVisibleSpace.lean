import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace

/-! Visible storage after the actual preparation excludes only the two
suspended collector words. Port332 has its own frontend bound and remains
byte-identical; the arbitrary collector length never enters this local cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryVisibleSpace

open BitProgram StructuredCalls SqrtLog LeafParametersProgram
open NativeQueryPreparation LeafProgram.Query CostAssembly.Polynomial

local notation "Hidden" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322 ∨
  Fin.val i = 770 ∨ Fin.val i = 771 ∨ Fin.val i = 781)

/-- The full frontend visible bound includes332 as well as every other lower
word except the two suspended collectors. -/
theorem project_visible (a : State 40 896) (A : ℕ)
    (ha : ∀ i, ¬ Hidden i → (a.stacks i).length ≤ A) :
    ∀ i : Fin 768, i ≠ 320 → i ≠ 322 →
      ((HighMarkedFrontend.project a).stacks i).length ≤ A := by
  intro i h320 h322
  apply ha (HighMarkedFrontend.stackMap i)
  change ¬ (i.val = 320 ∨ i.val = 322 ∨ i.val = 770 ∨ i.val = 771 ∨ i.val = 781)
  have hi := i.isLt
  have h320v : i.val ≠ 320 := fun h => h320 (Fin.ext h)
  have h322v : i.val ≠ 322 := fun h => h322 (Fin.ext h)
  omega

/-- The actual producer's read/write exclusion preserves332 at every prefix,
including all called routines and the final compiled halt. -/
theorem prefix332 (front out : Data) (steps : ℕ)
    (he : Eval command steps front out) :
    ∀ t z, t ≤ steps + 1 → Trace (compiled command 700 728) t
      (front.withPC (some (compiled command 700 728).entry)) z →
      z.stacks 332 = front.stacks 332 := by
  have hs := ProgramTapeReplay.eval_rebase LeafProgram.OuterCarried.hidden
    command_avoids he (fun _ => [])
  intro t z ht hz
  exact CommandStackTransport.eval_shadow_prefix_frame LeafProgram.OuterCarried.hidden
    command_avoids 700 728 hs ht hz 332 (by decide)

/-- The original semantic producer certificate also identifies this retained
word exactly, without replacing its actual output state. -/
theorem output332 (front packed out : Data) (p : PackingCallerProgram.Problem)
    (first : MulticolorTypes.Word p.r p.Q) (rest : List (MulticolorTypes.Word p.r p.Q))
    (hb : packed.stacks = (PackingCallerProgram.result front p first rest).stacks)
    {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)} {half : RingProgram.ScalarCode 3 (m.val 33)}
    {e : LeafRingSetupProgram.Data} (ho : ArithmeticOutput packed out m hd M cache half e) :
    out.stacks 332 = front.stacks 332 :=
  collector_frame front packed out p first rest hb ho 332 (by decide) (by decide)

/-- A source-only preparation time bound controls every visible prefix by
single-stack growth. The two arbitrary collector words remain outside it. -/
theorem prefix_visible (front out : Data) (steps S T : ℕ)
    (he : Eval command steps front out) (ht : steps ≤ T)
    (hv : ∀ i, ¬ LeafProgram.OuterCarried.hidden i → (front.stacks i).length ≤ S)
    (h332 : (front.stacks 332).length ≤ S) :
    ∀ t z, t ≤ steps + 1 → Trace (compiled command 700 728) t
      (front.withPC (some (compiled command 700 728).entry)) z →
      ∀ i : Fin 768, i ≠ 320 → i ≠ 322 → (z.stacks i).length ≤ S + T + 1 := by
  intro t z htime hz i h320 h322
  by_cases h : i = 332
  · subst i
    rw [prefix332 front out steps he t z htime hz]
    omega
  · have hi : ¬ LeafProgram.OuterCarried.hidden i := by
      simp only [LeafProgram.OuterCarried.hidden, List.mem_cons, List.not_mem_nil, or_false]
      exact not_or.mpr ⟨h320, not_or.mpr ⟨h322, h⟩⟩
    have hg := trace_selectedStackBits (compiled command 700 728) {i} hz
    have hg' : (z.stacks i).length ≤ (front.stacks i).length + t := by
      simpa only [selectedStackBits, Finset.sum_singleton] using hg
    have hb := hv i hi
    omega

/-- This compact output cap is independent of the arbitrary retained-frame
bound used in the separate maximum all-prefix space theorem. -/
theorem output_visible (front out : Data) (steps S T : ℕ)
    (he : Eval command steps front out) (ht : steps ≤ T)
    (hv : ∀ i, ¬ LeafProgram.OuterCarried.hidden i → (front.stacks i).length ≤ S)
    (h332 : (front.stacks 332).length ≤ S) :
    ∀ i : Fin 768, i ≠ 320 → i ≠ 322 → (out.stacks i).length ≤ S + T + 1 :=
  prefix_visible front out steps S T he ht hv h332 _ _ le_rfl
    (compiled_halt_trace he 700 728)

/-- A fixed ordinary polynomial absorbs the actual preparation time while
keeping all constants before the physical input and execution. -/
theorem visible_envelope_polynomial (C d : ℕ) :
    Ordinary (fun S => S + C * (S + 1) ^ d + 1) :=
  ordinary_add (ordinary_add ordinary_id (ordinary_mul (ordinary_const C)
    (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) d))) (ordinary_const 1)

theorem run_visible_polynomial (C d : ℕ) : ∃ A e : ℕ,
    ∀ (front out : Data) (steps S : ℕ), Eval command steps front out →
      steps ≤ C * (S + 1) ^ d →
      (∀ i, ¬ LeafProgram.OuterCarried.hidden i → (front.stacks i).length ≤ S) →
      (front.stacks 332).length ≤ S →
      (∀ i : Fin 768, i ≠ 320 → i ≠ 322 → (out.stacks i).length ≤ A * (S + 1) ^ e) ∧
      ∀ t z, t ≤ steps + 1 → Trace (compiled command 700 728) t
        (front.withPC (some (compiled command 700 728).entry)) z →
        ∀ i : Fin 768, i ≠ 320 → i ≠ 322 → (z.stacks i).length ≤ A * (S + 1) ^ e := by
  obtain ⟨A,e,hA⟩ := visible_envelope_polynomial C d
  refine ⟨A,e,?_⟩
  intro front out steps S he ht hv h332
  constructor
  · intro i h320 h322
    exact (output_visible front out steps S _ he ht hv h332 i h320 h322).trans (hA S)
  · intro t z htime hz i h320 h322
    exact (prefix_visible front out steps S _ he ht hv h332 t z htime hz i h320 h322).trans (hA S)

/-- The actual lower-call result preserves all upper caller words. Combining
its local cap with the visible upper cap excludes exactly the five suspended
words used by the complete query callback. -/
theorem lift_output_visible (a : State 40 896) (out : Data) (A B : ℕ)
    (hout : ∀ i : Fin 768, i ≠ 320 → i ≠ 322 → (out.stacks i).length ≤ A)
    (ha : ∀ i, ¬ Hidden i → (a.stacks i).length ≤ B) :
    ∀ i, ¬ Hidden i → ((HighMarkedFrontend.result a out).stacks i).length ≤ max A B := by
  intro i hi
  by_cases hl : i.val < 768
  · let j : Fin 768 := ⟨i.val, hl⟩
    have hij : i = HighMarkedFrontend.stackMap j := rfl
    rw [hij, HighMarkedFrontend.result_stack]
    apply (hout j _ _).trans (Nat.le_max_left _ _)
    · intro he
      have hv := congrArg Fin.val he
      exact hi (Or.inl hv)
    · intro he
      have hv := congrArg Fin.val he
      exact hi (Or.inr (Or.inl hv))
  · rw [HighMarkedFrontend.result_upper_frame a out i (by omega)]
    exact (ha i hi).trans (Nat.le_max_right _ _)


/-- The actual lower preparation call has the same source-only visible bound
in the complete leaf ABI, including both compiled halt steps. -/
theorem lift_run_visible (a : State 40 896) (out : Data) (steps S T : ℕ)
    (he : Eval command steps (HighMarkedFrontend.project a) out) (ht : steps ≤ T)
    (ha : ∀ i, ¬ Hidden i → (a.stacks i).length ≤ S) :
    let call : Cmd 40 896 := .call (ProgramLinking.liftProgram (compiled command 700 728)
      id HighMarkedFrontend.stackMap)
    let result := HighMarkedFrontend.result a out
    Eval call (steps + 1) a result ∧
      (∀ i, ¬ Hidden i → (result.stacks i).length ≤ S + T + 2) ∧
      ∀ t z, t ≤ steps + 2 → Trace (compiled call 700 728) t
        (a.withPC (some (compiled call 700 728).entry)) z →
        ∀ i, ¬ Hidden i → (z.stacks i).length ≤ S + T + 2 := by
  dsimp only
  let call : Cmd 40 896 := .call (ProgramLinking.liftProgram (compiled command 700 728)
    id HighMarkedFrontend.stackMap)
  have hc : Eval call (steps + 1) a (HighMarkedFrontend.result a out) :=
    eval_call_from_state (compiled command 700 728) id HighMarkedFrontend.stackMap a
      Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace he 700 728)
  have hp : ∀ t z, t ≤ steps + 2 → Trace (compiled call 700 728) t
      (a.withPC (some (compiled call 700 728).entry)) z →
      ∀ i, ¬ Hidden i → (z.stacks i).length ≤ S + T + 2 := by
    intro t z htime hz i hi
    have hg := trace_selectedStackBits (compiled call 700 728) {i} hz
    have hg' : (z.stacks i).length ≤ (a.stacks i).length + t := by
      simpa only [selectedStackBits, Finset.sum_singleton] using hg
    have hb := ha i hi
    omega
  exact ⟨hc, hp _ _ le_rfl (compiled_halt_trace hc 700 728), hp⟩


/-- The actual canonical frontend padding converts the physical cubic
capacity bound into one fixed polynomial bound on every serialized word.
This does not infer word length from its numeric value. -/
theorem front_serialized_lengths_cubic : ∃ A e : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (base front : Data)
      (l : Fin 8 → ℕ) (w : Bank.Words) (T : ℕ),
      q.Valid → FrontState q k base front l w →
      LeafScopeInputBounds.capacity q k ≤ 106 * T ^ 3 →
      ∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)).len i ≤
        A * (T + 1) ^ e := by
  obtain ⟨C,d,hcanonical⟩ := front_serialized_lengths_polynomial
  have hp : Ordinary (fun T => C * (106 * T ^ 3 + 1) ^ d) :=
    ordinary_mul (ordinary_const C) (ordinary_pow
      (ordinary_add (ordinary_mul (ordinary_const 106) (ordinary_pow ordinary_id 3))
        (ordinary_const 1)) d)
  obtain ⟨A,e,hA⟩ := hp
  refine ⟨A,e,?_⟩
  intro q k base front l w T hv hf hcap i
  exact (hcanonical q k base front l w hv hf i).trans
    ((Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right hcap 1) d)).trans (hA T))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryVisibleSpace
