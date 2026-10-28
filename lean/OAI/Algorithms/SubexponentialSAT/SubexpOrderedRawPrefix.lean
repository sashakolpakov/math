import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupMainRuntime
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyEncoding
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# The existing frontend on ordered dense-variable clause lists

Only the theorem's input domain changes. The program is the same physical
`frontendProcedure`; it parses the unary variable-count header and preserves
the supplied clause order, literal order, duplicates, and empty clauses.
The actual normalizer runs later. No canonical finite-set serialization is
required here.
-/

namespace SubexponentialSAT.SubexpOrderedRawPrefix

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpSetupStorage Filter

abbrev Formula (n : ℕ) := ExecCNF.Formula (SAT.Literal (Fin n))

def body {n : ℕ} (G : Formula n) : List Bool :=
  Encoding.encodeList (Encoding.encodeList id) (ExecSparsifyEncoding.words G)

def encode {n : ℕ} (G : Formula n) : List Bool :=
  Encoding.encodeNat n ++ body G

def bitLength {n : ℕ} (G : Formula n) : ℕ := (encode G).length

theorem encode_eq {n : ℕ} (G : Formula n) :
    encode G = Encoding.encodeNat n ++
      Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
        (G.map (List.map Encoding.literalCode)) :=
  congrArg (fun body => Encoding.encodeNat n ++ body)
    (ExecSparsifyEncoding.words_encoding G)

theorem numVariables_le_bitLength {n : ℕ} (G : Formula n) : n ≤ bitLength G := by
  simp only [bitLength, encode, List.length_append, Encoding.length_encodeNat]
  omega

structure Facts {n : ℕ} (G : Formula n) {er es : ℕ} (a : MainState er es) : Prop where
  variableCount : BinaryArithmetic.toNat (a.stacks (persistent es 2)) = n
  scale : BinaryArithmetic.toNat (a.stacks (persistent es 4)) = SubexpPackingParameters.s n
  capacity : BinaryArithmetic.toNat (a.stacks (persistent es 5)) = SubexpPackingParameters.u n
  body : a.stacks (persistent es 0) = body G
  empty : ∀ i : Fin 32, 6 ≤ i.val → a.stacks (persistent es i) = []

theorem prefix_word (er es : ℕ) (input body nb sb ub : List Bool) (i : Fin 6) :
    (prefixData er es input body nb sb ub).stacks (persistent es (i.castAdd 26)) =
      (SubexpFrontendPrefix.state body nb sb ub).stacks i :=
  embedState_stack _ _ _ _ (frontendProcedure er es).stack.injective i

theorem prefix_empty (er es : ℕ) (input body nb sb ub : List Bool)
    (i : Fin 32) (hi : 6 ≤ i.val) :
    (prefixData er es input body nb sb ub).stacks (persistent es i) = [] := by
  have hframe : (prefixData er es input body nb sb ub).stacks (persistent es i) =
      (initialData er es input).stacks (persistent es i) := by
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have he : j.castAdd 26 = i := (persistent_injective es) hj
    have hv := congrArg Fin.val he
    have hjlt : j.val < 6 := j.isLt
    simp only [Fin.val_castAdd] at hv
    omega
  rw [hframe]
  have hz : i ≠ 0 := by intro h; subst i; simp at hi
  simp [initialData, StructuredProgram.ioState, hz]

theorem prefix_facts (er es : ℕ) {n : ℕ} (G : Formula n) (nb sb ub : List Bool)
    (hn : CounterPrograms.value nb = n)
    (hs : CounterPrograms.value sb = SubexpPackingParameters.s n)
    (hu : CounterPrograms.value ub = SubexpPackingParameters.u n) :
    Facts G (prefixData er es (encode G) (body G) nb sb ub) := by
  have h2 : (prefixData er es (encode G) (body G) nb sb ub).stacks (persistent es 2) = nb :=
    prefix_word er es (encode G) (body G) nb sb ub 2
  have h4 : (prefixData er es (encode G) (body G) nb sb ub).stacks (persistent es 4) = sb :=
    prefix_word er es (encode G) (body G) nb sb ub 4
  have h5 : (prefixData er es (encode G) (body G) nb sb ub).stacks (persistent es 5) = ub :=
    prefix_word er es (encode G) (body G) nb sb ub 5
  have h0 : (prefixData er es (encode G) (body G) nb sb ub).stacks (persistent es 0) = body G :=
    prefix_word er es (encode G) (body G) nb sb ub 0
  refine ⟨?_, ?_, ?_, h0, fun i hi => prefix_empty er es _ _ _ _ _ i hi⟩
  · rw [h2]
    simpa only [CounterPrograms.value_eq_toNat] using hn
  · rw [h4]
    simpa only [CounterPrograms.value_eq_toNat] using hs
  · rw [h5]
    simpa only [CounterPrograms.value_eq_toNat] using hu

/-- The same finite frontend starts from the ordered-list bytes. -/
theorem prefix_execution (er es : ℕ) {n : ℕ} (G : Formula n) :
    ∃ (nb sb ub : List Bool) (steps : ℕ),
      CounterPrograms.value nb = n ∧
      CounterPrograms.value sb = SubexpPackingParameters.s n ∧
      CounterPrograms.value ub = SubexpPackingParameters.u n ∧
      steps ≤ SubexpFrontendPrefix.bound (bitLength G) ∧
      Eval (frontendProcedure er es).invoke steps (initialData er es (encode G))
        (prefixData er es (encode G) (body G) nb sb ub) := by
  obtain ⟨nb, sb, ub, hn, hs, hu, _, _, _, steps, hsteps, ht⟩ :=
    SubexpFrontendPrefix.run_raw n (body G)
  refine ⟨nb, sb, ub, steps, hn, hs, hu,
    hsteps.trans (SubexpFrontendPrefix.bound_mono (numVariables_le_bitLength G)), ?_⟩
  apply Procedure.invoke_trace
  change Trace SubexpFrontendPrefix.program steps
    (((frontendProcedure er es).project (initialData er es (encode G))).withPC
      (some SubexpFrontendPrefix.program.entry)) _
  rw [prefix_project_initial]
  change Trace SubexpFrontendPrefix.program steps
    ((StructuredProgram.ioState 0 (Encoding.encodeNat n ++ body G)).withPC
      (some SubexpFrontendPrefix.program.entry)) _
  have hio : SubexpFrontendPrefix.state (Encoding.encodeNat n ++ body G) [] [] [] =
      StructuredProgram.ioState 0 (Encoding.encodeNat n ++ body G) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> rfl
  rw [← hio]
  rw [SubexpFrontendPrefix.program_initial]
  exact ht

/-- Determinism transfers the facts to the exact trace used by the caller. -/
theorem facts_of_execution {er es n : ℕ} (G : Formula n) {steps : ℕ}
    {a : MainState er es}
    (he : Eval (frontendProcedure er es).invoke steps (initialData er es (encode G)) a) :
    Facts G a := by
  obtain ⟨nb, sb, ub, t, hn, hs, hu, _, ht⟩ := prefix_execution er es G
  have ha := Eval.final_unique (persistent es 0) he ht
  rw [ha]
  exact prefix_facts er es G nb sb ub hn hs hu

theorem Facts.known {c : Config} {er n : ℕ} {G : Formula n}
    {a : MainState er (mainExtraStacks c)} (h : Facts G a) :
    Known c n initialKnown ((mainProcedure c er).project a) := by
  apply initialKnown_of_words c n _
  · rw [main_project_word]; exact h.variableCount
  · rw [main_project_word]; exact h.scale
  · rw [main_project_word]; exact h.capacity

/-- The numerical setup is polynomial in the actual ordered input length.
The constants and degree precede the varying count and clause list. -/
theorem eventually_setup_bounded (c : Config) (er : ℕ) :
    ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
      ∀ᶠ n : ℕ in atTop, ∀ G : Formula n,
        ∃ (prefixSteps setupSteps : ℕ) (before : MainState er (mainExtraStacks c))
          (out : SetupState c),
          prefixSteps ≤ SubexpFrontendPrefix.bound (bitLength G) ∧
          Eval (frontendProcedure er (mainExtraStacks c)).invoke prefixSteps
            (initialData er (mainExtraStacks c) (encode G)) before ∧
          Eval (mainProcedure c er).invoke setupSteps before
            ((mainProcedure c er).install before out) ∧
          prefixSteps + setupSteps ≤ C * (bitLength G + 1) ^ d ∧
          WordBound (C * (bitLength G + 1) ^ d) ((mainProcedure c er).install before out) ∧
          SubexpSetupMainRuntime.Postconditions c er n before out := by
  obtain ⟨C, d, hC, hd, hmain⟩ := SubexpSetupMainRuntime.eventually_main_bounded c er
  refine ⟨133 + C * 135 ^ d, 2 * d, by omega, by omega, ?_⟩
  filter_upwards [hmain] with n hmain
  intro G
  let L := bitLength G
  let M := L + SubexpFrontendPrefix.bound L
  obtain ⟨nb, sb, ub, tp, hn, hs, hu, hp, ep⟩ := prefix_execution er (mainExtraStacks c) G
  let before := prefixData er (mainExtraStacks c) (encode G) (body G) nb sb ub
  have hinit : WordBound L (initialData er (mainExtraStacks c) (encode G)) :=
    SubexpSetupMainRuntime.initial_wordBound er (mainExtraStacks c) (encode G)
  have hbefore : WordBound M before := SubexpSetupBoundSpec.wordBound_mono
    (SubexpSetupBoundSpec.eval_wordBound hinit ep) (Nat.add_le_add_left hp L)
  have hnL : n ≤ L := numVariables_le_bitLength G
  have hnM : n ≤ M := hnL.trans (by dsimp [M]; omega)
  have hknown : Known c n initialKnown ((mainProcedure c er).project before) :=
    (prefix_facts er (mainExtraStacks c) G nb sb ub hn hs hu).known
  obtain ⟨ts, out, es, htime, hword, hpost⟩ := hmain M before hnM hknown hbefore
  have hgrowth : M + 1 ≤ 135 * (L + 1) ^ 2 := SubexpSetupMainRuntime.prefix_growth_polynomial L
  have hsetup : C * (M + 1) ^ d ≤ C * 135 ^ d * (L + 1) ^ (2 * d) := by
    calc
      _ ≤ C * (135 * (L + 1) ^ 2) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgrowth d)
      _ = C * 135 ^ d * (L + 1) ^ (2 * d) := by
        rw [mul_pow, ← pow_mul]
        ring
  have hpow : (L + 1) ^ 2 ≤ (L + 1) ^ (2 * d) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hprefix : tp ≤ 133 * (L + 1) ^ (2 * d) :=
    hp.trans ((SubexpSetupMainRuntime.prefix_bound_polynomial L).trans (Nat.mul_le_mul_left _ hpow))
  have htotal : tp + ts ≤ (133 + C * 135 ^ d) * (L + 1) ^ (2 * d) := by
    calc
      tp + ts ≤ 133 * (L + 1) ^ (2 * d) + C * 135 ^ d * (L + 1) ^ (2 * d) :=
        Nat.add_le_add hprefix (htime.trans hsetup)
      _ = (133 + C * 135 ^ d) * (L + 1) ^ (2 * d) := by ring
  have hout : WordBound ((133 + C * 135 ^ d) * (L + 1) ^ (2 * d))
      ((mainProcedure c er).install before out) :=
    SubexpSetupBoundSpec.wordBound_mono hword
      (hsetup.trans (Nat.mul_le_mul_right _ (by omega)))
  exact ⟨tp, ts, before, out, hp, ep, es, htotal, hout, hpost⟩

end SubexponentialSAT.SubexpOrderedRawPrefix

end OAI.Algorithms
