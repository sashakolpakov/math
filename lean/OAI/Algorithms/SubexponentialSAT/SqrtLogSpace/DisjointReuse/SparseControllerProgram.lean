import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

/-! Concrete control composition for fixed finite bit commands. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.Controller

open BitProgram StructuredCalls

/-- A real finite while command composes actual local body executions. The
premises must be supplied by the concrete search, child, and leaf routines. -/
theorem while_execution {R S : ℕ} (flag : Fin R) (body : Cmd R S)
    (store : ℕ → StructuredProgram.State R S) (visits budget : ℕ)
    (hflag : ∀ i ≤ visits, (store i).regs flag = decide (i < visits))
    (hbody : ∀ i < visits, ∃ t ≤ budget, Eval body t (store i) (store (i + 1))) :
    ∃ t ≤ visits * (budget + 1) + 1,
      Eval (.while flag body) t (store 0) (store visits) := by
  induction visits generalizing store with
  | zero =>
    have hz : (store 0).regs flag = false := by simpa using hflag 0 (by omega)
    exact ⟨1, by simp, .while_false hz⟩
  | succ visits ih =>
    obtain ⟨t₀, ht₀, he₀⟩ := hbody 0 (by omega)
    have hnextFlag : ∀ i ≤ visits,
        (store (i + 1)).regs flag = decide (i < visits) := by
      intro i hi
      simpa only [Nat.add_lt_add_iff_right] using hflag (i + 1) (by omega)
    have hnextBody : ∀ i < visits, ∃ t ≤ budget,
        Eval body t (store (i + 1)) (store (i + 1 + 1)) := by
      intro i hi
      exact hbody (i + 1) (by omega)
    obtain ⟨t, ht, he⟩ := ih (fun i => store (i + 1)) hnextFlag hnextBody
    have hz : (store 0).regs flag = true := by simpa using hflag 0 (by omega)
    refine ⟨t₀ + t + 1, ?_, .while_true hz he₀ he⟩
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- A fixed while table retains one uniform all-prefix stack bound across
every visit. Each premise is a measured execution of the concrete body. -/
theorem while_execution_space {R S : ℕ} (flag : Fin R) (body : Cmd R S)
    (inputStack outputStack : Fin S) (store : ℕ → StructuredProgram.State R S)
    (visits budget bound : ℕ)
    (hflag : ∀ i ≤ visits, (store i).regs flag = decide (i < visits))
    (hfinal : ∀ stack, ((store visits).stacks stack).length ≤ bound)
    (hbody : ∀ i < visits, ∃ t ≤ budget,
      Eval body t (store i) (store (i + 1)) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ t →
        Trace (compiled body inputStack outputStack) prefixSteps
          ((store i).withPC (some (compiled body inputStack outputStack).entry)) intermediate →
        ∀ stack, (intermediate.stacks stack).length ≤ bound) :
    ∃ t ≤ visits * (budget + 1) + 1,
      Eval (.while flag body) t (store 0) (store visits) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ t →
        Trace (compiled (.while flag body) inputStack outputStack) prefixSteps
          ((store 0).withPC (some (compiled (.while flag body) inputStack outputStack).entry))
          intermediate → ∀ stack, (intermediate.stacks stack).length ≤ bound := by
  induction visits generalizing store with
  | zero =>
    have hz : (store 0).regs flag = false := by simpa using hflag 0 (by omega)
    have he : Eval (.while flag body) 1 (store 0) (store 0) := .while_false hz
    refine ⟨1, by simp, he, ?_⟩
    intro prefixSteps intermediate hp hc
    by_cases hp0 : prefixSteps = 0
    · subst prefixSteps
      cases hc
      exact hfinal
    · have hp1 : prefixSteps = 1 := by omega
      subst prefixSteps
      rw [trace_same_length_unique hc (compiled_trace he inputStack outputStack)]
      exact hfinal
  | succ visits ih =>
    obtain ⟨t₀, ht₀, he₀, hb₀⟩ := hbody 0 (by omega)
    have hnextFlag : ∀ i ≤ visits,
        (store (i + 1)).regs flag = decide (i < visits) := by
      intro i hi
      simpa only [Nat.add_lt_add_iff_right] using hflag (i + 1) (by omega)
    have hnextBody : ∀ i < visits, ∃ t ≤ budget,
        Eval body t (store (i + 1)) (store (i + 1 + 1)) ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ t →
          Trace (compiled body inputStack outputStack) prefixSteps
            ((store (i + 1)).withPC (some (compiled body inputStack outputStack).entry)) intermediate →
          ∀ stack, (intermediate.stacks stack).length ≤ bound := by
      intro i hi
      exact hbody (i + 1) (by omega)
    obtain ⟨t, ht, he, hb⟩ := ih (fun i => store (i + 1)) hnextFlag hfinal hnextBody
    have hz : (store 0).regs flag = true := by simpa using hflag 0 (by omega)
    refine ⟨t₀ + t + 1, ?_, .while_true hz he₀ he, ?_⟩
    · simp only [Nat.add_mul, Nat.one_mul]
      omega
    · exact StructuredSpace.while_true_stack_bound hz he₀ he inputStack outputStack hb₀ hb
        (compiled (.while flag body) inputStack outputStack)
        (siteAddress (.while flag body)) (exitAddress (.while flag body))
        (compiled_site (.while flag body) inputStack outputStack)

/-- The list is part of finite control, chosen with `k`, not an input table. -/
def firstHit {R S : ℕ} (flag : Fin R) : List (Cmd R S) → Cmd R S
  | [] => .base .skip
  | command :: rest => .ite flag (.base .skip) (.seq command (firstHit flag rest))

/-- Only actually executed phases occur as `next` constructors. A `stop`
retains the unvisited command suffix and performs no callback invocation. -/
inductive Visits {R S : ℕ} (flag : Fin R) :
    List (Cmd R S) → State R S → State R S → ℕ → Prop
  | nil (d : State R S) : Visits flag [] d d 0
  | stop (command : Cmd R S) (rest : List (Cmd R S)) (d : State R S)
      (hfound : d.regs flag = true) : Visits flag (command :: rest) d d 1
  | next {command rest d e final steps tailSteps}
      (hmissing : d.regs flag = false) (heval : Eval command steps d e)
      (tail : Visits flag rest e final tailSteps) :
      Visits flag (command :: rest) d final (steps + tailSteps + 1)

theorem Visits.eval {R S : ℕ} {flag : Fin R} {commands : List (Cmd R S)}
    {d final : State R S} {steps : ℕ} (h : Visits flag commands d final steps) :
    Eval (firstHit flag commands) steps d final := by
  induction h with
  | nil d => exact .base (.skip d)
  | stop command rest d hfound => exact .ite_true hfound (.base (.skip d))
  | next hmissing heval tail ih => exact .ite_false hmissing (heval.seq ih)

theorem Visits.initial_false {R S : ℕ} {flag : Fin R} {commands : List (Cmd R S)}
    {d final : State R S} {steps : ℕ} (h : Visits flag commands d final steps)
    (hfinal : final.regs flag = false) : d.regs flag = false := by
  cases h with
  | nil => exact hfinal
  | stop command rest d hfound => simp_all
  | next hmissing heval tail => exact hmissing

/-- If the final flag is false, each phase was actually run, and each phase
output was false. This exposes all unsuccessful searches to completeness proofs. -/
inductive FailedStages {R S : ℕ} (flag : Fin R) :
    List (Cmd R S) → State R S → State R S → Prop
  | nil (d : State R S) (hmissing : d.regs flag = false) : FailedStages flag [] d d
  | next {command rest d e final steps}
      (hmissing : d.regs flag = false) (heval : Eval command steps d e)
      (hfailed : e.regs flag = false) (tail : FailedStages flag rest e final) :
      FailedStages flag (command :: rest) d final

theorem Visits.failedStages {R S : ℕ} {flag : Fin R} {commands : List (Cmd R S)}
    {d final : State R S} {steps : ℕ} (h : Visits flag commands d final steps)
    (hfinal : final.regs flag = false) : FailedStages flag commands d final := by
  induction h with
  | nil d => exact .nil d hfinal
  | stop command rest d hfound => simp_all
  | next hmissing heval tail ih =>
    exact .next hmissing heval (tail.initial_false hfinal) (ih hfinal)

/-- Fixed-code phases compose with their measured local budgets. This is an
intermediate theorem: the actual phase programs must discharge `hphase`. -/
theorem firstHit_execution {R S : ℕ} (flag : Fin R) (commands : List (Cmd R S))
    (invariant : State R S → Prop) (budget : ℕ) (d : State R S) (hd : invariant d)
    (hphase : ∀ command ∈ commands, ∀ a, invariant a → a.regs flag = false →
      ∃ steps ≤ budget, ∃ b, Eval command steps a b ∧ invariant b) :
    ∃ steps ≤ (budget + 1) * commands.length, ∃ final,
      invariant final ∧ Visits flag commands d final steps := by
  induction commands generalizing d with
  | nil => exact ⟨0, by simp, d, hd, .nil d⟩
  | cons command rest ih =>
    cases hf : d.regs flag with
    | true =>
      refine ⟨1, ?_, d, hd, .stop command rest d hf⟩
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    | false =>
      obtain ⟨steps, hs, e, he, hI⟩ := hphase command (by simp) d hd hf
      have hrest : ∀ command ∈ rest, ∀ a, invariant a → a.regs flag = false →
          ∃ steps ≤ budget, ∃ b, Eval command steps a b ∧ invariant b := by
        intro cmd hcmd a ha hf
        exact hphase cmd (List.mem_cons_of_mem _ hcmd) a ha hf
      obtain ⟨tailSteps, ht, final, hfinal, htail⟩ := ih e hI hrest
      refine ⟨steps + tailSteps + 1, ?_, final, hfinal, .next hf he htail⟩
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega


theorem firstHit_execution_space {R S : ℕ} (flag : Fin R) (commands : List (Cmd R S))
    (inputStack outputStack : Fin S) (invariant : State R S → Prop) (budget bound : ℕ)
    (hboundary : ∀ a, invariant a → ∀ stack, (a.stacks stack).length ≤ bound)
    (d : State R S) (hd : invariant d)
    (hphase : ∀ command ∈ commands, ∀ a, invariant a → a.regs flag = false →
      ∃ steps ≤ budget, ∃ b, Eval command steps a b ∧ invariant b ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ steps →
          Trace (compiled command inputStack outputStack) prefixSteps
            (a.withPC (some (compiled command inputStack outputStack).entry)) intermediate →
          ∀ stack, (intermediate.stacks stack).length ≤ bound) :
    ∃ steps ≤ (budget + 1) * commands.length, ∃ final,
      invariant final ∧ Visits flag commands d final steps ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (compiled (firstHit flag commands) inputStack outputStack) prefixSteps
          (d.withPC (some (compiled (firstHit flag commands) inputStack outputStack).entry))
          intermediate → ∀ stack, (intermediate.stacks stack).length ≤ bound := by
  induction commands generalizing d with
  | nil =>
    refine ⟨0, by simp, d, hd, .nil d, ?_⟩
    intro prefixSteps intermediate hp hc
    have hz : prefixSteps = 0 := by omega
    subst prefixSteps
    cases hc
    exact hboundary d hd
  | cons command rest ih =>
    cases hf : d.regs flag with
    | true =>
      refine ⟨1, ?_, d, hd, .stop command rest d hf, ?_⟩
      · simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega
      · have hskip : Eval (.base (.skip : StructuredProgram.Cmd R S)) 0 d d :=
          .base (.skip d)
        apply StructuredSpace.conditional_true_stack_bound hf hskip inputStack outputStack
          (caller := compiled (firstHit flag (command :: rest)) inputStack outputStack)
          (embed := siteAddress (firstHit flag (command :: rest)))
          (exit := exitAddress (firstHit flag (command :: rest)))
        · intro prefixSteps intermediate hp hc
          have hz : prefixSteps = 0 := by omega
          subst prefixSteps
          cases hc
          exact hboundary d hd
        · exact compiled_site _ inputStack outputStack
    | false =>
      obtain ⟨steps, hs, e, he, hI, hspace⟩ := hphase command (by simp) d hd hf
      have hrest : ∀ command ∈ rest, ∀ a, invariant a → a.regs flag = false →
          ∃ steps ≤ budget, ∃ b, Eval command steps a b ∧ invariant b ∧
            ∀ prefixSteps intermediate, prefixSteps ≤ steps →
              Trace (compiled command inputStack outputStack) prefixSteps
                (a.withPC (some (compiled command inputStack outputStack).entry)) intermediate →
              ∀ stack, (intermediate.stacks stack).length ≤ bound := by
        intro cmd hcmd a ha hf
        exact hphase cmd (List.mem_cons_of_mem _ hcmd) a ha hf
      obtain ⟨tailSteps, ht, final, hfinal, htail, htailSpace⟩ := ih e hI hrest
      refine ⟨steps + tailSteps + 1, ?_, final, hfinal, .next hf he htail, ?_⟩
      · simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega
      · have hseq := he.seq htail.eval
        apply StructuredSpace.conditional_false_stack_bound hf hseq inputStack outputStack
          (caller := compiled (firstHit flag (command :: rest)) inputStack outputStack)
          (embed := siteAddress (firstHit flag (command :: rest)))
          (exit := exitAddress (firstHit flag (command :: rest)))
        · exact StructuredSpace.sequence_stack_bound he htail.eval inputStack outputStack
            hspace htailSpace
            (compiled (.seq command (firstHit flag rest)) inputStack outputStack)
            (siteAddress (.seq command (firstHit flag rest)))
            (exitAddress (.seq command (firstHit flag rest)))
            (compiled_site _ inputStack outputStack)
        · exact compiled_site _ inputStack outputStack


theorem Visits.final_eq_of_true {R S : ℕ} {flag : Fin R} {commands : List (Cmd R S)}
    {d final : State R S} {steps : ℕ} (h : Visits flag commands d final steps)
    (hd : d.regs flag = true) : final = d := by
  cases h with
  | nil => rfl
  | stop => rfl
  | next hmissing heval tail => simp_all

/-- A successful search exposes its first successful concrete phase, all actual
failed earlier phases, and the untouched command suffix. -/
theorem Visits.first_success {R S : ℕ} {flag : Fin R} {commands : List (Cmd R S)}
    {d final : State R S} {steps : ℕ} (h : Visits flag commands d final steps)
    (hd : d.regs flag = false) (hf : final.regs flag = true) :
    ∃ (before : List (Cmd R S)) (winner : Cmd R S) (after : List (Cmd R S))
      (a : State R S) (time : ℕ),
      commands = before ++ winner :: after ∧ FailedStages flag before d a ∧
      a.regs flag = false ∧ Eval winner time a final := by
  induction h with
  | nil d => simp_all
  | stop command rest d hfound => simp_all
  | @next command rest d e final time tailSteps hmissing heval tail ih =>
    cases heflag : e.regs flag with
    | true =>
      have hfinal := tail.final_eq_of_true heflag
      subst final
      exact ⟨[], command, rest, d, time, rfl, .nil d hd, hd, heval⟩
    | false =>
      obtain ⟨before, winner, after, a, t, hsplit, hfailed, ha, hwin⟩ := ih heflag hf
      refine ⟨command :: before, winner, after, a, t, ?_,
        .next hmissing heval heflag hfailed, ha, hwin⟩
      simp only [List.cons_append, hsplit]

theorem FailedStages.mem_execution {R S : ℕ} {flag : Fin R} {commands : List (Cmd R S)}
    {d final : State R S} (h : FailedStages flag commands d final)
    {command : Cmd R S} (hm : command ∈ commands) :
    ∃ (a b : State R S) (time : ℕ),
      a.regs flag = false ∧ Eval command time a b ∧ b.regs flag = false := by
  induction h with
  | nil d hd => simp at hm
  | @next head rest d e final time hmissing heval hfailed tail ih =>
    rcases List.mem_cons.mp hm with heq | hrest
    · subst command
      exact ⟨d, e, time, hmissing, heval, hfailed⟩
    · exact ih hrest


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.Controller
