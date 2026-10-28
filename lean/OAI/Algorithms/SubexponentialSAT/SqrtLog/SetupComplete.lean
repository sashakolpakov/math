import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupScheduleBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupBankBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Complete

open BitProgram StructuredCalls SubexpSetupProgram SubexpSetupStorage

def command (c : Config) : SetupCmd c := .seq (Schedule.command c) (Banks.command c)
def program (c : Config) := compiled (command c) (persistent c 0) (persistent c 0)

structure Values (c : Config) (n : ℕ) (b : SetupState c) : Prop where
  L : BinaryArithmetic.toNat (b.stacks (persistent c 30)) = Asymptotic.L n
  w : BinaryArithmetic.toNat (b.stacks (persistent c 31)) = Asymptotic.w n
  s : BinaryArithmetic.toNat (b.stacks (persistent c 4)) = Asymptotic.s n
  banks : Banks.Values c (Asymptotic.s n) b

/-- Unconditional exact setup from the retained binary n word; the old s word
and all initially dirty arithmetic storage are replaced by physical programs. -/
theorem command_eval (c : Config) (a : SetupState c) :
    ∃ t b, Eval (command c) t a b ∧
      Values c (BinaryArithmetic.toNat (a.stacks (persistent c 2))) b ∧
      (∀ i : Fin 32, i ≠ 4 → i ≠ 23 → i ≠ 24 → i ≠ 30 → i ≠ 31 →
        b.stacks (persistent c i) = a.stacks (persistent c i)) := by
  obtain ⟨ts,mid,hs,hL,hw,hS,hfS⟩ := Schedule.command_eval c a
  obtain ⟨tb,b,hb,hV,hfB⟩ := Banks.scheduled_eval c
    (BinaryArithmetic.toNat (a.stacks (persistent c 2))) mid hS
  refine ⟨ts+tb,b,hs.seq hb,?_,?_⟩
  · exact ⟨by rw [hfB 30 (by decide) (by decide)]; exact hL,
      by rw [hfB 31 (by decide) (by decide)]; exact hw,
      by rw [hfB 4 (by decide) (by decide)]; exact hS,hV⟩
  · intro i h4 h23 h24 h30 h31
    exact (hfB i h23 h24).trans (hfS i h4 h30 h31)

theorem polynomial_envelope (c : Config) : PolynomialEnvelope (command c) :=
  (Schedule.polynomial_envelope c).seq (Banks.polynomial_envelope c)

theorem bounded_eval (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ B (a : SetupState c), WordBound B a →
      ∃ t b, Eval (command c) t a b ∧ t ≤ C*(B+1)^q ∧ WordBound (C*(B+1)^q) b ∧
        Values c (BinaryArithmetic.toNat (a.stacks (persistent c 2))) b ∧
        (∀ i : Fin 32, i ≠ 4 → i ≠ 23 → i ≠ 24 → i ≠ 30 → i ≠ 31 →
          b.stacks (persistent c i) = a.stacks (persistent c i)) := by
  obtain ⟨C,q,hC,hq,hbound⟩ := polynomial_envelope c
  refine ⟨C,q,hC,hq,?_⟩
  intro B a ha
  obtain ⟨t,b,he,hv,hf⟩ := command_eval c a
  obtain ⟨ht,hb⟩ := hbound B a t b ha he
  exact ⟨t,b,he,ht,hb,hv,hf⟩

/-- One actual Procedure for the controller's setup phase. All port maps are
those already used by the original setup-to-sparsifier boundary. -/
def procedure (c : Config) (er : ℕ) :
    SubexpMainProgram.Procedure er (mainExtraStacks c) where
  registers := 16
  stackCount := stackCount c
  labels := size (command c) + 1
  program := program c
  register := (mainProcedure c er).register
  stack := (mainProcedure c er).stack

theorem procedure_eval (c : Config) (er : ℕ)
    (a : SubexpMainProgram.MainState er (mainExtraStacks c)) :
    ∃ t out, Eval (procedure c er).invoke t a ((procedure c er).install a out) ∧
      Values c (BinaryArithmetic.toNat
        (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 2))) out ∧
      (∀ i : Fin 32, i ≠ 4 → i ≠ 23 → i ≠ 24 → i ≠ 30 → i ≠ 31 →
        ((procedure c er).install a out).stacks
          (SubexpMainProgram.persistent (mainExtraStacks c) i) =
        a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) i)) := by
  let localState := (procedure c er).project a
  obtain ⟨t,out,he,hv,hf⟩ := command_eval c localState
  have hn : localState.stacks (persistent c 2) =
      a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 2) := by
    change a.stacks (mainStack c (persistent c 2)) = _
    rw [mainStack_persistent]
  refine ⟨t+1,out,(procedure c er).invoke_trace a out (compiled_halt_trace he _ _),?_,?_⟩
  · simpa only [hn] using hv
  · intro i h4 h23 h24 h30 h31
    rw [← mainStack_persistent c i]
    have hout := embedState_stack (procedure c er).registerMap (procedure c er).stack a out
      (procedure c er).stack.injective (persistent c i)
    change ((procedure c er).install a out).stacks (mainStack c (persistent c i)) = _ at hout
    rw [hout,hf i h4 h23 h24 h30 h31]
    rfl

end SubexponentialSAT.SqrtLog.Setup.Complete

namespace SubexponentialSAT.SqrtLog.Setup.Complete

open BitProgram StructuredCalls SubexpSetupProgram SubexpSetupStorage

/-- Caller-level paid execution. The only size hypothesis is on actual stored
words; there is no precomputed schedule, bank, or clean-workspace premise. -/
theorem procedure_bounded_eval (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ er B
      (a : SubexpMainProgram.MainState er (mainExtraStacks c)), WordBound B a →
      ∃ t out, Eval (procedure c er).invoke t a ((procedure c er).install a out) ∧
        t ≤ C*(B+1)^q ∧ WordBound (C*(B+1)^q) out ∧
        Values c (BinaryArithmetic.toNat
          (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 2))) out ∧
        (∀ i : Fin 32, i ≠ 4 → i ≠ 23 → i ≠ 24 → i ≠ 30 → i ≠ 31 →
          ((procedure c er).install a out).stacks
            (SubexpMainProgram.persistent (mainExtraStacks c) i) =
          a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) i)) := by
  obtain ⟨C,q,hC,hq,hbound⟩ := bounded_eval c
  refine ⟨C+1,q,by omega,hq,?_⟩
  intro er B a ha
  let localState := (procedure c er).project a
  have hlocal : WordBound B localState := fun i => ha ((procedure c er).stack i)
  obtain ⟨t,out,he,ht,hout,hv,hf⟩ := hbound B localState hlocal
  have hpow : 1 ≤ (B+1)^q := Nat.one_le_pow _ _ (by omega)
  have hn : localState.stacks (persistent c 2) =
      a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 2) := by
    change a.stacks (mainStack c (persistent c 2)) = _
    rw [mainStack_persistent]
  refine ⟨t+1,out,(procedure c er).invoke_trace a out (compiled_halt_trace he _ _),?_,?_,?_,?_⟩
  · nlinarith
  · intro i; exact (hout i).trans (Nat.mul_le_mul_right _ (by omega))
  · simpa only [hn] using hv
  · intro i h4 h23 h24 h30 h31
    rw [← mainStack_persistent c i]
    have hh := embedState_stack (procedure c er).registerMap (procedure c er).stack a out
      (procedure c er).stack.injective (persistent c i)
    change ((procedure c er).install a out).stacks (mainStack c (persistent c i)) = _ at hh
    rw [hh,hf i h4 h23 h24 h30 h31]
    rfl

theorem install_eq_banks (c : Config) (er : ℕ)
    (a : SubexpMainProgram.MainState er (mainExtraStacks c)) (out : SetupState c) :
    (procedure c er).install a out = (Banks.procedure c er).install a out := by
  simp only [SubexpMainProgram.Procedure.install,
    SubexpMainProgram.Procedure.registerMap, procedure, Banks.procedure]
  rfl

end SubexponentialSAT.SqrtLog.Setup.Complete

namespace SubexponentialSAT.SqrtLog.Setup.Complete

open BitProgram StructuredCalls SubexpSetupProgram

/-- The postcondition applies to every actual run, not only the constructed
witness used to establish totality. -/
theorem values_of_eval (c : Config) {a b : SetupState c} {t : ℕ}
    (he : Eval (command c) t a b) :
    Values c (BinaryArithmetic.toNat (a.stacks (persistent c 2))) b ∧
      (∀ i : Fin 32, i ≠ 4 → i ≠ 23 → i ≠ 24 → i ≠ 30 → i ≠ 31 →
        b.stacks (persistent c i) = a.stacks (persistent c i)) := by
  obtain ⟨u,out,hu,hv,hf⟩ := command_eval c a
  have hb := SubexpPrimeProgram.eval_result_unique he hu (persistent c 0) (persistent c 0)
  simpa only [hb] using And.intro hv hf

end SubexponentialSAT.SqrtLog.Setup.Complete

end OAI.Algorithms
