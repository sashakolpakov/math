import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramCode
import OAI.Algorithms.SubexponentialSAT.CounterWidth

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

private theorem low3_injective : Function.Injective low3 := Fin.castAdd_injective _ _

def counterPorts (src : Fin 64) (hs : src≠41) : CounterForPrograms.Ports 16 64 :=
  ⟨⟨low3,low3_injective⟩,src,41,hs⟩

noncomputable def incremented (d : Data) (src : Fin 64) (hs : src≠41) : Data :=
  CounterForPrograms.install (counterPorts src hs) d false false (d.regs 2)
    (CounterPrograms.ripple true (d.stacks src)) []

theorem increment_eval (d : Data) (src : Fin 64) (hs : src≠41)
    (ht : d.stacks 41=[]) :
    Eval (increment src) (CounterPrograms.rippleCost true (d.stacks src)+1)
      d (incremented d src hs) := by
  let p := counterPorts src hs
  have he := eval_call_lifted (CounterPrograms.rippleProgram true)
    p.register (CounterForPrograms.stackPorts p) d p.register.injective
    (CounterForPrograms.stackPorts p).injective
    (CounterForPrograms.ripple_local_trace true (d.regs 0) (d.regs 1) (d.regs 2) (d.stacks src))
  have hm : (CounterForPrograms.stackPorts p : Fin 2 → Fin 64)=incrementStacks src := by
    funext i; fin_cases i <;> rfl
  change Eval _ _ (CounterForPrograms.install p d (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks src) []) (incremented d src hs) at he
  have hself : CounterForPrograms.install p d (d.regs 0) (d.regs 1) (d.regs 2)
      (d.stacks src) []=d := by
    have hh := CounterForPrograms.install_self p d
    simpa [p,counterPorts,low3,ht] using hh
  rw [hself] at he
  rw [hm] at he
  simpa [increment, p, counterPorts] using he

theorem incremented_stacks (d : Data) (src : Fin 64) (hs : src≠41)
    (ht : d.stacks 41=[]) :
    (incremented d src hs).stacks=
      Function.update d.stacks src (CounterPrograms.ripple true (d.stacks src)) := by
  funext i
  let b := CounterForPrograms.localData false false (d.regs 2)
    (CounterPrograms.ripple true (d.stacks src)) []
  unfold incremented CounterForPrograms.install
  by_cases hi : i=src
  · subst i
    have he := embedState_stack (counterPorts src hs).register
      (CounterForPrograms.stackPorts (counterPorts src hs)) d b
      (CounterForPrograms.stackPorts (counterPorts src hs)).injective 0
    simpa [b,counterPorts,CounterForPrograms.localData,CounterPrograms.counterStacks] using he
  · by_cases h41 : i=41
    · subst i
      have he := embedState_stack (counterPorts src hs).register
        (CounterForPrograms.stackPorts (counterPorts src hs)) d b
        (CounterForPrograms.stackPorts (counterPorts src hs)).injective 1
      simpa [b,counterPorts,CounterForPrograms.localData,CounterPrograms.counterStacks,hi,ht] using he
    · have hn : ¬∃ j, CounterForPrograms.stackPorts (counterPorts src hs) j=i := by
        rintro ⟨j,hj⟩
        fin_cases j
        · apply hi; simpa [counterPorts] using hj.symm
        · apply h41; simpa [counterPorts] using hj.symm
      have he := embedState_stack_frame (counterPorts src hs).register
        (CounterForPrograms.stackPorts (counterPorts src hs)) d b i hn
      simpa [hi] using he

theorem incremented_register (d : Data) (src : Fin 64) (hs : src≠41)
    (i : Fin 16) (hi : 3 ≤ i.val) : (incremented d src hs).regs i=d.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hjlt : (low3 j).val < 3 := by simp [low3]
  rw [show (counterPorts src hs).register j = low3 j by rfl] at hj
  rw [hj] at hjlt
  exact (Nat.not_lt_of_ge hi) hjlt

theorem ripple_length_ge (xs : List Bool) : xs.length ≤ (CounterPrograms.ripple true xs).length := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp [CounterPrograms.ripple] at * ; omega

theorem increment_vertex_width (xs : List Bool) (r : ℕ) (hl : xs.length=r)
    (hv : CounterPrograms.value xs+1 < 2^r) : (CounterPrograms.ripple true xs).length=r := by
  exact Nat.le_antisymm (CounterPrograms.increment_length_le_of_lt xs r hl.le hv)
    (hl ▸ ripple_length_ge xs)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
