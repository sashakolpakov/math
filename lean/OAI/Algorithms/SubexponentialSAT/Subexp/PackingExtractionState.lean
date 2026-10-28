import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketSelect

namespace OAI.Algorithms

/-! Fixed physical ports for block-major extraction and its bucket reader. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

abbrev Data := StructuredProgram.State 8 19

structure Context where
  keys : List Bool
  payload : List Bool
  block : List Bool
  address : List Bool
  storage : List Bool
  metadata : List Bool
  addresses : List Bool
  buckets : List Bool
  remaining : List Bool

def state (regs : Fin 8 → Bool) (c : Context)
    (source key count vertex scratch temp workA workB : List Bool) : Data :=
  ⟨regs, ![source, key, count, vertex, scratch, [], [], c.keys, c.payload, temp,
    c.block, c.address, c.storage, c.metadata, c.addresses, c.buckets, c.remaining,
    workA, workB]⟩

def ready (regs : Fin 8 → Bool) (c : Context) : Data := state regs c [] [] [] [] [] [] [] []

def selectPorts (i : Fin 5) : Fin 19 := Fin.castAdd 14 i

theorem selectPorts_injective : Function.Injective selectPorts := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 19 => z.val) h)

abbrev selectCall : Cmd 8 19 :=
  .call (ProgramLinking.liftProgram PackingBucketSelect.program id selectPorts)

private theorem embed_select (regs localRegs : Fin 8 → Bool) (c : Context)
    (source key count vertex scratch temp workA workB : List Bool)
    (source' key' count' vertex' scratch' : List Bool) :
    embedState id selectPorts (state regs c source key count vertex scratch temp workA workB)
      (PackingBucketSelect.state localRegs source' key' count' vertex' scratch') =
    state localRegs c source' key' count' vertex' scratch' temp workA workB := by
  apply SelectorMapProgram.embed_eq _ _ Function.injective_id selectPorts_injective
  · intro i; rfl
  · intro i
    fin_cases i <;> simp [state, PackingBucketSelect.state, selectPorts]
  · intro j hj
    exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    fin_cases j <;> simp_all [selectPorts, state]
    all_goals
      first | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
        exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl) |
        exact False.elim (hj 4 rfl)

theorem selectCall_eval (key vertex : List Bool) (pre rest : List (List Bool))
    (regs : Fin 8 → Bool) (c : Context) :
    ∃ n ≤ 21 * ((Encoding.frame key ++ words (pre ++ vertex :: rest)).length + 1),
      ∃ rf, Eval selectCall n
        (state regs c (Encoding.frame key ++ words (pre ++ vertex :: rest)) []
          (List.replicate pre.length true) [] [] [] [] [])
        (state rf c [] key [] vertex [] [] [] []) := by
  obtain ⟨n, hn, rf, ht⟩ := PackingBucketSelect.program_trace key vertex pre rest regs
  have he := eval_call_lifted PackingBucketSelect.program id selectPorts
    (state regs c (Encoding.frame key ++ words (pre ++ vertex :: rest)) []
      (List.replicate pre.length true) [] [] [] [] [])
    Function.injective_id selectPorts_injective ht
  rw [embed_select, embed_select] at he
  exact ⟨n, hn, rf, he⟩

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
