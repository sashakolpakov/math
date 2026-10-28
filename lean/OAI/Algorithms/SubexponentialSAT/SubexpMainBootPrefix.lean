import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupMainRuntime
import OAI.Algorithms.SubexponentialSAT.SubexpRawNormalization
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Exact frontend facts recovered from the same actual trace used by Main.
The uniqueness argument is in the proof only; the machine runs the frontend once. -/

namespace SubexponentialSAT.SubexpMainBootPrefix

open StructuredCalls SubexpMainProgram

variable {er es n : ℕ}

structure Facts (F : SAT.CNF (Fin n)) (a : MainState er es) : Prop where
  variableCount : BinaryArithmetic.toNat (a.stacks (persistent es 2)) = n
  scale : BinaryArithmetic.toNat (a.stacks (persistent es 4)) = SubexpPackingParameters.s n
  capacity : BinaryArithmetic.toNat (a.stacks (persistent es 5)) = SubexpPackingParameters.u n
  body : a.stacks (persistent es 0) = Encoding.encodeCNFBody F
  empty : ∀ i : Fin 32, 6 ≤ i.val → a.stacks (persistent es i) = []

theorem prefix_empty (input body nb sb ub : List Bool) (i : Fin 32) (hi : 6 ≤ i.val) :
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

theorem prefix_facts (F : SAT.CNF (Fin n)) (nb sb ub : List Bool)
    (hn : CounterPrograms.value nb = n)
    (hs : CounterPrograms.value sb = SubexpPackingParameters.s n)
    (hu : CounterPrograms.value ub = SubexpPackingParameters.u n) :
    Facts F (prefixData er es (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) nb sb ub) := by
  let a := prefixData er es (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) nb sb ub
  have hslot := SubexpRawNormalization.prefix_slot er es
    (Encoding.encodeCNF F) (Encoding.encodeCNFBody F) nb sb ub
  have h2 : a.stacks (persistent es 2) = nb := hslot 2
  have h4 : a.stacks (persistent es 4) = sb := hslot 4
  have h5 : a.stacks (persistent es 5) = ub := hslot 5
  have h0 : a.stacks (persistent es 0) = Encoding.encodeCNFBody F := hslot 0
  refine ⟨?_, ?_, ?_, h0, fun i hi => prefix_empty _ _ _ _ _ i hi⟩
  · rw [h2]
    simpa only [CounterPrograms.value_eq_toNat] using hn
  · rw [h4]
    simpa only [CounterPrograms.value_eq_toNat] using hs
  · rw [h5]
    simpa only [CounterPrograms.value_eq_toNat] using hu

/-- The numerical word and framing facts hold for any actual execution of
the fixed frontend on this input, including the runtime theorem's execution. -/
theorem facts_of_execution (F : SAT.CNF (Fin n)) {steps : ℕ} {a : MainState er es}
    (he : Eval (frontendProcedure er es).invoke steps
      (initialData er es (Encoding.encodeCNF F)) a) : Facts F a := by
  obtain ⟨nb, sb, ub, t, hn, hs, hu, _, ht⟩ := prefix_execution er es F
  have ha := Eval.final_unique (persistent es 0) he ht
  rw [ha]
  exact prefix_facts F nb sb ub hn hs hu

end SubexponentialSAT.SubexpMainBootPrefix

end OAI.Algorithms
