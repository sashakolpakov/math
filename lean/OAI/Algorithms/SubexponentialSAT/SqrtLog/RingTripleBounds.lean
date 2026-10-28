import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTripleBridge

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram
open SubexponentialSAT.SubexpQuarticRing

theorem expandBudget_le (B d : ℕ) :
    expandBudget B d ≤ 300 * (d + 1)^3 * (B + 1) := by
  unfold expandBudget
  ring_nf
  omega

theorem tableEncoding_length {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B) :
    (tableEncoding table).length = d^3 * B := by
  have hlen (i j k : Fin d) : (table i j k).val.length = B := (table i j k).property
  simp [tableEncoding, List.length_flatten, List.map_ofFn,
 Function.comp_def, hlen]
  ring

theorem blocks_length {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) :
    (blocks table x y).length = d := by simp [blocks]

theorem blocks_inner_length {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) (b : List (RingScan.WordTriple B))
    (hb : b ∈ blocks table x y) : b.length = d * d := by
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hb
  exact RingProgram.coordinateTriples_length table x y k

/-- The same fixed expander has a primitive-machine execution. Its overhead
is a constant of the instruction table, independent of B and d. -/
theorem expansion_primitive {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) (degree width : List Bool)
    (regs : Fin 2 → Bool) (hd : degree.length = d) (hw : width.length = B) :
    ∃ regs', Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (300 * (d + 1)^3 * (B + 1) + 1))
      (primitiveCfg program
        ((state regs {(layout (RingProgram.flat x) (RingProgram.flat y) degree width) with table := tableEncoding table}).withPC
          (some program.entry)))
      (primitiveCfg program
        ((state regs' {(layout (RingProgram.flat x) (RingProgram.flat y) degree width) with xs := RingScan.blockBits (blocks table x y)}).withPC none)) := by
  obtain ⟨regs', hr⟩ := expansion_native table x y degree width regs hd hw
  refine ⟨regs', ?_⟩
  have hp := BitProgram.primitive_execution _ hr
  exact hp.mono (Nat.mul_le_mul_left _ (Nat.add_le_add_right (expandBudget_le B d) 1))

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
