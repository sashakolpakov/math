import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowAssemblyPrepared
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowTableContext

namespace OAI.Algorithms

/-! Input data shared by every physical row call. The three per-incidence
metadata words are established by the actual lookup and prefix-slot program.
All other premises below identify stored parameters or empty work stacks. -/

namespace SubexponentialSAT.SubexpGlobalRowInputs

open BitProgram StructuredCalls SubexpDenseRowTableProgram
  SubexpDenseRowTableAssembly SubexpDenseRowTableContext
  SubexpGlobalRowLookup SubexpGlobalRowSelection
open Subexp.UniversalRowWorkspace (port)

variable (p r Q : ℕ) [Fact p.Prime]
variable (xs : List (ZMod p)) (inverse negative : Fin Q → Word)
  (difference : Fin Q → Fin Q → Word)

structure Masters (a : Data) : Prop where
  empty : ∀ j : Fin 49, a.stacks (port j) = []
  code : a.stacks 26 = []
  positions : a.stacks 253 = List.replicate Q true
  colors : a.stacks 252 = List.replicate r true
  degree : a.stacks 243 = List.replicate (xs.length + 1) true
  width : (a.stacks 129).length = Subexp.MatrixWordEncoding.width p
  zero : a.stacks 131 = List.replicate (4 * Subexp.MatrixWordEncoding.width p) false
  constantWidth : (a.stacks 133).length = Subexp.MatrixWordEncoding.width p
  constantValue : BinaryArithmetic.toNat (a.stacks 133) = p - 1
  modulus : a.stacks 128 = Subexp.MatrixWordEncoding.modulus p
  coefficients : a.stacks 254 =
    Subexp.MatrixProgramSupport.words (xs.map (Subexp.MatrixWordEncoding.word p))
  inverseArray : a.stacks 135 = (List.ofFn inverse).flatten
  negativeArray : a.stacks 136 = (List.ofFn negative).flatten
  differenceArray : a.stacks 137 =
    (List.ofFn (fun j => (List.ofFn (difference j)).flatten)).flatten
  nodeArrayWidth : (a.stacks 134).length = Q * (4 * Subexp.MatrixWordEncoding.width p)
  inverseWidth : ∀ j, (inverse j).length = 4 * Subexp.MatrixWordEncoding.width p
  negativeWidth : ∀ j, (negative j).length = 4 * Subexp.MatrixWordEncoding.width p
  differenceWidth : ∀ j k, (difference j k).length = 4 * Subexp.MatrixWordEncoding.width p

private theorem port_ne_output (j : Fin 49) : port j ≠ 87 := by
  intro heq
  have hv := congrArg (fun i : Fin 288 => i.val) heq
  change (port j).val = 87 at hv
  rw [Subexp.UniversalRowWorkspace.port_val] at hv
  split_ifs at hv <;> omega

omit [Fact p.Prime] in
/-- Parser tails, coordinate counters, and previous row accumulators do
not alter any shared arithmetic or source-construction input. -/
theorem Masters.of_sameContext {a b : Data}
    (h : Masters p r Q xs inverse negative difference a)
    (hab : SameContext a.stacks b.stacks) :
    Masters p r Q xs inverse negative difference b := by
  have same (j : Fin 288) (hj : j.val < 256) (h87 : j ≠ 87) :
      b.stacks j = a.stacks j := sameContext_low hab j hj h87
  constructor
  · intro j
    rw [same (port j) (lt_trans (Subexp.UniversalRowWorkspace.port_lt_cache j) (by decide))
      (port_ne_output j)]
    exact h.empty j
  · rw [same 26 (by decide) (by decide)]; exact h.code
  · rw [same 253 (by decide) (by decide)]; exact h.positions
  · rw [same 252 (by decide) (by decide)]; exact h.colors
  · rw [same 243 (by decide) (by decide)]; exact h.degree
  · rw [same 129 (by decide) (by decide)]; exact h.width
  · rw [same 131 (by decide) (by decide)]; exact h.zero
  · rw [same 133 (by decide) (by decide)]; exact h.constantWidth
  · rw [same 133 (by decide) (by decide)]; exact h.constantValue
  · rw [same 128 (by decide) (by decide)]; exact h.modulus
  · rw [same 254 (by decide) (by decide)]; exact h.coefficients
  · rw [same 135 (by decide) (by decide)]; exact h.inverseArray
  · rw [same 136 (by decide) (by decide)]; exact h.negativeArray
  · rw [same 137 (by decide) (by decide)]; exact h.differenceArray
  · rw [same 134 (by decide) (by decide)]; exact h.nodeArrayWidth
  · exact h.inverseWidth
  · exact h.negativeWidth
  · exact h.differenceWidth

omit [Fact p.Prime] in
/-- The classified types and physical one-based prefix slot discharge
exactly the per-row fields of the source producer's stored-input contract. -/
theorem Masters.prepared {Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) {a b : Data}
    (h : Masters p r Q xs inverse negative difference a)
    (hframe : ∀ j : Fin 288, j ∉ cleanupPorts → b.stacks j = a.stacks j)
    (hleft : b.stacks 272 = Subexp.CollisionProgram.encodeType u)
    (hright : b.stacks 275 = Subexp.CollisionProgram.encodeType y)
    (hslot : b.stacks 284 = List.replicate (i.val + 1) true) :
    Subexp.UniversalRowAssembly.PreparedInput p i u y xs inverse negative difference
      (projectState (Fin.castAdd 9) id b) := by
  have same (j : Fin 288) (hj : j.val < 270) : b.stacks j = a.stacks j := by
    apply hframe
    intro hm
    have := cleanup_mem_high j hm
    omega
  constructor
  · intro j
    change b.stacks (port j) = []
    rw [same (port j) (lt_trans (Subexp.UniversalRowWorkspace.port_lt_cache j) (by decide))]
    exact h.empty j
  · change b.stacks 26 = []
    rw [same 26 (by decide)]; exact h.code
  · change b.stacks 253 = _
    rw [same 253 (by decide)]; exact h.positions
  · change b.stacks 252 = _
    rw [same 252 (by decide)]; exact h.colors
  · change b.stacks 243 = _
    rw [same 243 (by decide)]; exact h.degree
  · change (b.stacks 129).length = _
    rw [same 129 (by decide)]; exact h.width
  · change b.stacks 131 = _
    rw [same 131 (by decide)]; exact h.zero
  · change (b.stacks 133).length = _
    rw [same 133 (by decide)]; exact h.constantWidth
  · change BinaryArithmetic.toNat (b.stacks 133) = _
    rw [same 133 (by decide)]; exact h.constantValue
  · exact hleft
  · exact hright
  · exact hslot
  · change b.stacks 128 = _
    rw [same 128 (by decide)]; exact h.modulus
  · change b.stacks 254 = _
    rw [same 254 (by decide)]; exact h.coefficients
  · change b.stacks 135 = _
    rw [same 135 (by decide)]; exact h.inverseArray
  · change b.stacks 136 = _
    rw [same 136 (by decide)]; exact h.negativeArray
  · change b.stacks 137 = _
    rw [same 137 (by decide)]; exact h.differenceArray
  · change (b.stacks 134).length = _
    rw [same 134 (by decide)]; exact h.nodeArrayWidth
  · exact h.inverseWidth
  · exact h.negativeWidth
  · exact h.differenceWidth

end SubexponentialSAT.SubexpGlobalRowInputs

end OAI.Algorithms
