import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan

namespace OAI.Algorithms

/-! The concrete extractor on canonical one-hot type encodings. -/

namespace SubexponentialSAT.Subexp.MatrixInputTypes

open BitProgram StructuredCalls MulticolorTypes ReadPlan MatrixInputProgram

variable {r Q Δ : ℕ}

def slotRows (u : UniversalType r Q Δ) : List (List Bool) :=
  List.ofFn (fun j => encodeWord (u.slot j))

def before (i : Fin Δ) (u : UniversalType r Q Δ) : List (List Bool) :=
  (slotRows u).take i.val

def after (i : Fin Δ) (u : UniversalType r Q Δ) : List (List Bool) :=
  (slotRows u).drop (i.val + 1)

theorem before_length (i : Fin Δ) (u : UniversalType r Q Δ) :
    (before i u).length = i.val := by
  simp [before, slotRows ]

theorem before_width (i : Fin Δ) (u : UniversalType r Q Δ) :
    ∀ row ∈ before i u, row.length = Q * r := by
  intro row hrow
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hrow)
  simp [wordWidth]

theorem slotRows_split (i : Fin Δ) (u : UniversalType r Q Δ) :
    slotRows u = before i u ++ encodeWord (u.slot i) :: after i u := by
  have hi : i.val < (slotRows u).length := by simp [slotRows]
  have h := List.take_append_drop i.val (slotRows u)
  rw [List.drop_eq_getElem_cons hi] at h
  simpa [before, after, slotRows] using h.symm

theorem encodeType_head_slots (u : UniversalType r Q Δ) :
    CollisionProgram.encodeType u = encodeWord u.head ++ (slotRows u).flatten := by
  rw [encodeType_eq_words, List.ofFn_succ]
  simp [slotRows]

theorem encoded_array (i : Fin Δ) (u : UniversalType r Q Δ) :
    array (encodeWord u.head) (encodeWord (u.slot i)) (before i u) (after i u) =
      CollisionProgram.encodeType u := by
  rw [encodeType_head_slots, slotRows_split i u]
  simp [array, List.append_assoc]

def normalizedType (common : Word r Q) (i : Fin Δ) (u : UniversalType r Q Δ) :
    UniversalType r Q Δ := ⟨common, Function.update u.slot i common⟩

theorem slotRows_normalizedType (common : Word r Q) (i : Fin Δ)
    (u : UniversalType r Q Δ) :
    slotRows (normalizedType common i u) = (slotRows u).set i.val (encodeWord common) := by
  apply List.ext_getElem
  · simp [slotRows]
  · intro j hj hk
    simp only [slotRows, List.getElem_ofFn, List.getElem_set]
    by_cases hij : i.val = j
    · have he : (⟨j, by simpa [slotRows] using hj⟩ : Fin Δ) = i := Fin.ext hij.symm
      simp [normalizedType, hij, he]
    · have he : (⟨j, by simpa [slotRows] using hj⟩ : Fin Δ) ≠ i := by
        intro he; exact hij (congrArg Fin.val he).symm
      simp [normalizedType, hij, he]

theorem normalizedType_encoding (common : Word r Q) (i : Fin Δ)
    (u : UniversalType r Q Δ) :
    CollisionProgram.encodeType (normalizedType common i u) =
      normalizedBits (encodeWord common) (before i u) (after i u) := by
  rw [encodeType_head_slots, slotRows_normalizedType, List.set_eq_take_append_cons_drop]
  have hi : i.val < (slotRows u).length := by simp [slotRows]
  simp [hi, normalizedType, normalizedBits, before, after, List.append_assoc]

theorem normalizedType_eq_iff (common : Word r Q) (i : Fin Δ)
    (u y : UniversalType r Q Δ) :
    normalizedType common i u = normalizedType common i y ↔
      ∀ j, j ≠ i → ∀ l, u.slot j l = y.slot j l := by
  constructor
  · intro h j hj l
    have hs := congrArg (fun z : UniversalType r Q Δ => z.slot j l) h
    simpa [normalizedType, hj] using hs
  · intro h
    apply UniversalType.ext
    · rfl
    · funext j l
      by_cases hj : j = i
      · subst j; simp [normalizedType]
      · simpa [normalizedType, hj] using h j hj l

theorem normalizedBits_eq_iff (common : Word r Q) (i : Fin Δ)
    (u y : UniversalType r Q Δ) :
    normalizedBits (encodeWord common) (before i u) (after i u) =
      normalizedBits (encodeWord common) (before i y) (after i y) ↔
      ∀ j, j ≠ i → ∀ l, u.slot j l = y.slot j l := by
  rw [← normalizedType_encoding, ← normalizedType_encoding,
    CollisionProgram.encodeType_eq_iff, normalizedType_eq_iff]

def input (i : Fin Δ) (u y : UniversalType r Q Δ) (regs : Fin 8 → Bool) :
    MatrixInputAccess.Data :=
  inputState (CollisionProgram.encodeType u) (CollisionProgram.encodeType y)
    (List.replicate (i.val + 1) true) (List.replicate (Q * r) true)
    (List.replicate r true) (List.replicate Q true) regs

def output (i : Fin Δ) (u y : UniversalType r Q Δ) (regs : Fin 8 → Bool) :
    MatrixInputAccess.Data :=
  outputState (CollisionProgram.encodeType u) (CollisionProgram.encodeType y)
    (List.replicate (i.val + 1) true) (List.replicate (Q * r) true)
    (List.replicate r true) (List.replicate Q true)
    (encodeWord u.head) (encodeWord (u.slot i))
    (encodeWord y.head) (encodeWord (y.slot i))
    (decide (∀ j, j ≠ i → ∀ l, u.slot j l = y.slot j l)) regs

/-- Actual type bytes are read and normalized by the fixed extractor; the
spectator bit is produced by the actual equality machine. -/
theorem program_runsIn (i : Fin Δ) (u y : UniversalType r Q Δ) (regs : Fin 8 → Bool) :
    RunsIn MatrixInputProgram.program
      (36 * CollisionProgram.typeWidth r Q Δ +
        4 * (i.val + 1) * (14 * (Q * r) + 17) + 203 * (Q * r) + 265)
      ((input i u y regs).withPC (some MatrixInputProgram.program.entry))
      ((output i u y regs).withPC none) := by
  have h := MatrixInputProgram.program_runsIn
    (encodeWord u.head) (encodeWord (u.slot i))
    (encodeWord y.head) (encodeWord (y.slot i))
    (List.replicate (i.val + 1) true) (List.replicate (Q * r) true)
    (List.replicate r true) (List.replicate Q true)
    (before i u) (after i u) (before i y) (after i y) regs
    (by simp [before_length]) (by simp [before_length])
    (by simp [wordWidth]) (by simp [wordWidth])
    (by simp [wordWidth]) (by simp [wordWidth])
    (by simpa using before_width i u) (by simpa using before_width i y)
  have hcost : cost (CollisionProgram.encodeType u) (CollisionProgram.encodeType y)
      (List.replicate (i.val + 1) true) (List.replicate (Q * r) true) =
      36 * CollisionProgram.typeWidth r Q Δ +
        4 * (i.val + 1) * (14 * (Q * r) + 17) + 203 * (Q * r) + 265 := by
    simp only [cost, CollisionProgram.encodeType_length, List.length_replicate]
    ring
  simpa only [encoded_array, normalizedBits_eq_iff, hcost, input, output] using h

theorem program_primitive_runsIn (i : Fin Δ) (u y : UniversalType r Q Δ)
    (regs : Fin 8 → Bool) :
    Computation.RunsIn (BitProgram.primitive MatrixInputProgram.program).step
      (BitProgram.primitiveOverhead MatrixInputProgram.program *
        (36 * CollisionProgram.typeWidth r Q Δ +
          4 * (i.val + 1) * (14 * (Q * r) + 17) + 203 * (Q * r) + 265))
      (BitProgram.primitiveCfg MatrixInputProgram.program
        ((input i u y regs).withPC (some MatrixInputProgram.program.entry)))
      (BitProgram.primitiveCfg MatrixInputProgram.program ((output i u y regs).withPC none)) :=
  BitProgram.primitive_execution _ (program_runsIn i u y regs)

end SubexponentialSAT.Subexp.MatrixInputTypes

end OAI.Algorithms
