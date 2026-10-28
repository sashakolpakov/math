import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingTupleBounds
import OAI.Algorithms.SubexponentialSAT.SubexpTupleRefinement
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationPayload

namespace OAI.Algorithms

/-!
# Fixed-control enumeration of the code-construction search spaces

The very same 83-label bit program enumerates all dimensions. Dimension is a
unary input stack, not the size of a generated instruction table. The output
is the actual framed list in the order produced by that program. Theorems
below charge the complete list, including candidates subsequently rejected.
Preparing the input dimension and fixed alphabet, and checking candidates,
are separate stages: this module does not pretend they are free.
-/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.TupleProgram SubexponentialSAT.SubexpTupleRefinement
open SubexponentialSAT.SubexpEnumerationPayload

def fieldAlphabet (p : ℕ) [Fact p.Prime] : List (List Bool) :=
  (QuarticSearch.elements p).map (scalarCode p).block

def fieldCandidates (p d : ℕ) [Fact p.Prime] : List (List Bool) :=
  powerRows (fieldAlphabet p) d [[]]

@[simp] theorem fieldAlphabet_length (p : ℕ) [Fact p.Prime] :
    (fieldAlphabet p).length = p := by
  simp [fieldAlphabet, QuarticSearch.elements]

theorem fieldAlphabet_width (p : ℕ) [Fact p.Prime] :
    ∀ word ∈ fieldAlphabet p, word.length = scalarWidth p := by
  intro word hword
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hword
  exact scalarBits_length x

@[simp] theorem fieldCandidates_length (p d : ℕ) [Fact p.Prime] :
    (fieldCandidates p d).length = p ^ d := by
  simp [fieldCandidates, generated_count]

theorem fieldCandidates_complete (p d : ℕ) [Fact p.Prime]
    (v : Fin d → ZMod p) :
    encodeTuple (scalarCode p) v ∈ fieldCandidates p d := by
  exact encodeTuple_mem_powerRows (scalarCode p) (QuarticSearch.elements p)
    (QuarticSearch.mem_elements p) d v

theorem fieldCandidates_sound (p d : ℕ) [Fact p.Prime] (bits : List Bool) :
    bits ∈ fieldCandidates p d ↔
      ∃ v : Fin d → ZMod p, encodeTuple (scalarCode p) v = bits := by
  constructor
  · intro h
    obtain ⟨v, _, hv⟩ := (mem_powerRows_encoded (scalarCode p)
      (QuarticSearch.elements p) d bits).mp h
    exact ⟨v, hv⟩
  · rintro ⟨v, rfl⟩
    exact fieldCandidates_complete p d v

theorem fieldCandidates_nodup (p d : ℕ) [Fact p.Prime] :
    (fieldCandidates p d).Nodup :=
  powerRows_encoded_nodup (scalarCode p) (QuarticSearch.elements p)
    (SubexpVectorEnumeration.elements_nodup p) d

theorem fieldCandidates_width (p d : ℕ) [Fact p.Prime]
    (bits : List Bool) (hbits : bits ∈ fieldCandidates p d) :
    bits.length = d * scalarWidth p := by
  obtain ⟨v, rfl⟩ := (fieldCandidates_sound p d bits).mp hbits
  simp [encodeTuple, scalarCode]

def flattenMatrix {p rows cols : ℕ}
    (M : Fin rows → Fin cols → ZMod p) : Fin (rows * cols) → ZMod p :=
  fun i => M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

def expandMatrix {p rows cols : ℕ}
    (v : Fin (rows * cols) → ZMod p) : Fin rows → Fin cols → ZMod p :=
  fun i j => v (finProdFinEquiv (i, j))

@[simp] theorem expand_flatten {p rows cols : ℕ}
    (M : Fin rows → Fin cols → ZMod p) :
    expandMatrix (flattenMatrix M) = M := by
  funext i j
  simp [expandMatrix, flattenMatrix]

@[simp] theorem flatten_expand {p rows cols : ℕ}
    (v : Fin (rows * cols) → ZMod p) :
    flattenMatrix (expandMatrix (rows := rows) (cols := cols) v) = v := by
  funext i
  change v (finProdFinEquiv (finProdFinEquiv.symm i)) = v i
  rw [Equiv.apply_symm_apply]

def encodeMatrix {p rows cols : ℕ} [Fact p.Prime]
    (M : Fin rows → Fin cols → ZMod p) : List Bool :=
  encodeTuple (scalarCode p) (flattenMatrix M)

theorem encodeMatrix_injective {p rows cols : ℕ} [Fact p.Prime] :
    Function.Injective (encodeMatrix (p := p) (rows := rows) (cols := cols)) := by
  intro M N h
  have hf := encodeTuple_injective (scalarCode p) (rows * cols) h
  simpa using congrArg (expandMatrix (rows := rows) (cols := cols)) hf

theorem encodedMatrix_mem {p rows cols : ℕ} [Fact p.Prime]
    (M : Fin rows → Fin cols → ZMod p) :
    encodeMatrix M ∈ fieldCandidates p (rows * cols) :=
  fieldCandidates_complete p (rows * cols) (flattenMatrix M)

def enumerationCost (p d : ℕ) : ℕ :=
  800 * (d + 1) * (p ^ d + 1) * ((d + 1) * scalarWidth p + 1) + 9

theorem enumerationCost_bound (p d : ℕ) [Fact p.Prime] :
    powerCost (fieldAlphabet p) d [[]] + 9 ≤ enumerationCost p d := by
  have h := Subexp.PackingTupleBounds.generated_powerCost_le
    (fieldAlphabet p) d (scalarWidth p)
    (fun word hw => (fieldAlphabet_width p word hw).le)
  simpa [enumerationCost] using Nat.add_le_add_right h 9

/-- The instruction table is fixed, independent of all numerical parameters. -/
abbrev enumerationProgram := generateProgram

theorem enumerationProgram_size : size generateCmd + 1 = 83 :=
  generate_control_size

/-- All input arrays are explicit. The scalar alphabet is the fixed two- or
three-element array at the applications; the unary dimension is input data. -/
def enumerationInput (p d : ℕ) [Fact p.Prime] : State 10 9 :=
  ⟨fun _ => false, fun i =>
    if i = 1 then ProgramEncoding.encodeRecords (fieldAlphabet p)
    else if i = 8 then List.replicate d false else []⟩

theorem enumeration_runsIn (p d : ℕ) [Fact p.Prime] :
    ∃ next : State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords (fieldCandidates p d) ∧
      next.stacks 8 = [] ∧
      RunsIn enumerationProgram (enumerationCost p d)
        ((enumerationInput p d).withPC (some enumerationProgram.entry))
        (next.withPC none) := by
  have hi : outerInvariant (fieldAlphabet p) (List.replicate d false) false
      (enumerationInput p d) := by simp [outerInvariant, enumerationInput]
  obtain ⟨next, hnext, k, hk, he⟩ := generateProgram_runsIn (fieldAlphabet p)
    (List.replicate d false) false (enumerationInput p d) hi
    (by simp [enumerationInput]) (by simp [enumerationInput])
    (by simp [enumerationInput])
  refine ⟨next, ?_, hnext.1.2.2.2.2.2.1, k, ?_, he⟩
  · simpa [fieldCandidates] using hnext.2.1
  · exact hk.trans (by simpa using enumerationCost_bound p d)

theorem enumeration_primitive (p d : ℕ) [Fact p.Prime] :
    ∃ next : State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords (fieldCandidates p d) ∧
      next.stacks 8 = [] ∧
      Computation.RunsIn (primitive enumerationProgram).step
        (primitiveOverhead enumerationProgram * enumerationCost p d)
        (primitiveCfg enumerationProgram
          ((enumerationInput p d).withPC (some enumerationProgram.entry)))
        (primitiveCfg enumerationProgram (next.withPC none)) := by
  obtain ⟨next, hout, hdepth, hrun⟩ := enumeration_runsIn p d
  exact ⟨next, hout, hdepth, primitive_execution enumerationProgram hrun⟩

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
