import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposeProgram

namespace OAI.Algorithms

/-! Generating framed scalar entries directly avoids an uncharged recoding
step. The same fixed tuple machine concatenates scalar frames; the outer
list frame delimits candidates, while the inner frames delimit entries. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.TupleProgram SubexponentialSAT.SubexpTupleRefinement
open SubexponentialSAT.SubexpEnumerationPayload

def framedScalarCode (p : ℕ) [Fact p.Prime] : StackEncoding.BlockCode (ZMod p) :=
  Subexp.BasisTransposeProgram.framedCode (scalarCode p)

def framedAlphabet (p : ℕ) [Fact p.Prime] : List (List Bool) :=
  (QuarticSearch.elements p).map (framedScalarCode p).block

def framedCandidates (p d : ℕ) [Fact p.Prime] : List (List Bool) :=
  powerRows (framedAlphabet p) d [[]]

def framedVector {p d : ℕ} [Fact p.Prime] (v : Fin d → ZMod p) : List Bool :=
  encodeTuple (framedScalarCode p) v

def framedMatrix {p rows cols : ℕ} [Fact p.Prime]
    (M : Fin rows → Fin cols → ZMod p) : List Bool :=
  framedVector (flattenMatrix M)

@[simp] theorem framedAlphabet_length (p : ℕ) [Fact p.Prime] :
    (framedAlphabet p).length = p := by
  simp [framedAlphabet, QuarticSearch.elements]

@[simp] theorem framedCandidates_length (p d : ℕ) [Fact p.Prime] :
    (framedCandidates p d).length = p ^ d := by
  simp [framedCandidates, generated_count]

theorem framedCandidates_complete {p d : ℕ} [Fact p.Prime] (v : Fin d → ZMod p) :
    framedVector v ∈ framedCandidates p d :=
  encodeTuple_mem_powerRows (framedScalarCode p) (QuarticSearch.elements p)
    (QuarticSearch.mem_elements p) d v

theorem framedMatrix_mem {p rows cols : ℕ} [Fact p.Prime]
    (M : Fin rows → Fin cols → ZMod p) :
    framedMatrix M ∈ framedCandidates p (rows * cols) :=
  framedCandidates_complete (flattenMatrix M)

theorem framedCandidates_nodup (p d : ℕ) [Fact p.Prime] :
    (framedCandidates p d).Nodup :=
  powerRows_encoded_nodup (framedScalarCode p) (QuarticSearch.elements p)
    (SubexpVectorEnumeration.elements_nodup p) d

theorem framedCandidates_sound {p d : ℕ} [Fact p.Prime] (bits : List Bool) :
    bits ∈ framedCandidates p d ↔ ∃ v : Fin d → ZMod p, framedVector v = bits := by
  constructor
  · intro h
    obtain ⟨v, _, hv⟩ := (mem_powerRows_encoded (framedScalarCode p)
      (QuarticSearch.elements p) d bits).mp h
    exact ⟨v, hv⟩
  · rintro ⟨v, rfl⟩
    exact framedCandidates_complete v

def framedEnumerationCost (p d : ℕ) : ℕ :=
  800 * (d + 1) * (p ^ d + 1) * ((d + 1) * (2 * scalarWidth p + 1) + 1) + 9

def framedEnumerationInput (p d : ℕ) [Fact p.Prime] : StructuredProgram.State 10 9 :=
  ⟨fun _ => false, fun i =>
    if i = 1 then ProgramEncoding.encodeRecords (framedAlphabet p)
    else if i = 8 then List.replicate d false else []⟩

theorem framedEnumeration_runsIn (p d : ℕ) [Fact p.Prime] :
    ∃ next : StructuredProgram.State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords (framedCandidates p d) ∧
      next.stacks 8 = [] ∧
      RunsIn enumerationProgram (framedEnumerationCost p d)
        ((framedEnumerationInput p d).withPC (some enumerationProgram.entry))
        (next.withPC none) := by
  have hi : outerInvariant (framedAlphabet p) (List.replicate d false) false
      (framedEnumerationInput p d) := by simp [outerInvariant, framedEnumerationInput]
  obtain ⟨next, hnext, k, hk, he⟩ := generateProgram_runsIn (framedAlphabet p)
    (List.replicate d false) false (framedEnumerationInput p d) hi
    (by simp [framedEnumerationInput]) (by simp [framedEnumerationInput])
    (by simp [framedEnumerationInput])
  have hwidth : ∀ word ∈ framedAlphabet p, word.length ≤ 2 * scalarWidth p + 1 := by
    intro word hw
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw
    exact ((framedScalarCode p).length_block x).le
  have hc := Subexp.PackingTupleBounds.generated_powerCost_le
    (framedAlphabet p) d (2 * scalarWidth p + 1) hwidth
  refine ⟨next, ?_, hnext.1.2.2.2.2.2.1, k, ?_, he⟩
  · simpa [framedCandidates] using hnext.2.1
  · have hk' : k ≤ powerCost (framedAlphabet p) d [[]] + 9 := by simpa using hk
    exact hk'.trans (by simpa [framedEnumerationCost] using Nat.add_le_add_right hc 9)

theorem framedEnumeration_primitive (p d : ℕ) [Fact p.Prime] :
    ∃ next : StructuredProgram.State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords (framedCandidates p d) ∧
      next.stacks 8 = [] ∧
      Computation.RunsIn (primitive enumerationProgram).step
        (primitiveOverhead enumerationProgram * framedEnumerationCost p d)
        (primitiveCfg enumerationProgram
          ((framedEnumerationInput p d).withPC (some enumerationProgram.entry)))
        (primitiveCfg enumerationProgram (next.withPC none)) := by
  obtain ⟨next, hout, hdepth, hrun⟩ := framedEnumeration_runsIn p d
  exact ⟨next, hout, hdepth, primitive_execution enumerationProgram hrun⟩

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
