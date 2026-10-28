import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLoopFinal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramOrigin
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayloadRoundTrip
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyEncoding

namespace OAI.Algorithms

/-! The assembler receives exactly the selector's raw candidate bytes. Its
source is a serialized original formula, and its result is a produced inline
row, with every raw tuple occurrence retained. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def candidateTerms {m depth : ℕ} (h : HashFamily.Candidate m depth) :
    List (Fin m × ZMod 3) := List.ofFn fun j => (h.1 j,h.2 j)

theorem candidate_rawInput {m depth : ℕ} (width : ℕ)
    (h : HashFamily.Candidate m depth) :
    Loop.rawInput width (candidateTerms h) = HashFamilyPayload.encode width h := by
  simp only [Loop.rawInput,candidateTerms,List.map_ofFn,HashFamilyPayload.encode,
    HashFamilyPayload.encodeDigits]
  rfl

theorem candidate_payloads {m depth n : ℕ} (t d : ℕ)
    (source : Fin m → List (SAT.Literal (Fin n))) (clauses : List (List Bool))
    (hm : clauses.length=m) (h : HashFamily.Candidate clauses.length depth)
    (hs : ∀ i : Fin clauses.length, clauses[i.val]=clausePayload (source (Fin.cast hm i))) :
    (candidateTerms h).map (Loop.payload t d clauses) =
      (rawRow (fun i => source (Fin.cast hm i)) h).map
        (fun term => weightedPayload (RingProgram.flat (constantVector t d term.1)) term.2) := by
  simp only [candidateTerms,rawRow,List.map_ofFn,weightedPayload]
  congr 1
  funext j
  change Encoding.frame (RingProgram.flat (constantVector t d (h.2 j))) ++ clauses[(h.1 j).val] =
    Encoding.frame (RingProgram.flat (constantVector t d (h.2 j))) ++
      clausePayload (source (Fin.cast hm (h.1 j)))
  rw [hs]

/-- This theorem starts from the selector's raw byte payload and the actual
source serialization. No inline weighted clauses are supplied as input. -/
theorem assemble_serialized_candidate_runs {α : Type*} {depth : ℕ}
    (t d : ℕ) (ht : 0 < t) (width : ℕ) (hwpos : 0 < width)
    (source : List α) (enc : α → List Bool)
    (h : HashFamily.Candidate (source.map enc).length depth)
    (hbound : 3*(source.map enc).length ≤ 2^width) (regs : Fin 8 → Bool)
    (widthBits modulus shape : List Bool)
    (hw : widthBits.length=width)
    (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=(source.map enc).length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ rf, RunsIn Loop.assembleProgram
      (Loop.uniformBudget t d width modulus (source.map enc) depth+3)
      ((Loop.data regs (HashFamilyPayload.encode width h) widthBits modulus
        (Encoding.encodeList enc source) shape [] [] [] [] []).withPC
          (some Loop.assembleProgram.entry))
      ((Loop.data rf [] widthBits modulus (Encoding.encodeList enc source) shape
        (Encoding.encodeList id ((candidateTerms h).map (Loop.payload t d (source.map enc))))
        [] [] [] []).withPC none) := by
  have hr := Loop.assemble_runs t d ht width hwpos (source.map enc) (candidateTerms h)
    hbound regs widthBits modulus shape hw hm hshape
  rw [candidate_rawInput] at hr
  simpa only [candidateTerms,List.length_ofFn,
    ExecSparsifyEncoding.encodeList_map,id_eq] using hr


/-- Every actual generated selector payload, not merely an extensionally equal
row, is accepted by the same fixed native assembler. -/
theorem assemble_generated_candidate_runs {α : Type*} {depth : ℕ}
    (t d : ℕ) (ht : 0 < t) (width : ℕ) (hwpos : 0 < width)
    (source : List α) (enc : α → List Bool)
    (hsource : 0 < (source.map enc).length)
    (raw : List Bool)
    (hraw : raw ∈ HashSelectProgram.generatedPayloads
      (HashFamilyPayload.alphabet (source.map enc).length width) depth)
    (hbound : 3*(source.map enc).length ≤ 2^width) (regs : Fin 8 → Bool)
    (widthBits modulus shape : List Bool)
    (hw : widthBits.length=width)
    (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=(source.map enc).length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    let h := HashFamilyPayload.decode (source.map enc).length depth width hsource raw
    ∃ rf, RunsIn Loop.assembleProgram
      (Loop.uniformBudget t d width modulus (source.map enc) depth+3)
      ((Loop.data regs raw widthBits modulus (Encoding.encodeList enc source)
        shape [] [] [] [] []).withPC (some Loop.assembleProgram.entry))
      ((Loop.data rf [] widthBits modulus (Encoding.encodeList enc source) shape
        (Encoding.encodeList id ((candidateTerms h).map (Loop.payload t d (source.map enc))))
        [] [] [] []).withPC none) := by
  dsimp only
  have hr := assemble_serialized_candidate_runs t d ht width hwpos source enc
    (HashFamilyPayload.decode (source.map enc).length depth width hsource raw)
    hbound regs widthBits modulus shape hw hm hshape
  rw [HashFamilyPayload.encode_decode_generated hsource hbound raw hraw] at hr
  exact hr

end SubexponentialSAT.SqrtLog.HashInputProgram

end OAI.Algorithms
