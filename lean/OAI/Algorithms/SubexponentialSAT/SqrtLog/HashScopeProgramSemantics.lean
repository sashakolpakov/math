import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScopeProducer
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramOrigin

namespace OAI.Algorithms

/-! Raw hash scopes include every referenced literal, irrespective of its
coefficient. The physical materializer preserves these exact original codes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram

abbrev Word := List Bool
abbrev Term := Word × List ℕ

def payload (term : Term) : Word :=
  Encoding.frame term.1 ++ Encoding.encodeList Encoding.encodeNat term.2

def mergedCodes (terms : List Term) : List ℕ := terms.reverse.flatMap Prod.snd

def scope (terms : List Term) : List ℕ :=
  SubexpScopeProducer.scope [true] (mergedCodes terms)

@[simp] theorem mem_mergedCodes (terms : List Term) (c : ℕ) :
    c ∈ mergedCodes terms ↔ ∃ term ∈ terms, c ∈ term.2 := by
  simp [mergedCodes]

@[simp] theorem mem_scope (terms : List Term) (v : ℕ) :
    v ∈ scope terms ↔ ∃ term ∈ terms, ∃ code ∈ term.2, code / 2 = v := by
  simp only [scope, SubexpScopeProducer.mem_scope, mem_mergedCodes]
  simp only [BinaryArithmetic.toNat, Nat.mul_zero, Nat.add_zero, BinaryArithmetic.bitVal_true, Nat.div_one]
  aesop

theorem scope_nodup (terms : List Term) : (scope terms).Nodup :=
  SubexpScopeProducer.scope_nodup _ _

theorem scope_lt (terms : List Term) (n : ℕ)
    (h : ∀ term ∈ terms, ∀ c ∈ term.2, c / 2 < n) :
    ∀ v ∈ scope terms, v < n := by
  intro v hv
  obtain ⟨term,ht,c,hc,rfl⟩ := (mem_scope terms v).mp hv
  exact h term ht c hc

theorem mergedCodes_length (terms : List Term) :
    (mergedCodes terms).length = (terms.map fun term => term.2.length).sum := by
  simp [mergedCodes, List.length_flatMap, List.map_reverse]

theorem scope_length_le (terms : List Term) :
    (scope terms).length ≤ (terms.map fun term => term.2.length).sum := by
  exact (SubexpScopeProducer.scope_length_le _ _).trans_eq (mergedCodes_length terms)

def rawTerms {n m depth : ℕ} (weight : ZMod 3 → Word)
    (source : Fin m → List (SAT.Literal (Fin n))) (h : HashFamily.Candidate m depth) : List Term :=
  (HashInputProgram.rawRow source h).map fun term =>
    (weight term.1, term.2.map Encoding.literalCode)

theorem rawTerms_payload {n m depth : ℕ} (weight : ZMod 3 → Word)
    (source : Fin m → List (SAT.Literal (Fin n))) (h : HashFamily.Candidate m depth) :
    (rawTerms weight source h).map payload =
      (HashInputProgram.rawRow source h).map (fun term =>
        HashInputProgram.weightedPayload (weight term.1) term.2) := by
  simp only [rawTerms, List.map_map]
  apply List.map_congr_left
  intro term _
  simp [payload, HashInputProgram.weightedPayload, HashInputProgram.clausePayload_codes]

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
