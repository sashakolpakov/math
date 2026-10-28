import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLoopFinal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramSlots

namespace OAI.Algorithms

/-! Exact scopes of the physically stored sparse raw rows and optional original
marked clause. These definitions are shared by the machine and resource proofs. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram
namespace FromTuple
/-- Semantic interpretation of original source clauses, used only in the proof. -/
def interpretedTerms (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ)
    (terms : List (Fin clauses.length × ZMod 3)) : List Term :=
  terms.map fun a => (RingProgram.flat (HashInputProgram.constantVector t d a.2),codes a.1)

theorem interpreted_payload (t d : ℕ) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (terms : List (Fin clauses.length × ZMod 3)) :
    Encoding.encodeList payload (interpretedTerms (clauses := clauses) t d codes terms)=
      Encoding.encodeList id (terms.map (HashInputProgram.Loop.payload t d clauses)) := by
  induction terms with
  | nil => rfl
  | cons a as ih =>
      simpa [interpretedTerms,Encoding.encodeList,payload,HashInputProgram.Loop.payload,hc] using
        congrArg (fun rest => true :: (Encoding.frame (HashInputProgram.Loop.payload t d clauses a) ++ rest)) ih


theorem mem_interpreted_scope (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ)
    (terms : List (Fin clauses.length × ZMod 3)) (v : ℕ) :
    v ∈ scope (interpretedTerms (clauses := clauses) t d codes terms) ↔
      ∃ a∈terms, ∃ c∈codes a.1, c/2=v := by
  rw [mem_scope]
  constructor
  · rintro ⟨term,hterm,c,hc,hv⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hterm
    exact ⟨a,ha,c,hc,hv⟩
  · rintro ⟨a,ha,c,hc,hv⟩
    exact ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,c,hc,hv⟩

end FromTuple
namespace RawTable
abbrev Rows (m : ℕ) := List (List (Fin m × ZMod 3))
def rowBits {m : ℕ} (b : ℕ) (terms : List (Fin m × ZMod 3)) : List Bool :=
  (terms.map (HashInputProgram.Loop.word b m)).flatten

def scopeBytes (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (terms : List (Fin clauses.length × ZMod 3)) : List Bool :=
  Encoding.encodeList Encoding.encodeNat
    (scope (FromTuple.interpretedTerms (clauses := clauses) t d codes terms))

end RawTable
namespace Marked
abbrev markedScope (codes : List ℕ) := SubexpScopeProducer.scope [true] codes
abbrev scopeBits (codes : List ℕ) := Encoding.encodeList Encoding.encodeNat (markedScope codes)

end Marked
namespace Complete
def scopeWords (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) : List (List Bool) :=
  rows.map (RawTable.scopeBytes (clauses := clauses) t d codes) ++
    mark.toList.map (fun i => Marked.scopeBits (codes i))

def scopes (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) : List (List ℕ) :=
  rows.map (fun row => scope (FromTuple.interpretedTerms (clauses := clauses) t d codes row)) ++
    mark.toList.map (fun i => Marked.markedScope (codes i))

def outputBits (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) : List Bool :=
  Encoding.encodeList id (scopeWords (clauses := clauses) t d codes rows mark)

theorem outputBits_nested (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) :
    outputBits (clauses := clauses) t d codes rows mark=Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (scopes (clauses := clauses) t d codes rows mark) := by
  have h : scopeWords (clauses := clauses) t d codes rows mark=(scopes (clauses := clauses) t d codes rows mark).map (Encoding.encodeList Encoding.encodeNat) := by
    simp [scopeWords,scopes,RawTable.scopeBytes,List.map_map,Function.comp_def]
  unfold outputBits
  rw [h]
  generalize scopes (clauses := clauses) t d codes rows mark=ss
  induction ss with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList,ih]

theorem scopes_length (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) :
    (scopes (clauses := clauses) t d codes rows mark).length=rows.length+mark.isSome.toNat := by
  cases mark <;> simp [scopes]

theorem scopes_prefix (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) :
    (scopes (clauses := clauses) t d codes rows mark).take rows.length=
      rows.map (fun row => scope (FromTuple.interpretedTerms (clauses := clauses) t d codes row)) := by
  unfold scopes
  rw [List.take_append_of_le_length (by simp)]
  simp

theorem scopes_marked_last (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (i : Fin clauses.length) :
    scopes (clauses := clauses) t d codes rows (some i)=
      rows.map (fun row => scope (FromTuple.interpretedTerms (clauses := clauses) t d codes row)) ++ [Marked.markedScope (codes i)] := by
  rfl

theorem scopes_marked_index (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) :
    (scopes (clauses := clauses) t d codes rows mark)[rows.length]?=
      mark.map (fun i => Marked.markedScope (codes i)) := by
  unfold scopes
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_map,Nat.sub_self]
  cases mark <;> rfl

end Complete
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
