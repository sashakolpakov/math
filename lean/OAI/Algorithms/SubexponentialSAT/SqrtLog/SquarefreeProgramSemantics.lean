import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramReplace

namespace OAI.Algorithms

/-! Semantic contract of the primitive dictionary replacement, including its
use as the storage step of normalized additive insertion. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram

variable {K C A : Type*} [DecidableEq K] [AddCommMonoid C]

def put (k : K) (c : C) (entries : Sparse.Data K C) : Sparse.Data K C :=
  (k,c) :: (Sparse.erase k entries).reverse

omit [AddCommMonoid C] in
theorem put_keys_nodup (k : K) (c : C) (entries : Sparse.Data K C)
    (h : (Sparse.keys entries).Nodup) : (Sparse.keys (put k c entries)).Nodup := by
  have he : (Sparse.keys (Sparse.erase k entries)).Nodup := by
    rw [Sparse.keys_erase]
    exact h.filter _
  have hn : k ∉ Sparse.keys (Sparse.erase k entries) := by
    rw [Sparse.keys_erase]
    simp
  have hr : (Sparse.keys (Sparse.erase k entries)).reverse.Nodup := by simpa using he
  have hnr : k ∉ (Sparse.keys (Sparse.erase k entries)).reverse := by simpa using hn
  simpa [put,Sparse.keys,List.map_reverse] using List.nodup_cons.mpr ⟨hnr,hr⟩

omit [AddCommMonoid C] in
theorem put_length (k : K) (c : C) (entries : Sparse.Data K C) :
    (put k c entries).length ≤ entries.length + 1 := by
  have h := List.length_filter_le (fun a : K × C => decide (a.1 ≠ k)) entries
  simpa [put,Sparse.erase] using Nat.add_le_add_right h 1

section Decode
variable [AddCommMonoid A]

omit [DecidableEq K] [AddCommMonoid C] in
theorem decode_reverse (atom : K → C → A) (entries : Sparse.Data K C) :
    Sparse.decode atom entries.reverse = Sparse.decode atom entries := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    simp [List.reverse_cons,Sparse.decode_append,Sparse.decode,ih,add_comm]

omit [AddCommMonoid C] in
theorem decode_put (atom : K → C → A) (k : K) (c : C) (entries : Sparse.Data K C) :
    Sparse.decode atom (put k c entries) = atom k c + Sparse.decode atom (Sparse.erase k entries) := by
  simp only [put,Sparse.decode,decode_reverse]


/-- Reversal changes storage order only. Adding the old coefficient first
makes primitive replacement exactly the semantic additive insertion. -/
theorem decode_put_add (atom : K → C → A) (k : K) (c : C) (entries : Sparse.Data K C) :
    Sparse.decode atom (put k (c + Sparse.fetch k entries) entries) =
      Sparse.decode atom (Sparse.insert k c entries) := by
  simp only [decode_put,Sparse.insert,Sparse.decode]
end Decode

omit [AddCommMonoid C] in
theorem encode_erase (key : K → List Bool) (coeff : C → List Bool) (hk : Function.Injective key)
    (k : K) (entries : Sparse.Data K C) :
    encodeDictionary key coeff (Sparse.erase k entries) =
      erasedEntries (key k) (encodeDictionary key coeff entries) := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    by_cases h : j=k
    · subst j
      simpa [Sparse.erase,encodeDictionary,erasedEntries] using ih
    · have h' : key j ≠ key k := fun hh => h (hk hh)
      simpa [Sparse.erase,encodeDictionary,erasedEntries,h,h'] using
        congrArg ((key j,coeff c)::·) ih

omit [AddCommMonoid C] in
theorem encode_put (key : K → List Bool) (coeff : C → List Bool) (hk : Function.Injective key)
    (k : K) (c : C) (entries : Sparse.Data K C) :
    encodeDictionary key coeff (put k c entries) =
      (key k,coeff c)::(erasedEntries (key k) (encodeDictionary key coeff entries)).reverse := by
  simp only [put,encodeDictionary,List.map_cons,List.map_reverse]
  exact congrArg ((key k,coeff c)::·) (congrArg List.reverse (encode_erase key coeff hk k entries))

omit [AddCommMonoid C] in
theorem dictionaryPut_trace (key : K → List Bool) (coeff : C → List Bool) (hk : Function.Injective key)
    (k : K) (c : C) (entries : Sparse.Data K C) (regs : Fin 5 → Bool) :
    ∃ n ≤ eraseBudget (key k) (encodeDictionary key coeff entries) +
        4 * (key k).length + 4 * (coeff c).length + 17, ∃ final,
      Trace dictionaryReplaceProgram n
        ((replaceData regs (encodeDictionary key coeff entries) (key k) (coeff c)).withPC
          (some dictionaryReplaceProgram.entry))
        ((replaceDone final (rawEntries (encodeDictionary key coeff (put k c entries)))).withPC none) := by
  rw [encode_put key coeff hk]
  exact dictionaryReplace_trace _ _ _ _
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
