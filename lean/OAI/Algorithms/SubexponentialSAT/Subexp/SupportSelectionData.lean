import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata
import OAI.Algorithms.SubexponentialSAT.MulticolorTypes

namespace OAI.Algorithms

/-! Ordered support records selected from the actual packing inverse. -/

namespace SubexponentialSAT.Subexp.SupportSelectionProgram

open ConstructivePacking

abbrev unary (n : ℕ) : List Bool := List.replicate n true

variable {D r Q Δ : ℕ}

def colorAt (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (g : ℕ) (v : Fin D) : Bool :=
  match P.lookup v with
  | none => false
  | some (_, u) => decide ((u.head t).val = g)

def outsideAt (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (v : Fin D) : Bool := (P.lookup v).isNone

def colorTest (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (g n : ℕ) : Bool :=
  if h : n < D then colorAt P t g ⟨n, h⟩ else false

def outsideTest (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (n : ℕ) : Bool :=
  if h : n < D then outsideAt P ⟨n, h⟩ else false

def indexWords (p : ℕ → Bool) (n : ℕ) : List (List Bool) :=
  ((List.range n).filter p).map unary

def record (n : ℕ) : List Bool := true :: Encoding.frame (unary n)

def supportPrefix (p : ℕ → Bool) (n : ℕ) : List Bool :=
  ((List.range n).filter p).flatMap record

@[simp] theorem prefix_zero (p : ℕ → Bool) : supportPrefix p 0 = [] := rfl

theorem prefix_succ (p : ℕ → Bool) (n : ℕ) :
    supportPrefix p (n + 1) = supportPrefix p n ++ if p n then record n else [] := by
  simp only [supportPrefix, List.range_succ, List.filter_append, List.flatMap_append]
  cases h : p n <;> simp [h]

theorem prefix_encode (p : ℕ → Bool) (n : ℕ) :
    supportPrefix p n ++ [false] = Encoding.encodeList id (indexWords p n) := by
  have h (xs : List ℕ) : xs.flatMap record ++ [false] =
      Encoding.encodeList id (xs.map unary) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.map_cons, Encoding.encodeList, id_eq]
      rw [List.append_assoc, ih]
      rfl
  exact h _

@[simp] theorem record_length (n : ℕ) : (record n).length = 2 * n + 2 := by
  simp [record]

theorem indexWords_length_le (p : ℕ → Bool) (n : ℕ) : (indexWords p n).length ≤ n := by
  simpa [indexWords] using List.length_filter_le p (List.range n)

end SubexponentialSAT.Subexp.SupportSelectionProgram

end OAI.Algorithms
