import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SAT

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

/-- Unary natural-number field, terminated by a false bit. -/
def encodeNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Read a unary field and return the unconsumed suffix. -/
def readNat : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← readNat rest
      pure (n + 1, tail)

@[simp] theorem readNat_encodeNat_append (n : ℕ) (rest : List Bool) :
    readNat (encodeNat n ++ rest) = some (n, rest) := by
  induction n with
  | zero => simp [encodeNat, readNat]
  | succ n ih =>
      change (do
        let (v, tail) ← readNat (encodeNat n ++ rest)
        pure (v + 1, tail)) = some (n + 1, rest)
      rw [ih]
      rfl

@[simp] theorem readNat_encodeNat (n : ℕ) : readNat (encodeNat n) = some (n, []) := by
  simpa using readNat_encodeNat_append n []

@[simp] theorem length_encodeNat (n : ℕ) : (encodeNat n).length = n + 1 := by
  simp [encodeNat]

theorem encodeNat_injective : Function.Injective encodeNat := by
  intro n m h
  have hr := congrArg (fun bits => readNat (bits ++ [])) h
  simpa using hr

/-- Escape each data bit with a true bit; terminate the frame by false. -/
def frame (bits : List Bool) : List Bool :=
  bits.foldr (fun b rest => true :: b :: rest) [false]

@[simp] theorem frame_nil : frame [] = [false] := rfl

@[simp] theorem frame_cons (b : Bool) (bits : List Bool) :
    frame (b :: bits) = true :: b :: frame bits := rfl

/-- Decode one escape frame and return its unconsumed suffix. -/
def readFrame : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: rest => some ([], rest)
  | true :: [] => none
  | true :: b :: rest => do
      let (bs, tail) ← readFrame rest
      pure (b :: bs, tail)

@[simp] theorem readFrame_frame_append (bits rest : List Bool) :
    readFrame (frame bits ++ rest) = some (bits, rest) := by
  induction bits with
  | nil => simp [readFrame]
  | cons b bits ih => simp [readFrame, ih]

@[simp] theorem length_frame (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => simp
  | cons b bits ih => simp only [frame_cons, List.length_cons, ih]; omega

theorem frame_append_injective {bits bits' rest rest' : List Bool}
    (h : frame bits ++ rest = frame bits' ++ rest') :
    bits = bits' ∧ rest = rest' := by
  have hr := congrArg readFrame h
  simpa using hr

/-- Explicit list syntax: false ends a list; true introduces a framed item. -/
def encodeList {α : Type*} (enc : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: as => true :: (frame (enc a) ++ encodeList enc as)

theorem encodeList_injective {α : Type*} {enc : α → List Bool}
    (hinj : Function.Injective enc) : Function.Injective (encodeList enc) := by
  intro as
  induction as with
  | nil =>
      intro bs h
      cases bs <;> simp_all [encodeList]
  | cons a as ih =>
      intro bs h
      cases bs with
      | nil => simp [encodeList] at h
      | cons b bs =>
          have ht : frame (enc a) ++ encodeList enc as =
              frame (enc b) ++ encodeList enc bs := by
            simpa only [encodeList, List.cons.injEq, true_and] using h
          obtain ⟨hab, htail⟩ := frame_append_injective ht
          exact congrArg₂ List.cons (hinj hab) (ih htail)

@[simp] theorem length_encodeList_nil {α : Type*} (enc : α → List Bool) :
    (encodeList enc []).length = 1 := rfl

@[simp] theorem length_encodeList_cons {α : Type*} (enc : α → List Bool)
    (a : α) (as : List α) :
    (encodeList enc (a :: as)).length =
      2 * (enc a).length + 2 + (encodeList enc as).length := by
  simp only [encodeList, List.length_cons, List.length_append, length_frame]
  omega

theorem length_encodeList_lower {α : Type*} (enc : α → List Bool) (as : List α) :
    as.length + 1 ≤ (encodeList enc as).length := by
  induction as with
  | nil => simp
  | cons a as ih => rw [length_encodeList_cons]; simp only [List.length_cons]; omega

theorem length_encodeList_upper {α : Type*} (enc : α → List Bool)
    (as : List α) (K : ℕ) (hK : ∀ a ∈ as, (enc a).length ≤ K) :
    (encodeList enc as).length ≤ 1 + (2 * K + 2) * as.length := by
  induction as with
  | nil => simp
  | cons a as ih =>
      have ha := hK a (by simp)
      have ht := ih (fun b hb => hK b (by simp [hb]))
      rw [length_encodeList_cons]
      simp only [List.length_cons]
      calc
        2 * (enc a).length + 2 + (encodeList enc as).length
            ≤ 2 * K + 2 + (1 + (2 * K + 2) * as.length) := by omega
        _ = 1 + (2 * K + 2) * (as.length + 1) := by ring

/-- Literal syntax contains its variable index and polarity, independently of semantics. -/
def literalCode {n : ℕ} (l : SAT.Literal (Fin n)) : ℕ :=
  2 * l.variable.val + if l.positive then 1 else 0

theorem literalCode_injective {n : ℕ} :
    Function.Injective (literalCode (n := n)) := by
  intro a b h
  rcases a with ⟨av, ap⟩
  rcases b with ⟨bv, bp⟩
  cases ap <;> cases bp <;> simp [literalCode] at h
  · have hv : av = bv := Fin.ext (by omega)
    cases hv
    rfl
  · omega
  · omega
  · have hv : av = bv := Fin.ext (by omega)
    cases hv
    rfl

theorem literalCode_lt {n : ℕ} (l : SAT.Literal (Fin n)) : literalCode l < 2 * n := by
  have hv := l.variable.isLt
  cases hp : l.positive <;> simp [literalCode, hp] ; omega

/-- Sort the injective numerical representations of a clause's literals. -/
def clauseNumbers {n : ℕ} (C : SAT.Clause (Fin n)) : List ℕ :=
  (C.image literalCode).sort (· ≤ ·)

@[simp] theorem length_clauseNumbers {n : ℕ} (C : SAT.Clause (Fin n)) :
    (clauseNumbers C).length = C.card := by
  simp [clauseNumbers, Finset.card_image_of_injective _ literalCode_injective]

theorem clauseNumbers_injective {n : ℕ} :
    Function.Injective (clauseNumbers (n := n)) := by
  intro C D h
  apply Finset.image_injective literalCode_injective
  have hs := congrArg List.toFinset h
  simpa [clauseNumbers] using hs

theorem mem_clauseNumbers_lt {n : ℕ} {C : SAT.Clause (Fin n)} {a : ℕ}
    (h : a ∈ clauseNumbers C) : a < 2 * n := by
  have hi : a ∈ C.image literalCode := by simpa [clauseNumbers] using h
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hi
  exact literalCode_lt l

/-- Canonical order of the explicit literal lists of the formula's clauses. -/
def cnfNumbers {n : ℕ} (F : SAT.CNF (Fin n)) : List (List ℕ) :=
  (F.image clauseNumbers).sort (· ≤ ·)

@[simp] theorem length_cnfNumbers {n : ℕ} (F : SAT.CNF (Fin n)) :
    (cnfNumbers F).length = F.card := by
  simp [cnfNumbers, Finset.card_image_of_injective _ clauseNumbers_injective]

theorem cnfNumbers_injective {n : ℕ} :
    Function.Injective (cnfNumbers (n := n)) := by
  intro F G h
  apply Finset.image_injective clauseNumbers_injective
  have hs := congrArg List.toFinset h
  simpa [cnfNumbers] using hs

/-- The payload is a list of literal-code lists, in explicit binary list syntax. -/
def encodeCNFBody {n : ℕ} (F : SAT.CNF (Fin n)) : List Bool :=
  encodeList (encodeList encodeNat) (cnfNumbers F)

/-- Full binary formula syntax, including the ambient number of variables. -/
def encodeCNF {n : ℕ} (F : SAT.CNF (Fin n)) : List Bool :=
  encodeNat n ++ encodeCNFBody F

def formulaBitLength {n : ℕ} (F : SAT.CNF (Fin n)) : ℕ := (encodeCNF F).length

@[simp] theorem readNat_encodeCNF {n : ℕ} (F : SAT.CNF (Fin n)) :
    readNat (encodeCNF F) = some (n, encodeCNFBody F) := by
  simp [encodeCNF]

theorem encodeCNFBody_injective {n : ℕ} :
    Function.Injective (encodeCNFBody (n := n)) :=
  (encodeList_injective (encodeList_injective encodeNat_injective)).comp
    cnfNumbers_injective

theorem encodeCNF_injective {n : ℕ} : Function.Injective (encodeCNF (n := n)) := by
  intro F G h
  apply encodeCNFBody_injective
  exact List.append_cancel_left h

theorem encodeCNF_numVariables {n m : ℕ} (F : SAT.CNF (Fin n)) (G : SAT.CNF (Fin m))
    (h : encodeCNF F = encodeCNF G) : n = m := by
  have hr := congrArg (fun bits => (readNat bits).map Prod.fst) h
  simpa [encodeCNF] using hr

/-- The encoding also distinguishes formulas with different variable-coordinate types. -/
def encodeFormula (F : (n : ℕ) × SAT.CNF (Fin n)) : List Bool := encodeCNF F.2

theorem encodeFormula_injective : Function.Injective encodeFormula := by
  rintro ⟨n, F⟩ ⟨m, G⟩ h
  have hnm : n = m := encodeCNF_numVariables F G h
  subst m
  have hFG : F = G := encodeCNF_injective h
  cases hFG
  rfl

@[simp] theorem formulaBitLength_eq {n : ℕ} (F : SAT.CNF (Fin n)) :
    formulaBitLength F = n + 1 + (encodeCNFBody F).length := by
  simp [formulaBitLength, encodeCNF]

theorem formulaBitLength_lower {n : ℕ} (F : SAT.CNF (Fin n)) :
    n + F.card + 2 ≤ formulaBitLength F := by
  have h := length_encodeList_lower (encodeList encodeNat) (cnfNumbers F)
  rw [length_cnfNumbers] at h
  rw [formulaBitLength_eq]
  change F.card + 1 ≤ (encodeCNFBody F).length at h
  omega

theorem numVariables_le_formulaBitLength {n : ℕ} (F : SAT.CNF (Fin n)) :
    n ≤ formulaBitLength F := by
  have := formulaBitLength_lower F
  omega

theorem numClauses_le_formulaBitLength {n : ℕ} (F : SAT.CNF (Fin n)) :
    F.card ≤ formulaBitLength F := by
  have := formulaBitLength_lower F
  omega

theorem length_encodeClause_upper {n : ℕ} (C : SAT.Clause (Fin n)) :
    (encodeList encodeNat (clauseNumbers C)).length ≤ 1 + (4 * n + 4) * C.card := by
  have h := length_encodeList_upper encodeNat (clauseNumbers C) (2 * n + 1)
    (fun a ha => by rw [length_encodeNat]; have := mem_clauseNumbers_lt ha; omega)
  have hc : 2 * (2 * n + 1) + 2 = 4 * n + 4 := by omega
  simpa only [length_clauseNumbers, hc] using h

/-- A polynomial upper bound for the actual encoding, without any semantic oracle. -/
theorem formulaBitLength_upper {n k : ℕ} (F : SAT.CNF (Fin n))
    (hw : SAT.WidthAtMost k F) :
    formulaBitLength F ≤ n + 2 + (4 + (8 * n + 8) * k) * F.card := by
  have hp : ∀ as ∈ cnfNumbers F,
      (encodeList encodeNat as).length ≤ 1 + (4 * n + 4) * k := by
    intro as has
    have hi : as ∈ F.image clauseNumbers := by simpa [cnfNumbers] using has
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hi
    exact (length_encodeClause_upper C).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hw C hC)) _)
  have h := length_encodeList_upper (encodeList encodeNat) (cnfNumbers F)
    (1 + (4 * n + 4) * k) hp
  rw [length_cnfNumbers] at h
  rw [formulaBitLength_eq]
  change (encodeCNFBody F).length ≤ _ at h
  calc
    n + 1 + (encodeCNFBody F).length
        ≤ n + 1 + (1 + (2 * (1 + (4 * n + 4) * k) + 2) * F.card) :=
          Nat.add_le_add_left h _
    _ = n + 2 + (4 + (8 * n + 8) * k) * F.card := by ring

end SubexponentialSAT.Encoding

end OAI.Algorithms
