import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientCheckerSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPredicate

namespace OAI.Algorithms

/-! Exact finite candidate order and correctness target for the coefficient
search. The physical generator's reversals are retained. -/

namespace SubexponentialSAT.Subexp.CoefficientSearchSemantics

open SubexpTupleRefinement MatrixWordEncoding CoefficientCheckerSemantics

variable (p : ℕ) [Fact p.Prime]

def alphabet : List (ZMod p) := (QuarticSearch.elements p).reverse

def scalarTokens : List (List Bool) :=
  (alphabet p).map (fun x => Encoding.frame (word p x))

def rows (R : ℕ) : List (List Bool) := TupleProgram.powerRows (scalarTokens p) R [[]]

def encode {R : ℕ} (v : Fin R → ZMod p) : List Bool :=
  encodeTuple (BlockSearchPredicate.scalarCode p) v

def valueTest (A : ℕ) {R : ℕ} (v : Fin R → ZMod p) : Bool :=
  checkHeads R (advanceParity A false) (CoefficientDynamics.shifts A (List.ofFn v))

def test (A R : ℕ) (bits : List Bool) : Bool :=
  BlockSearchPredicate.finiteTest (QuarticSearch.vectors (alphabet p) R)
    (encode p) (valueTest p A) bits

theorem alphabet_complete (x : ZMod p) : x ∈ alphabet p := by
  simpa [alphabet] using QuarticSearch.mem_elements p x

theorem encode_injective (R : ℕ) : Function.Injective (encode p (R := R)) :=
  encodeTuple_injective (BlockSearchPredicate.scalarCode p) R

theorem test_encode (A R : ℕ) (v : Fin R → ZMod p) :
    test p A R (encode p v) = valueTest p A v := by
  exact BlockSearchPredicate.finiteTest_encoded _ _ (encode_injective p R) _ v
    (QuarticSearch.mem_vectors (alphabet p) (alphabet_complete p) R v)

theorem encode_mem (R : ℕ) (v : Fin R → ZMod p) : encode p v ∈ rows p R := by
  exact encodeTuple_mem_powerRows (BlockSearchPredicate.scalarCode p) (alphabet p)
    (alphabet_complete p) R v

theorem mem_rows (R : ℕ) (bits : List Bool) :
    bits ∈ rows p R ↔ ∃ v : Fin R → ZMod p, encode p v = bits := by
  rw [rows]
  change bits ∈ TupleProgram.powerRows
    ((alphabet p).map (BlockSearchPredicate.scalarCode p).block) R [[]] ↔ _
  rw [mem_powerRows_encoded]
  constructor
  · rintro ⟨v, _, h⟩
    exact ⟨v, h⟩
  · rintro ⟨v, h⟩
    exact ⟨v, QuarticSearch.mem_vectors (alphabet p) (alphabet_complete p) R v, h⟩

theorem test_iff (A R : ℕ) (bits : List Bool) (hbits : bits ∈ rows p R) :
    test p A R bits = true ↔ ∃ v : Fin R → ZMod p, encode p v = bits ∧
      ∀ d < R, CoefficientDynamics.evaluate (List.ofFn v) (A + d) = (-1 : ZMod p)^(A + d) := by
  obtain ⟨v, rfl⟩ := (mem_rows p R bits).mp hbits
  rw [test_encode]
  change checkHeads R (advanceParity A false) (CoefficientDynamics.shifts A (List.ofFn v)) = true ↔ _
  rw [checkHeads_normalized]
  constructor
  · intro h
    exact ⟨v,rfl,h⟩
  · rintro ⟨w, hw, h⟩
    have hv := encode_injective p R hw
    subst w
    exact h

theorem exists_success (h2 : (2 : ZMod p) ≠ 0) (A R : ℕ) :
    ∃ bits ∈ rows p R, test p A R bits = true := by
  obtain ⟨xs, hlen, hcheck⟩ := exists_checkHeads h2 A R
  subst R
  let v : Fin xs.length → ZMod p := xs.get
  have hv : List.ofFn v = xs := List.ofFn_get xs
  refine ⟨encode p v, encode_mem p xs.length v, ?_⟩
  rw [test_encode]
  simpa only [valueTest, hv] using hcheck

omit [Fact p.Prime] in
theorem rows_length (R : ℕ) : (rows p R).length = p ^ R := by
  simp [rows, TupleProgram.generated_count, scalarTokens, alphabet]

theorem encode_length {R : ℕ} (v : Fin R → ZMod p) :
    (encode p v).length = R * (2 * width p + 1) := by
  rw [encode, encodeTuple, StackEncoding.length_encodeDataStack, List.length_ofFn]
  rfl

end SubexponentialSAT.Subexp.CoefficientSearchSemantics

end OAI.Algorithms
