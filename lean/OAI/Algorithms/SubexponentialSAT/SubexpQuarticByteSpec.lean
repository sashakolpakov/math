import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticSelector

namespace OAI.Algorithms

/-!
# Byte interpretation of the quartic search predicates

These total, executable functions specify the bit-level tests. The machine
callbacks prove these specifications on the generated fixed-width records.
No coefficient lookup or choice is used to interpret a payload.
-/

namespace SubexponentialSAT.SubexpQuarticByteSpec

open SubexpEnumerationPayload SubexpTupleRefinement

def readWord (p : ℕ) (bits : List Bool) : ZMod p := (BinaryArithmetic.toNat bits : ℕ)

def readTuple (p : ℕ) : (n : ℕ) → List Bool → (Fin n → ZMod p)
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, bits => Fin.cons (readWord p (bits.take (scalarWidth p)))
      (readTuple p n (bits.drop (scalarWidth p)))

theorem readWord_block (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    readWord p ((scalarCode p).block a) = a := by
  simp only [readWord, scalarCode, scalarBits_value, ZMod.natCast_zmod_val]

theorem tuple_cons (p n : ℕ) [Fact p.Prime] (c : Fin (n + 1) → ZMod p) :
    encodeTuple (scalarCode p) c = (scalarCode p).block (c 0) ++
      encodeTuple (scalarCode p) (fun i : Fin n => c i.succ) := by
  simp only [encodeTuple, List.ofFn_succ, StackEncoding.encodeDataStack_cons]

theorem readTuple_encode (p n : ℕ) [Fact p.Prime] (c : Fin n → ZMod p) :
    readTuple p n (encodeTuple (scalarCode p) c) = c := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      rw [tuple_cons p n c]
      have ht : ((scalarCode p).block (c 0) ++
          encodeTuple (scalarCode p) (fun i : Fin n => c i.succ)).take (scalarWidth p) =
          (scalarCode p).block (c 0) :=
        StackEncoding.take_block_append (scalarCode p) (c 0)
          (encodeTuple (scalarCode p) (fun i : Fin n => c i.succ))
      have hd : ((scalarCode p).block (c 0) ++
          encodeTuple (scalarCode p) (fun i : Fin n => c i.succ)).drop (scalarWidth p) =
          encodeTuple (scalarCode p) (fun i : Fin n => c i.succ) :=
        StackEncoding.drop_block_append (scalarCode p) (c 0)
          (encodeTuple (scalarCode p) (fun i : Fin n => c i.succ))
      simp only [readTuple, ht, hd, readWord_block, ih]
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

def linearTest (p : ℕ) (c : Fin 4 → ZMod p) (bits : List Bool) : Bool :=
  QuarticSearch.linearPass p c (readWord p bits)

def quadraticTest (p : ℕ) (c : Fin 4 → ZMod p) (bits : List Bool) : Bool :=
  QuarticSearch.quadraticPass p c (readTuple p 2 bits)

def candidateTest (p : ℕ) (bits : List Bool) : Bool :=
  QuarticSearch.passes p (readTuple p 4 bits)

theorem linearTest_block (p : ℕ) [Fact p.Prime]
    (c : Fin 4 → ZMod p) (a : ZMod p) :
    linearTest p c ((scalarCode p).block a) = QuarticSearch.linearPass p c a := by
  rw [linearTest, readWord_block]

theorem quadraticTest_block (p : ℕ) [Fact p.Prime]
    (c : Fin 4 → ZMod p) (a : Fin 2 → ZMod p) :
    quadraticTest p c (encodeTuple (scalarCode p) a) = QuarticSearch.quadraticPass p c a := by
  rw [quadraticTest, readTuple_encode]

theorem candidateTest_block (p : ℕ) [Fact p.Prime] (c : Fin 4 → ZMod p) :
    candidateTest p (encodeTuple (scalarCode p) c) = QuarticSearch.passes p c := by
  rw [candidateTest, readTuple_encode]

theorem all_linear (p : ℕ) [Fact p.Prime] (c : Fin 4 → ZMod p) :
    ((QuarticSearch.elements p).map (scalarCode p).block).all (linearTest p c) =
      (QuarticSearch.elements p).all (QuarticSearch.linearPass p c) := by
  simp only [List.all_map, Function.comp_def, linearTest_block]

theorem all_quadratic (p : ℕ) [Fact p.Prime] (c : Fin 4 → ZMod p) :
    ((QuarticSearch.vectors (QuarticSearch.elements p) 2).map (encodeTuple (scalarCode p))).all
      (quadraticTest p c) =
      (QuarticSearch.vectors (QuarticSearch.elements p) 2).all (QuarticSearch.quadraticPass p c) := by
  simp only [List.all_map, Function.comp_def, quadraticTest_block]

theorem candidate_first (p : ℕ) [Fact p.Prime] :
    (SubexpQuarticSelector.candidateRecords p).find? (candidateTest p) =
      some (encodeTuple (scalarCode p) (QuarticSearch.coefficients p)) :=
  SubexpQuarticSelector.first_candidateRecord p (candidateTest p) (candidateTest_block p)

end SubexponentialSAT.SubexpQuarticByteSpec

end OAI.Algorithms
