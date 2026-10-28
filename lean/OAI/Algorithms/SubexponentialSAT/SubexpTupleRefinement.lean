import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.SubexpVectorEnumeration
import OAI.Algorithms.SubexponentialSAT.StackEncoding

namespace OAI.Algorithms

/-!
# Representation and coverage of the fixed tuple program

The tuple program reverses its record order at each Cartesian expansion.
These theorems retain that actual order and show that it is a permutation of
the explicit coefficient-vector enumeration. Fixed-width injective encodings
then give uniqueness, not just coverage.
-/

namespace SubexponentialSAT.SubexpTupleRefinement

open Subexp.TupleProgram

def tuplePayload {n : ℕ} (v : Fin n → List Bool) : List Bool :=
  (List.ofFn v).flatten

@[simp] theorem tuplePayload_zero (v : Fin 0 → List Bool) : tuplePayload v = [] := rfl

@[simp] theorem tuplePayload_cons {n : ℕ} (a : List Bool) (v : Fin n → List Bool) :
    tuplePayload (Fin.cons a v) = a ++ tuplePayload v := by
  simp [tuplePayload, List.ofFn_succ]

/-- All record reversals affect order only; every prefix/suffix combination
is generated with its correct multiplicity. -/
theorem powerRows_perm (alphabet rows : List (List Bool)) (n : ℕ) :
    (powerRows alphabet n rows).Perm
      (rows.flatMap fun pre => (QuarticSearch.vectors alphabet n).map
        (fun v => pre ++ tuplePayload v)) := by
  induction n generalizing rows with
  | zero => simp [powerRows, QuarticSearch.vectors, tuplePayload]
  | succ n ih =>
    change (powerRows alphabet n (cartesianOutput rows alphabet)).Perm _
    refine (ih (cartesianOutput rows alphabet)).trans ?_
    refine ((cartesianOutput_perm rows alphabet).flatMap_right
      (fun pre => (QuarticSearch.vectors alphabet n).map
        (fun v => pre ++ tuplePayload v))).trans ?_
    apply List.Perm.of_eq
    simp only [QuarticSearch.vectors, List.flatMap_assoc, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def, tuplePayload_cons,
      List.append_assoc]

theorem powerRows_empty_perm (alphabet : List (List Bool)) (n : ℕ) :
    (powerRows alphabet n [[]]).Perm
      ((QuarticSearch.vectors alphabet n).map tuplePayload) := by
  simpa using powerRows_perm alphabet [[]] n

theorem vectors_map {A B : Type*} (f : A → B) (alphabet : List A) (n : ℕ) :
    QuarticSearch.vectors (alphabet.map f) n =
      (QuarticSearch.vectors alphabet n).map (fun v i => f (v i)) := by
  induction n with
  | zero =>
      simp only [QuarticSearch.vectors, List.map_cons, List.map_nil]
      congr 2
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      simp only [QuarticSearch.vectors, ih, List.flatMap_map, List.map_flatMap,
        List.map_map, Function.comp_def]
      congr 1
      funext a
      congr 1
      funext v
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

def encodeTuple {A : Type*} (code : StackEncoding.BlockCode A)
    {n : ℕ} (v : Fin n → A) : List Bool :=
  StackEncoding.encodeDataStack code (List.ofFn v)

theorem encodeTuple_injective {A : Type*} (code : StackEncoding.BlockCode A) (n : ℕ) :
    Function.Injective (encodeTuple code (n := n)) := by
  intro v w h
  exact List.ofFn_injective (StackEncoding.encodeDataStack_injective code h)

theorem tuplePayload_map {A : Type*} (code : StackEncoding.BlockCode A)
    {n : ℕ} (v : Fin n → A) :
    tuplePayload (fun i => code.block (v i)) = encodeTuple code v := by
  rw [encodeTuple, StackEncoding.encodeDataStack_eq_flatMap]
  change (List.ofFn (code.block ∘ v)).flatten = _
  rw [← List.map_ofFn]
  rfl

/-- The actual fixed-control tuple program enumerates precisely the encoded
vectors for any fixed-width code, in its own explicit order. -/
theorem powerRows_encoded_perm {A : Type*} (code : StackEncoding.BlockCode A)
    (alphabet : List A) (n : ℕ) :
    (powerRows (alphabet.map code.block) n [[]]).Perm
      ((QuarticSearch.vectors alphabet n).map (encodeTuple code)) := by
  have h := powerRows_empty_perm (alphabet.map code.block) n
  rw [vectors_map, List.map_map] at h
  simpa only [Function.comp_def, tuplePayload_map] using h

theorem powerRows_encoded_nodup {A : Type*} (code : StackEncoding.BlockCode A)
    (alphabet : List A) (h : alphabet.Nodup) (n : ℕ) :
    (powerRows (alphabet.map code.block) n [[]]).Nodup := by
  apply (powerRows_encoded_perm code alphabet n).nodup_iff.mpr
  exact (SubexpVectorEnumeration.vectors_nodup alphabet h n).map
    (encodeTuple_injective code n)

theorem mem_powerRows_encoded {A : Type*} (code : StackEncoding.BlockCode A)
    (alphabet : List A) (n : ℕ) (bits : List Bool) :
    bits ∈ powerRows (alphabet.map code.block) n [[]] ↔
      ∃ v ∈ QuarticSearch.vectors alphabet n, encodeTuple code v = bits := by
  rw [(powerRows_encoded_perm code alphabet n).mem_iff, List.mem_map]

/-- Every requested tuple is visited when the scalar alphabet is complete. -/
theorem encodeTuple_mem_powerRows {A : Type*} (code : StackEncoding.BlockCode A)
    (alphabet : List A) (hfull : ∀ a, a ∈ alphabet) (n : ℕ) (v : Fin n → A) :
    encodeTuple code v ∈ powerRows (alphabet.map code.block) n [[]] := by
  rw [mem_powerRows_encoded]
  exact ⟨v, QuarticSearch.mem_vectors alphabet hfull n v, rfl⟩

theorem encodeTuple_append {A : Type*} (code : StackEncoding.BlockCode A)
    {d e : ℕ} (a : Fin d → A) (b : Fin e → A) :
    encodeTuple code (Fin.append a b) = encodeTuple code a ++ encodeTuple code b := by
  simp only [encodeTuple, List.ofFn_fin_append, StackEncoding.encodeDataStack_append]

theorem encodePair_injective {A : Type*} (code : StackEncoding.BlockCode A) (d e : ℕ) :
    Function.Injective (fun ab : (Fin d → A) × (Fin e → A) =>
      encodeTuple code ab.1 ++ encodeTuple code ab.2) := by
  intro a b hab
  have heq : Fin.append a.1 a.2 = Fin.append b.1 b.2 :=
    encodeTuple_injective code (d + e) (by simpa only [encodeTuple_append] using hab)
  apply Prod.ext
  · funext i
    simpa only [Fin.append_left] using congrFun heq (Fin.castAdd e i)
  · funext i
    simpa only [Fin.append_right] using congrFun heq (Fin.natAdd d i)

/-- One tuple loop at depth d+e covers all concatenated coefficient pairs. -/
theorem encodePair_mem_powerRows {A : Type*} (code : StackEncoding.BlockCode A)
    (alphabet : List A) (hfull : ∀ a, a ∈ alphabet) {d e : ℕ}
    (a : Fin d → A) (b : Fin e → A) :
    encodeTuple code a ++ encodeTuple code b ∈
      powerRows (alphabet.map code.block) (d + e) [[]] := by
  simpa only [encodeTuple_append] using
    encodeTuple_mem_powerRows code alphabet hfull (d + e) (Fin.append a b)

/-- Each generated word has a unique pair of prefixes of the requested
coefficient lengths, including zero-length parts. -/
theorem generated_unique_pair {A : Type*} (code : StackEncoding.BlockCode A)
    (alphabet : List A) (d e : ℕ) (bits : List Bool)
    (hbits : bits ∈ powerRows (alphabet.map code.block) (d + e) [[]]) :
    ∃! ab : (Fin d → A) × (Fin e → A),
      encodeTuple code ab.1 ++ encodeTuple code ab.2 = bits := by
  obtain ⟨v, _, hv⟩ := (mem_powerRows_encoded code alphabet (d + e) bits).mp hbits
  let ab : (Fin d → A) × (Fin e → A) :=
    (fun i => v (Fin.castAdd e i), fun i => v (Fin.natAdd d i))
  have hab : encodeTuple code ab.1 ++ encodeTuple code ab.2 = bits := by
    rw [← encodeTuple_append]
    change encodeTuple code (Fin.append (fun i => v (Fin.castAdd e i))
      (fun i => v (Fin.natAdd d i))) = bits
    rw [Fin.append_castAdd_natAdd]
    exact hv
  refine ⟨ab, hab, ?_⟩
  intro other hother
  exact encodePair_injective code d e (hother.trans hab.symm)

end SubexponentialSAT.SubexpTupleRefinement

end OAI.Algorithms
