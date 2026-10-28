import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpJetAccumulator

namespace OAI.Algorithms

/-!
# The concrete extraction generator's query order

The machine enumerates moments first, traverses Z and U inside each moment,
and prepends output records.  The older jet formula is Z-major.  The following
permutation proof connects these exact finite orders without changing the
number or identity of visits.
-/

namespace SubexponentialSAT.SubexpQueryOrder

open SubexpExtractionJobs

theorem flatMap_swap {α β γ : Type*} (xs : List α) (ys : List β)
    (f : α → β → List γ) :
    (xs.flatMap fun x => ys.flatMap (f x)).Perm
      (ys.flatMap fun y => xs.flatMap fun x => f x y) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      exact (ih.append_left (ys.flatMap (f x))).trans
        (List.flatMap_append_perm ys (f x) (fun y => xs.flatMap fun x => f x y))

def perMoment (D : ℕ) (a : Fin D → ℕ) : List (Query D) :=
  (List.range D).flatMap fun z =>
    (List.range (D + 1)).map fun u => ⟨a, u, z⟩

/-- This is the order emitted by the actual prepend-based outer job loop. -/
def generatedQueries (D : ℕ) : List (Query D) :=
  ((Algorithm.exponentList D (2 * D + 1)).reverse.flatMap (perMoment D)).reverse

theorem generatedQueries_perm (D : ℕ) : (generatedQueries D).Perm (queries D) := by
  unfold generatedQueries
  apply (List.reverse_perm _).trans
  apply ((List.reverse_perm (Algorithm.exponentList D (2 * D + 1))).flatMap_right
    (perMoment D)).trans
  exact flatMap_swap (Algorithm.exponentList D (2 * D + 1)) (List.range D)
    (fun a z => (List.range (D + 1)).map fun u => Query.mk a u z)

theorem generatedQueries_length (D : ℕ) :
    (generatedQueries D).length = D * ((3 * D + 1).choose D) * (D + 1) := by
  rw [(generatedQueries_perm D).length_eq, queries_length]

/-- Slot visit order used by the key-only generator. Its writer prepends keys,
so the actual encoded master stores the reverse of this list. -/
def visitSlots (D : ℕ) : List (SymbolicCost.RawIndex D) :=
  (Algorithm.exponentList D (2 * D + 1)).reverse.flatMap fun a =>
    (List.range D).flatMap fun z =>
      (List.range (D + 1)).map fun u => (a, (u, z))

theorem visitSlots_perm (D : ℕ) : (visitSlots D).Perm (Algorithm.retainedSlots D) := by
  have hi (a : Fin D → ℕ) :
      ((List.range D).flatMap fun z => (List.range (D + 1)).map fun u => (a, (u, z))).Perm
        ((List.range (D + 1)).flatMap fun u => (List.range D).map fun z => (a, (u, z))) := by
    simpa only [← List.map_eq_flatMap] using
      flatMap_swap (List.range D) (List.range (D + 1)) (fun z u => [(a, (u, z))])
  have houter := (List.reverse_perm (Algorithm.exponentList D (2 * D + 1))).flatMap_right
    (fun a => (List.range D).flatMap fun z => (List.range (D + 1)).map fun u => (a, (u, z)))
  have h := houter.trans (List.Perm.flatMap_left _ (fun a _ => hi a))
  simpa only [visitSlots, Algorithm.retainedSlots, List.product, List.map_flatMap,
    List.map_map, Function.comp_def] using h

theorem visitSlots_nodup (D : ℕ) : (visitSlots D).Nodup :=
  (visitSlots_perm D).symm.nodup (Algorithm.retainedSlots_nodup D)

theorem mem_visitSlots (D : ℕ) (a : SymbolicCost.RawIndex D) :
    a ∈ visitSlots D ↔ SymbolicCost.Retained D a :=
  (visitSlots_perm D).mem_iff.trans (Algorithm.mem_retainedSlots D a)

theorem visitSlots_length (D : ℕ) :
    (visitSlots D).length = (3 * D + 1).choose D * ((D + 1) * D) := by
  rw [(visitSlots_perm D).length_eq, Algorithm.retainedSlots_length]

def generatedJobs {D : ℕ} {C : Type*} (encode : SymbolicCost.CoeffList D C → List Bool)
    (program : (Fin D → ℕ) → Algorithm.Expr (SymbolicCost.CoeffList D C)) :
    List SubexpMomentProgram.Job :=
  (generatedQueries D).map fun q =>
    ⟨List.replicate q.z true, SubexpSymbolicCost.fixedKey (q.exponent, (q.u, q.z)),
      SubexpPostfixControl.serializeCode encode (program q.exponent).compile⟩

theorem generatedJobs_perm {D : ℕ} {C : Type*}
    (encode : SymbolicCost.CoeffList D C → List Bool)
    (program : (Fin D → ℕ) → Algorithm.Expr (SymbolicCost.CoeffList D C)) :
    (generatedJobs encode program).Perm (jobs encode program) :=
  (generatedQueries_perm D).map _

/-- Actual machine visit order has precisely the verified jet semantics. -/
theorem generatedQueries_fold_eq_rawJet {D : ℕ} {R : Type*} [CommSemiring R]
    (program : (Fin D → ℕ) → Algorithm.Expr (SymbolicCost.CoeffList D R)) :
    (List.range D).map (fun r =>
      ((generatedQueries D).foldl
        (SubexpJetAccumulator.addAt Query.z (contribution program)) (fun _ => 0)) r) =
      Algorithm.executeRawJet program :=
  SubexpJetAccumulator.permuted_queries_fold_eq_rawJet program _ (generatedQueries_perm D)

end SubexponentialSAT.SubexpQueryOrder

end OAI.Algorithms
