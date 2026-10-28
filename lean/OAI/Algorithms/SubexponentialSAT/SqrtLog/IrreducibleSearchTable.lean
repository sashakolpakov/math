import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCompanion

namespace OAI.Algorithms

/-!
# Materialized companion tables

Store every power vector once and build the multiplication table from those
stored rows. No recursively expanded coefficient function is used as a
substitute for storing the intermediate companion states.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

def storedPowers {R : Type*} [Ring R] {d : ℕ} (c : Fin d → R) :
    List.Vector (List.Vector R d) (2 * d + 1) :=
  List.Vector.ofFn fun n => List.Vector.ofFn (powerVector c n.val)

def storedTable {R : Type*} [Ring R] {d : ℕ} (c : Fin d → R) :
    List.Vector (List.Vector (List.Vector R d) d) d :=
  let powers := storedPowers c
  List.Vector.ofFn fun i => List.Vector.ofFn fun j =>
    powers.get ⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩

@[simp] theorem storedPowers_get {R : Type*} [Ring R] {d : ℕ}
    (c : Fin d → R) (n : Fin (2 * d + 1)) (i : Fin d) :
    ((storedPowers c).get n).get i = powerVector c n.val i := by
  simp [storedPowers, List.Vector.get_ofFn]

@[simp] theorem storedTable_get {R : Type*} [Ring R] {d : ℕ}
    (c : Fin d → R) (i j k : Fin d) :
    (((storedTable c).get i).get j).get k = structureTable c i j k := by
  simp [storedTable, storedPowers, List.Vector.get_ofFn, structureTable]

theorem storedTable_eq_coeff {R : Type*} [CommRing R] [Nontrivial R] [DecidableEq R]
    {d : ℕ} (hd : 0 < d) (c : Fin d → R) (i j k : Fin d) :
    (((storedTable c).get i).get j).get k =
      ((Polynomial.X ^ (i.val + j.val)) %ₘ QuarticSearch.poly c).coeff k.val := by
  rw [storedTable_get, structureTable_eq_coeff hd c]

theorem entry_map {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) {d : ℕ} (a : Fin d → R) (n : ℕ) :
    entry (fun i => f (a i)) n = f (entry a n) := by
  by_cases h : n < d <;> simp [entry, h]

theorem mulX_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    {d : ℕ} (c a : Fin d → R) (i : Fin d) :
    mulX (fun j => f (c j)) (fun j => f (a j)) i = f (mulX c a i) := by
  by_cases h : i.val = 0 <;> simp [mulX, h, entry_map]

theorem powerVector_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    {d : ℕ} (c : Fin d → R) (n : ℕ) :
    powerVector (fun i => f (c i)) n = fun i => f (powerVector c n i) := by
  induction n with
  | zero =>
      funext i
      by_cases h : i.val = 0 <;> simp [powerVector, oneVector, h]
  | succ n ih =>
      funext i
      simp only [powerVector, cacheVector_eq, ih]
      exact mulX_map f c (powerVector c n) i

theorem structureTable_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    {d : ℕ} (c : Fin d → R) (i j k : Fin d) :
    structureTable (fun l => f (c l)) i j k = f (structureTable c i j k) := by
  simp only [structureTable, powerVector_map]

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
