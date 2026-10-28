import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramProductFold
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNativeSemantics

namespace OAI.Algorithms

/-! Typed selected-ID semantics of the actual factor fold. Neutral IDs are
skipped, including in the output list; no redundant multiplication is added. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open NativeSemantics
open scoped BigOperators

variable {p t n d : ℕ} [Fact p.Prime]

abbrev Raw := List (MomentsProgram.Product.Entry n (baseWidth p t) d)

def selectedRun (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (select : ℕ → Option (Raw (p:=p) (t:=t) (n:=n) (d:=d)))
    (ids : List ℕ) (seed : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  Product.run p t M cache table u J seed (ids.filterMap select)

@[simp] theorem selectedRun_nil (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (select : ℕ → Option (Raw (p:=p) (t:=t) (n:=n) (d:=d))) (seed : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    selectedRun M cache table u J select [] seed = seed := rfl

theorem selectedRun_cons (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (select : ℕ → Option (Raw (p:=p) (t:=t) (n:=n) (d:=d)))
    (id : ℕ) (ids : List ℕ) (seed : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    selectedRun M cache table u J select (id::ids) seed =
      match select id with
      | none => selectedRun M cache table u J select ids seed
      | some factor => selectedRun M cache table u J select ids
          (MomentsProgram.Product.run p t M cache table u J seed factor []) := by
  cases h : select id <;> simp [selectedRun,h,Product.run]

theorem selectedRun_good (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ)
    (select : ℕ → Option (Raw (p:=p) (t:=t) (n:=n) (d:=d))) (ids : List ℕ)
    (hselect : ∀ id ∈ ids, ∀ factor, select id = some factor → Good vars u J factor)
    (seed : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (hseed : Good vars u J seed) :
    Good vars u J (selectedRun M cache table u J select ids seed) := by
  induction ids generalizing seed with
  | nil => exact hseed
  | cons id ids ih =>
    rw [selectedRun_cons]
    cases h : select id with
    | none => exact ih (fun j hj => hselect j (by simp [hj])) seed hseed
    | some factor =>
      exact ih (fun j hj => hselect j (by simp [hj])) _
        (product_good p t M cache table vars u J seed factor hseed
          (hselect id (by simp) factor h))

/-- Indexed semantics allow distinct IDs to emit identical raw dictionaries.
No injectivity or artificial choice of a meaning for a raw dictionary is used. -/
theorem selectedRun_denote {R : Type*} [CommRing R]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i*basis j =
      ∑ k, scalar (wordValue p t (table i j k))*basis k) (u J : ℕ)
    (select : ℕ → Option (Raw (p:=p) (t:=t) (n:=n) (d:=d)))
    (value : ℕ → Squarefree.Jet (Fin n) R) (ids : List ℕ)
    (hsome : ∀ id ∈ ids, ∀ factor, select id = some factor →
      rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) factor =
        Squarefree.canonical u J (value id))
    (hnone : ∀ id ∈ ids, select id = none → value id = 1)
    (seed : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (start : Squarefree.Jet (Fin n) R)
    (hseed : rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) seed =
      Squarefree.canonical u J start) :
    rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis)
      (selectedRun M cache table u J select ids seed) =
        Squarefree.canonical u J (start * (ids.map value).prod) := by
  induction ids generalizing seed start with
  | nil => simpa using hseed
  | cons id ids ih =>
    rw [selectedRun_cons]
    cases h : select id with
    | none =>
      have hv := hnone id (by simp) h
      simpa [hv] using ih (fun j hj => hsome j (by simp [hj]))
        (fun j hj => hnone j (by simp [hj])) seed start hseed
    | some factor =>
      have hp := product_denote p t M cache scalar basis table htable u J seed factor
      rw [hseed,hsome id (by simp) factor h,Squarefree.canonical_mul] at hp
      simpa only [List.map_cons,List.prod_cons,mul_assoc] using
        ih (fun j hj => hsome j (by simp [hj])) (fun j hj => hnone j (by simp [hj]))
          _ (start * value id) hp

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
