import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramScalar
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramProjection
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProductSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsSparse

namespace OAI.Algorithms

/-! Exact stored-list specification of the native Horner application. The
operations here are the functional results of the concrete normalized-add
and sparse-product machines, rather than operations on noncomputable jets. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open SubexpLiftRing SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}

abbrev Stored := List (Product.Entry n (baseWidth p t) d)

def constantStored (word : RingProgram.ScalarCode p t) : Stored p t (n:=n) (d:=d) :=
  [(Squarefree.Index.origin,scalarVector cache.zero word)]

def addStored (a b : Stored p t (n:=n) (d:=d)) : Stored p t (n:=n) (d:=d) :=
  Normalize.run p t M cache a b

def mulStored (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (uCap J : ℕ)
    (a b : Stored p t (n:=n) (d:=d)) : Stored p t (n:=n) (d:=d) :=
  Product.run p t M cache table uCap J a b []

def tripleStored (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (uCap J : ℕ)
    (h : Stored p t (n:=n) (d:=d)) (v : Triple (RingProgram.ScalarCode p t)) : Stored p t (n:=n) (d:=d) :=
  addStored p t M cache
    (mulStored p t M cache table uCap J
      (addStored p t M cache
        (mulStored p t M cache table uCap J (constantStored p t cache v.c) h)
        (constantStored p t cache v.b)) h)
    (constantStored p t cache v.a)

def descendingStored (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (uCap J : ℕ)
    (h g : Stored p t (n:=n) (d:=d)) (vs : List (Triple (RingProgram.ScalarCode p t)))
    (acc : Stored p t (n:=n) (d:=d)) : Stored p t (n:=n) (d:=d) :=
  vs.foldl (fun current v => addStored p t M cache
    (mulStored p t M cache table uCap J current g)
    (tripleStored p t M cache table uCap J h v)) acc

omit [Fact (Nat.Prime p)] in
theorem constantStored_nodup (word : RingProgram.ScalarCode p t) :
    (Squarefree.Sparse.keys (constantStored p t cache (n:=n) (d:=d) word)).Nodup := by
  simp [constantStored,Squarefree.Sparse.keys]

theorem tripleStored_nodup
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (uCap J : ℕ)
    (h : Stored p t (n:=n) (d:=d)) (v : Triple (RingProgram.ScalarCode p t)) :
    (Squarefree.Sparse.keys (tripleStored p t M cache table uCap J h v)).Nodup := by
  exact Normalize.run_nodup p t M cache _ _ (constantStored_nodup p t cache v.a)

theorem descendingStored_nodup
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (uCap J : ℕ)
    (h g : Stored p t (n:=n) (d:=d)) (vs : List (Triple (RingProgram.ScalarCode p t)))
    (acc : Stored p t (n:=n) (d:=d)) (ha : (Squarefree.Sparse.keys acc).Nodup) :
    (Squarefree.Sparse.keys (descendingStored p t M cache table uCap J h g vs acc)).Nodup := by
  induction vs generalizing acc with
  | nil => exact ha
  | cons v vs ih =>
    apply ih
    exact Normalize.run_nodup p t M cache _ _ (tripleStored_nodup p t M cache table uCap J h v)

variable {R : Type*} [CommRing R] (φ : ZMod (p^t) →+* R) (basis : Fin d → R)

noncomputable def storedDenote (a : Stored p t (n:=n) (d:=d)) : Squarefree.Jet (Fin n) R :=
  Squarefree.Sparse.denote (MomentsProgram.Dictionary.denoteTable
    (RingProgram.denote (RingProgram.scalarRing p t M cache) φ basis) a)

theorem addStored_denote (a b : Stored p t (n:=n) (d:=d))
    (hb : (Squarefree.Sparse.keys b).Nodup) :
    storedDenote p t M cache φ basis (addStored p t M cache a b)=
      storedDenote p t M cache φ basis a+storedDenote p t M cache φ basis b := by
  exact Normalize.run_decode p t M cache φ basis Squarefree.Sparse.atom
    Squarefree.Sparse.atom_zero Squarefree.Sparse.atom_add a b hb

theorem mulStored_denote
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (table i j k))*basis k)
    (uCap J : ℕ) (a b : Stored p t (n:=n) (d:=d)) :
    storedDenote p t M cache φ basis (mulStored p t M cache table uCap J a b)=
      Squarefree.canonical (V:=Fin n) (R:=R) uCap J
        (storedDenote p t M cache φ basis a*storedDenote p t M cache φ basis b) := by
  simpa [mulStored,storedDenote,MomentsProgram.Dictionary.denoteTable,
    Squarefree.Sparse.denote,Squarefree.Sparse.decode] using
    Product.run_denote p t M cache φ basis table htable uCap J a b [] (by simp [Squarefree.Sparse.keys])

theorem constantStored_denote (hd : 0 < d) (hb : basis ⟨0,hd⟩=1)
    (uCap J : ℕ) (hu : 0 < uCap) (hj : 0 < J) (word : RingProgram.ScalarCode p t) :
    storedDenote p t M cache φ basis (constantStored p t cache (n:=n) word)=
      Squarefree.canonical (V:=Fin n) (R:=R) uCap J
        ((Moments.ringScalar (V:=Fin n)).comp φ (wordValue p t word)) := by
  simp only [storedDenote,constantStored,MomentsProgram.Dictionary.denoteTable,
    List.map_cons,List.map_nil,Squarefree.Sparse.denote,Squarefree.Sparse.decode,
    RingHom.comp_apply,add_zero]
  rw [scalarVector_denote p t M cache φ hd basis hb,Moments.ringScalar_eq_atom,
    Squarefree.Sparse.canonical_atom]
  simp [Squarefree.Index.origin,Squarefree.Index.Kept,hu,hj]

theorem tripleStored_denote
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1)
    (uCap J : ℕ) (hu : 0 < uCap) (hj : 0 < J)
    (h : Stored p t (n:=n) (d:=d)) (v : Triple (RingProgram.ScalarCode p t)) :
    storedDenote p t M cache φ basis (tripleStored p t M cache table uCap J h v)=
      tripleAlgebra (LeafProgram.projectedAlgebra (Squarefree.canonical (V:=Fin n) (R:=R) uCap J))
        (fun c => Squarefree.canonical (V:=Fin n) (R:=R) uCap J
          ((Moments.ringScalar (V:=Fin n)).comp φ (wordValue p t c)))
        (storedDenote p t M cache φ basis h) v := by
  unfold tripleStored
  rw [addStored_denote p t M cache φ basis _ _ (constantStored_nodup p t cache v.a)]
  rw [mulStored_denote p t M cache φ basis table htable]
  rw [addStored_denote p t M cache φ basis _ _ (constantStored_nodup p t cache v.b)]
  rw [mulStored_denote p t M cache φ basis table htable]
  simp only [constantStored_denote p t M cache φ basis hd hb uCap J hu hj,
    tripleAlgebra,LeafProgram.projectedAlgebra]

theorem descendingStored_denote
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1)
    (uCap J : ℕ) (hu : 0 < uCap) (hj : 0 < J)
    (h g : Stored p t (n:=n) (d:=d)) (vs : List (Triple (RingProgram.ScalarCode p t)))
    (acc : Stored p t (n:=n) (d:=d)) :
    storedDenote p t M cache φ basis (descendingStored p t M cache table uCap J h g vs acc)=
      descendingAlgebra (LeafProgram.projectedAlgebra (Squarefree.canonical (V:=Fin n) (R:=R) uCap J))
        (fun c => Squarefree.canonical (V:=Fin n) (R:=R) uCap J
          ((Moments.ringScalar (V:=Fin n)).comp φ (wordValue p t c)))
        (storedDenote p t M cache φ basis h) (storedDenote p t M cache φ basis g)
        vs (storedDenote p t M cache φ basis acc) := by
  induction vs generalizing acc with
  | nil => rfl
  | cons v vs ih =>
    change storedDenote p t M cache φ basis
      (descendingStored p t M cache table uCap J h g vs
        (addStored p t M cache (mulStored p t M cache table uCap J acc g)
          (tripleStored p t M cache table uCap J h v))) = _
    rw [ih,addStored_denote p t M cache φ basis _ _ (tripleStored_nodup p t M cache table uCap J h v),
      mulStored_denote p t M cache φ basis table htable,
      tripleStored_denote p t M cache φ basis table htable hd hb uCap J hu hj]
    rfl

private theorem apply_projected_scalar (uCap J : ℕ)
    (H U : Squarefree.Jet (Fin n) R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) :
    let project := Squarefree.canonical (V:=Fin n) (R:=R) uCap J
    let ops := RingProgram.scalarRing p t M cache
    let ψ := (Moments.ringScalar (V:=Fin n)).comp φ
    descendingAlgebra (LeafProgram.projectedAlgebra project)
        (fun c => project (ψ (ops.decode c))) (project H)
        (project (U * IdempotentProgram.hValue H))
        (List.ofFn (coefficientTriple t code)).reverse 0 =
      project (∑ s : Fin t,
        U^s.val * (IdempotentProgram.digitPolynomial ops code s).eval₂ ψ H *
          IdempotentProgram.hValue H^s.val) := by
  dsimp only
  exact apply_projected _ (Squarefree.canonical_mul uCap J) _ _ H U t code

theorem applyStored_denote
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (table i j k))*basis k)
    (hd : 0 < d) (hb : basis ⟨0,hd⟩=1)
    (uCap J : ℕ) (hu : 0 < uCap) (hj : 0 < J)
    (h g : Stored p t (n:=n) (d:=d)) (H U : Squarefree.Jet (Fin n) R)
    (hH : storedDenote p t M cache φ basis h=Squarefree.canonical (V:=Fin n) (R:=R) uCap J H)
    (hG : storedDenote p t M cache φ basis g=
      Squarefree.canonical (V:=Fin n) (R:=R) uCap J (U*IdempotentProgram.hValue H))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) :
    storedDenote p t M cache φ basis
      (descendingStored p t M cache table uCap J h g
        (List.ofFn (coefficientTriple t code)).reverse []) =
      Squarefree.canonical (V:=Fin n) (R:=R) uCap J (∑ s : Fin t,
        U^s.val * (IdempotentProgram.digitPolynomial (RingProgram.scalarRing p t M cache)
          code s).eval₂ ((Moments.ringScalar (V:=Fin n)).comp φ) H *
        IdempotentProgram.hValue H^s.val) := by
  rw [descendingStored_denote p t M cache φ basis table htable hd hb uCap J hu hj,hH,hG]
  have hz : storedDenote p t M cache φ basis ([] : Stored p t (n:=n) (d:=d))=0 := rfl
  rw [hz]
  let project := Squarefree.canonical (V:=Fin n) (R:=R) uCap J
  let ops := RingProgram.scalarRing p t M cache
  let ψ := (Moments.ringScalar (V:=Fin n)).comp φ
  change descendingAlgebra (LeafProgram.projectedAlgebra project)
      (fun c => project (ψ (ops.decode c))) (project H)
      (project (U * IdempotentProgram.hValue H))
      (List.ofFn (coefficientTriple t code)).reverse 0 =
    project (∑ s : Fin t,
      U^s.val * (IdempotentProgram.digitPolynomial ops code s).eval₂ ψ H *
        IdempotentProgram.hValue H^s.val)
  exact apply_projected_scalar p t M cache φ uCap J H U code

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
