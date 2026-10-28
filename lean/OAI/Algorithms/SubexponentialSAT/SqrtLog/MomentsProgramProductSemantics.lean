import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProduct
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramNormalize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSparseOps

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem decoded_row (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    Dictionary.denoteTable f
      (keptJoin a.1 u J (Squarefree.ScaleProgram.scaled p t M cache table a.2 right)) =
      Squarefree.Sparse.row u J (a.1,f a.2) (Dictionary.denoteTable f right) := by
  dsimp only
  induction right with
  | nil => rfl
  | cons b right ih =>
    have hm := RingProgram.denote_mul (RingProgram.scalarRing p t M cache) scalar basis table htable a.2 b.2
    by_cases h : (a.1.join b.1).Kept u J <;>
      simp only [Squarefree.ScaleProgram.scaled,List.map_cons,keptJoin,h,ite_true,ite_false,
        Dictionary.denoteTable,Squarefree.Sparse.row] at ih ⊢
    · rw [ih]
      congr 2
    · exact ih

theorem block_denote (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    Squarefree.Sparse.denote (Dictionary.denoteTable f (block p t M cache table u J a right)) =
      Squarefree.canonical u J (Squarefree.Sparse.atom a.1 (f a.2) *
        Squarefree.Sparse.denote (Dictionary.denoteTable f right)) := by
  dsimp only
  unfold block
  rw [show Dictionary.denoteTable
      (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis)
      (keptJoin a.1 u J (Squarefree.ScaleProgram.scaled p t M cache table a.2 right)).reverse =
    (Dictionary.denoteTable
      (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis)
      (keptJoin a.1 u J (Squarefree.ScaleProgram.scaled p t M cache table a.2 right))).reverse by
        simp [Dictionary.denoteTable]]
  rw [Squarefree.Sparse.denote,Squarefree.Program.decode_reverse,
    decoded_row p t M cache scalar basis table htable u J a right]
  exact Squarefree.Sparse.denote_row u J _ _

theorem run_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (left right seed : List (Entry n (baseWidth p t) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    (Squarefree.Sparse.keys (run p t M cache table u J left right seed)).Nodup := by
  induction left generalizing seed with
  | nil => exact hn
  | cons a left ih =>
    exact ih _ (Normalize.run_nodup p t M cache _ seed hn)

theorem run_denote (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (left right seed : List (Entry n (baseWidth p t) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    Squarefree.Sparse.denote (Dictionary.denoteTable f (run p t M cache table u J left right seed)) =
      Squarefree.canonical u J (Squarefree.Sparse.denote (Dictionary.denoteTable f left) *
        Squarefree.Sparse.denote (Dictionary.denoteTable f right)) +
      Squarefree.Sparse.denote (Dictionary.denoteTable f seed) := by
  dsimp only
  induction left generalizing seed with
  | nil => simp [run,Dictionary.denoteTable,Squarefree.Sparse.denote,Squarefree.Sparse.decode]
  | cons a left ih =>
    rw [run,ih _ (Normalize.run_nodup p t M cache _ seed hn)]
    have hsum := Normalize.run_decode p t M cache scalar basis
      Squarefree.Sparse.atom Squarefree.Sparse.atom_zero Squarefree.Sparse.atom_add
      (block p t M cache table u J a right) seed hn
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    change Squarefree.Sparse.denote (Dictionary.denoteTable f
      (Normalize.run p t M cache (block p t M cache table u J a right) seed)) =
      Squarefree.Sparse.denote (Dictionary.denoteTable f (block p t M cache table u J a right)) +
      Squarefree.Sparse.denote (Dictionary.denoteTable f seed) at hsum
    rw [hsum,block_denote p t M cache scalar basis table htable u J a right]
    let lv := Squarefree.Sparse.denote (Dictionary.denoteTable f left)
    let rv := Squarefree.Sparse.denote (Dictionary.denoteTable f right)
    let sv := Squarefree.Sparse.denote (Dictionary.denoteTable f seed)
    let av := Squarefree.Sparse.atom a.1 (f a.2)
    change Squarefree.canonical u J (lv*rv) +
      (Squarefree.canonical u J (av*rv)+sv) =
      Squarefree.canonical u J ((av+lv)*rv)+sv
    rw [add_mul,map_add]
    exact (add_assoc _ _ _).symm.trans (congrArg (fun x => x+sv) (add_comm _ _))

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

end OAI.Algorithms
