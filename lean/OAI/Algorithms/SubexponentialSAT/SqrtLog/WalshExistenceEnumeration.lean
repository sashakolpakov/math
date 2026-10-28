import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistenceSearch

namespace OAI.Algorithms

/-! Executable binary indexing for Cayley vertices. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

/-- Explicit radix-two decoding. Both directions are computable; in particular
this does not use `Fintype.equivFin`. -/
def cubeEquiv (r : ℕ) : Fin (2 ^ r) ≃ Cube r :=
  (@finFunctionFinEquiv 2 r).symm

theorem cubeEquiv_decode (r : ℕ) (i : Fin (2 ^ r)) (j : Fin r) :
    (cubeEquiv r i j).val = i.val / 2 ^ j.val % 2 := by
  rfl

theorem cubeEquiv_encode (r : ℕ) (x : Cube r) :
    ((cubeEquiv r).symm x).val = ∑ j, (x j).val * 2 ^ j.val := by
  rfl

theorem cubeList_toFinset (r : ℕ) : (cubeList r).toFinset = Finset.univ := by
  ext x
  simp [mem_cubeList]

theorem cubeList_nodup (r : ℕ) : (cubeList r).Nodup := by
  have hc : (cubeList r).toFinset.card = (cubeList r).length := by
    rw [cubeList_toFinset, Finset.card_univ, cube_card, length_cubeList]
  exact (Multiset.toFinset_card_eq_card_iff_nodup
    (m := (cubeList r : Multiset (Cube r)))).mp hc

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
