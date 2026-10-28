import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblySemanticsValidity
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProductBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
open MomentsProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

/-- The normalized dictionary length bound is independent of the coefficient
ring and of how a particular value is decoded. -/
theorem valid_entries_length_le {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d))
    (hv : ValidEntries vars u J entries) (hn : (Sparse.keys entries).Nodup) :
    entries.length ≤ u * J * (Sparse.supportUniverse vars J).card := by
  have h := (Product.decoded_valid (fun _ => (0 : ℤ)) vars u J entries hv).length_le
    (by simpa only [Dictionary.denoteTable_keys] using hn)
  simpa [Dictionary.denoteTable] using h

/-- Practical uniform envelope for every reachable normalized dictionary.
The serialized bound includes every key and coefficient frame delimiter. -/
theorem valid_sizeBounds {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d))
    (hv : ValidEntries vars u J entries) (hn : (Sparse.keys entries).Nodup) :
    let L := u * J * (Sparse.supportUniverse vars J).card
    entries.length ≤ L ∧
      (Product.bytes entries).length ≤ L * (2 * (n + u + J) + 2 * (d * B) + 2) := by
  dsimp only
  have hl := valid_entries_length_le vars u J entries hv hn
  refine ⟨hl, (Product.bytes_length_le entries (n+u+J) ?_).trans
    (Nat.mul_le_mul_right _ hl)⟩
  intro a ha
  have h := encodeIndex_length_le a.1 (hv a ha).1
  omega

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
