import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSparseBounds

namespace OAI.Algorithms

/-! Negation preserves the sparse support and the canonical representation.
These lemmas extend the semiring interface without changing its dependencies. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

variable {V R : Type*} [DecidableEq V] [CommRing R]

omit [DecidableEq V] in
@[simp] theorem neg_length (l : Data (Index V) R) : (neg l).length = l.length :=
  List.length_map _

omit [DecidableEq V] in
@[simp] theorem keys_neg (l : Data (Index V) R) : keys (neg l) = keys l := by
  simp [keys, neg, List.map_map, Function.comp_def]

omit [DecidableEq V] in
theorem ValidData.neg {vars : Finset V} {t J : ℕ} {a : Data (Index V) R}
    (ha : ValidData vars t J a) : ValidData vars t J (neg a) := by
  intro k hk
  rw [keys_neg] at hk
  exact ha k hk

omit [DecidableEq V] in
theorem neg_nodup {a : Data (Index V) R} (ha : (keys a).Nodup) :
    (keys (neg a)).Nodup := by simpa using ha

theorem neg_storage {vars : Finset V} {t J : ℕ} {a : Data (Index V) R}
    (ha : ValidData vars t J a) (hna : (keys a).Nodup) :
    (neg a).length ≤ t * J * (supportUniverse vars J).card := by
  simpa using ha.length_le hna

end SubexponentialSAT.SqrtLog.Squarefree.Sparse

end OAI.Algorithms
