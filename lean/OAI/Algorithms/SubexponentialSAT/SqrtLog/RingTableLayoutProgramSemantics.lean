import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayoutProgramOuter

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

theorem rowBits_eq_ofFn (rows : List (List Bool)) (d n start : ℕ) :
    rowBits rows d start n =
      (List.ofFn fun j : Fin n => wordAt rows (start+j.val*d)).flatten := by
  induction n generalizing start with
  | zero => simp [rowBits]
  | succ n ih =>
      simp [rowBits, List.ofFn_succ, ih, Nat.add_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem matrixBits_eq_ofFn (rows : List (List Bool)) (d n start : ℕ) :
    matrixBits rows d start n =
      (List.ofFn fun i : Fin n =>
        (List.ofFn fun j : Fin d => wordAt rows (start+i.val*d+j.val*d)).flatten).flatten := by
  induction n generalizing start with
  | zero => simp [matrixBits]
  | succ n ih =>
      simp [matrixBits, List.ofFn_succ, ih, rowBits_eq_ofFn, Nat.add_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The exact public order: k first, then i, with j varying fastest. -/
theorem layoutBits_eq_ofFn (rows : List (List Bool)) (d n start : ℕ) :
    layoutBits rows d start n =
      (List.ofFn fun k : Fin n => (List.ofFn fun i : Fin d =>
        (List.ofFn fun j : Fin d => wordAt rows (start+k.val+i.val*d+j.val*d)).flatten).flatten).flatten := by
  induction n generalizing start with
  | zero => simp [layoutBits]
  | succ n ih =>
      simp [layoutBits, List.ofFn_succ, ih, matrixBits_eq_ofFn,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem flatten_ofFn_length {n B : ℕ} (f : Fin n → List Bool)
    (h : ∀ i, (f i).length = B) : (List.ofFn f).flatten.length = n*B := by
  have hh := ArrayUpdatePrograms.uniform_flatten_length (List.ofFn f) B (by
    intro row hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact h i)
  simpa using hh

theorem layoutBits_length (rows : List (List Bool)) (d n start B : ℕ)
    (h : ∀ k < n, ∀ i < d, ∀ j < d,
      (wordAt rows (start+k+i*d+j*d)).length = B) :
    (layoutBits rows d start n).length = n*(d*(d*B)) := by
  rw [layoutBits_eq_ofFn]
  apply flatten_ofFn_length
  intro k
  apply flatten_ofFn_length
  intro i
  apply flatten_ofFn_length
  intro j
  exact h k.val k.isLt i.val i.isLt j.val j.isLt

theorem table_index_lt (d k i j : ℕ) (hk : k < d) (hi : i < d) (hj : j < d) :
    k+i*d+j*d < d*(2*d-1) := by
  have hs : i+j+1 ≤ 2*d-1 := by omega
  have hm := Nat.mul_le_mul_right d hs
  nlinarith

theorem full_layout_length (rows : List (List Bool)) (d B : ℕ)
    (hw : ∀ row ∈ rows, row.length = B)
    (hn : d*(2*d-1) ≤ rows.length) :
    (layoutBits rows d 0 d).length = d^3*B := by
  have h := layoutBits_length rows d d 0 B (by
    intro k hk i hi j hj
    apply wordAt_length rows _ B
    · simpa using (table_index_lt d k i j hk hi hj).trans_le hn
    · exact hw)
  convert h using 1 ; ring

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
