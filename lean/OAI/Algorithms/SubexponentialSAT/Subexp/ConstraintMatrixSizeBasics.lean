import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixListEncoding

namespace OAI.Algorithms

/-! Exact sizes for the actual ordered fiber records and scalar matrix
encoding. These lemmas do not assume a canonical enumeration order. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixSizeBasics

open MulticolorTypes

variable {r Q Δ : ℕ}

theorem sideList_length (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length = blockSize r Q Δ / r := by
  have h := Fintype.card_congr (TypeEnumeration.sideEquiv (Δ := Δ) hr hQ t g)
  simpa only [Fintype.card_fin, card_side] using h

theorem jointList_length (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    (TypeEnumeration.jointList hr hQ t g i).length =
      (r - 1) * (blockSize r Q Δ / (r * r)) := by
  have h := Fintype.card_congr (TypeEnumeration.jointEquiv hr hQ t g i)
  simpa only [Fintype.card_fin, card_joint] using h

theorem sideList_length_le (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length ≤ blockSize r Q Δ := by
  rw [sideList_length]
  exact Nat.div_le_self _ _

theorem jointList_length_le_side (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    (TypeEnumeration.jointList hr hQ t g i).length ≤
      (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length := by
  have hs := Fintype.card_congr (TypeEnumeration.sideEquiv (Δ := Δ) hr hQ t g)
  have hj := Fintype.card_congr (TypeEnumeration.jointEquiv hr hQ t g i)
  simp only [Fintype.card_fin] at hs hj
  rw [hs, hj]
  exact card_joint_le_side t g i

theorem sideBytes_length (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (TypeEnumeration.sideBytes r Q Δ t.val g.val).length = blockSize r Q Δ / r := by
  rw [← TypeEnumeration.sideList_bytes hr hQ t g, List.length_map, sideList_length]

theorem jointBytes_length (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    (TypeEnumeration.jointBytes r Q Δ t.val g.val i.val).length =
      (r - 1) * (blockSize r Q Δ / (r * r)) := by
  rw [← TypeEnumeration.jointList_bytes hr hQ t g i, List.length_map, jointList_length]

theorem sideBytes_width (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    ∀ bits ∈ TypeEnumeration.sideBytes r Q Δ t.val g.val,
      bits.length = CollisionProgram.typeWidth r Q Δ := by
  intro bits hb
  rw [← TypeEnumeration.sideList_bytes hr hQ t g] at hb
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hb
  exact CollisionProgram.encodeType_length u.val

theorem jointBytes_width (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    ∀ bits ∈ TypeEnumeration.jointBytes r Q Δ t.val g.val i.val,
      bits.length = CollisionProgram.typeWidth r Q Δ := by
  intro bits hb
  rw [← TypeEnumeration.jointList_bytes hr hQ t g i] at hb
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hb
  exact CollisionProgram.encodeType_length u.val

theorem sum_lengths_of_uniform (records : List (List Bool)) (width : ℕ)
    (hwidth : ∀ bits ∈ records, bits.length = width) :
    (records.map List.length).sum = records.length * width := by
  induction records with
  | nil => simp
  | cons bits records ih =>
      have hb := hwidth bits (by simp)
      have ht := ih (fun b h => hwidth b (List.mem_cons_of_mem _ h))
      simp only [List.map_cons, List.sum_cons, List.length_cons, hb, ht]
      ring

theorem encodeRecords_length_of_uniform (records : List (List Bool)) (width : ℕ)
    (hwidth : ∀ bits ∈ records, bits.length = width) :
    (ProgramEncoding.encodeRecords records).length = records.length * (2 * width + 2) + 1 := by
  rw [ProgramEncoding.encodeRecords_length, sum_lengths_of_uniform records width hwidth]
  ring

theorem encodedSide_length (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t.val g.val)).length =
      (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length *
        (2 * CollisionProgram.typeWidth r Q Δ + 2) + 1 := by
  rw [encodeRecords_length_of_uniform _ _ (sideBytes_width hr hQ t g)]
  rw [← TypeEnumeration.sideList_bytes hr hQ t g, List.length_map]

theorem encodedJoint_length (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    (ProgramEncoding.encodeRecords (TypeEnumeration.jointBytes r Q Δ t.val g.val i.val)).length =
      (TypeEnumeration.jointList hr hQ t g i).length *
        (2 * CollisionProgram.typeWidth r Q Δ + 2) + 1 := by
  rw [encodeRecords_length_of_uniform _ _ (jointBytes_width hr hQ t g i)]
  rw [← TypeEnumeration.jointList_bytes hr hQ t g i, List.length_map]

theorem scalarRow_length {α : Type*} (p : ℕ) (columns : List α) (entry : α → ZMod p) :
    (columns.flatMap fun col => Encoding.frame (MatrixWordEncoding.word p (entry col))).length =
      columns.length * (2 * MatrixWordEncoding.width p + 1) := by
  induction columns with
  | nil => simp
  | cons col columns ih =>
      simp only [List.flatMap_cons, List.length_append, Encoding.length_frame,
        MatrixWordEncoding.word_length, ih, List.length_cons]
      ring

theorem matrixBits_length {α β : Type*} (p : ℕ) (rows : List α) (columns : List β)
    (entry : α → β → ZMod p) :
    (BlockCoefficientProgram.matrixBits p
      (ConstraintMatrixListEncoding.matrix p rows columns entry)).length =
      rows.length * columns.length * (2 * MatrixWordEncoding.width p + 1) := by
  rw [ConstraintMatrixListEncoding.matrixBits]
  induction rows with
  | nil => simp
  | cons row rows ih =>
      simp only [List.flatMap_cons, List.length_append, scalarRow_length, ih, List.length_cons]
      ring

end SubexponentialSAT.Subexp.ConstraintMatrixSizeBasics

end OAI.Algorithms
