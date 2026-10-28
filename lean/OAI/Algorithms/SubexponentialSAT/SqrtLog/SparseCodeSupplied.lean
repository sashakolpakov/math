import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeConstruct

namespace OAI.Algorithms

/-! The sparse-code assembly accepts any successful physical search output.
It does not require agreement with the semantic search enumeration order.
Physical serializers must emit the local incidence slots, rather than all
columns of these extensional matrices. -/
namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

abbrev SuppliedShifts (m B : ℕ) := Fin (degree m B) → Cayley.Cube (dimension m B)
abbrev SuppliedLocal (m B : ℕ) := CheckMatrix (Fin (localRows m B)) (Fin (degree m B))

def suppliedMatrix (m B : ℕ) (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B) :
    CheckMatrix (Fin (totalRows m B)) (Fin m) :=
  fun r c => (Cayley.graph s).matrix Q (rowEquiv m B r) (columnEmbedding m B hm hB c)

def suppliedRows (m B : ℕ) (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B) : List (Fin m → F3) :=
  List.ofFn (suppliedMatrix m B hm hB s Q)

theorem suppliedMatrix_distance {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
    (hs : WalshExistence.Good (gapDenom m B) s)
    (hQ : HasDistance Q (degree m B / (100 * B * logSize m) + 1)) :
    HasRelativeDistance (suppliedMatrix m B hm hB s Q)
      (1 / (distanceDenom m B : ℝ)) := by
  have hlocal := LocalCode.relative_of_log_distance hB (logSize_pos m) Q hQ
  have hwalsh := (WalshExistence.good_iff_smallWalsh (gapDenom_pos m hB) s).mp hs
  have hmix := Cayley.hasMixing_of_smallWalsh s (1 / (gapDenom m B : ℝ))
    (by positivity) hwalsh
  have hV : 0 < Fintype.card (Cayley.Cube (dimension m B)) := Fintype.card_pos
  have hP : 0 < Fintype.card (Fin (degree m B)) := by simpa using degree_pos hm hB
  have hglobal := (Cayley.graph s).matrix_relativeDistance hV hP
    (by positivity : (0 : ℝ) ≤ 1 / (100 * (B : ℝ) * logSize m)) hlocal hmix
  rw [relative_fraction m hB] at hglobal
  have hshort := relativeDistance_shorten _ (columnEmbedding m B hm hB)
    (by positivity : (0 : ℝ) ≤ 1 / (distanceDenom m B : ℝ)) hglobal
  intro w hw hw0
  apply hshort w _ hw0
  intro r
  obtain ⟨i,rfl⟩ := (rowEquiv m B).surjective r
  exact hw i

/-- The physical serializer may enumerate or reverse the rows in any order.
Coverage is sufficient; no agreement with rowEquiv's list order is assumed. -/
theorem supplied_kernel_bound_of_coverage {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
    (hs : WalshExistence.Good (gapDenom m B) s)
    (hQ : HasDistance Q (degree m B / (100 * B * logSize m) + 1))
    (rs : List (Fin m → F3))
    (hcover : ∀ i, suppliedMatrix m B hm hB s Q i ∈ rs)
    (w : Fin m → F3) (hw : ∀ r ∈ rs, (∑ c, r c*w c)=0) (hw0 : w≠0) :
    m ≤ distanceDenom m B*weight w := by
  have hc : IsCodeword (suppliedMatrix m B hm hB s Q) w := fun i => hw _ (hcover i)
  simpa only [Fintype.card_fin] using relativeDistance_integer (distanceDenom_pos m hB)
    (suppliedMatrix_distance hm hB s Q hs hQ) w hc hw0

theorem suppliedRows_kernel_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B)
    (hs : WalshExistence.Good (gapDenom m B) s)
    (hQ : HasDistance Q (degree m B / (100 * B * logSize m) + 1))
    (w : Fin m → F3)
    (hw : ∀ r ∈ suppliedRows m B hm hB s Q, (∑ c, r c * w c) = 0)
    (hw0 : w ≠ 0) : m ≤ distanceDenom m B * weight w := by
  have hc : IsCodeword (suppliedMatrix m B hm hB s Q) w := by
    intro r
    exact hw _ (List.mem_ofFn.mpr ⟨r,rfl⟩)
  simpa only [Fintype.card_fin] using relativeDistance_integer (distanceDenom_pos m hB)
    (suppliedMatrix_distance hm hB s Q hs hQ) w hc hw0

theorem suppliedRows_length_le {n m B : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hB : 0 < B) (hmb : m ≤ n*B) (s : SuppliedShifts m B) (Q : SuppliedLocal m B) :
    (suppliedRows m B hm hB s Q).length ≤ 3*n := by
  unfold suppliedRows
  change (List.ofFn (fun i : Fin (totalRows m B) =>
    suppliedMatrix m B hm hB s Q i)).length ≤ 3 * n
  rw [List.length_ofFn]
  exact totalRows_le hn hm hB hmb

theorem suppliedMatrix_row_support {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (s : SuppliedShifts m B) (Q : SuppliedLocal m B) (r : Fin (totalRows m B)) :
    weight (suppliedMatrix m B hm hB s Q r) ≤ degreeBound m B := by
  have hshort := rowSupport_shorten_card_le ((Cayley.graph s).matrix Q)
    (columnEmbedding m B hm hB) (rowEquiv m B r)
  have hfull := (Cayley.graph s).matrix_rowSupport_card_le Q (rowEquiv m B r)
  exact (hshort.trans (by simpa using hfull)).trans (degree_le_bound m B)

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
