import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeMatrix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeShorten
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CayleyGraph
import OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistenceEnumeration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCodeSearch

namespace OAI.Algorithms

/-!
# Explicit sparse parity-check constructor

Every choice below is executable: two finite searches, arithmetic index
equivalences, and restriction to the first input columns. The hypotheses of
the local-code and Walsh existence lemmas are discharged by the parameter
bounds. No code or expander is supplied as an assumption to the final rows.
-/

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

def edgeEquiv (r D : ℕ) : Fin (2 ^ r * D) ≃ Cayley.Cube r × Fin D :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (WalshExistence.cubeEquiv r) (Equiv.refl (Fin D)))

def rowEquiv (m B : ℕ) : Fin (totalRows m B) ≃
    (Cayley.Cube (dimension m B) × Fin (localRows m B)) ⊕
    (Cayley.Cube (dimension m B) × Fin (localRows m B)) :=
  (finCongr (by unfold totalRows; ring)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr (edgeEquiv (dimension m B) (localRows m B))
        (edgeEquiv (dimension m B) (localRows m B))))

def columnEmbedding (m B : ℕ) (hm : 0 < m) (hB : 0 < B) :
    Fin m ↪ Cayley.Cube (dimension m B) × Fin (degree m B) :=
  (Fin.castLEEmb (graph_edge_lower hm hB)).trans
    (edgeEquiv (dimension m B) (degree m B)).toEmbedding

def chosenGraph (m B : ℕ) : PortGraph (Cayley.Cube (dimension m B)) (Fin (degree m B)) :=
  Cayley.graph (WalshExistence.construct (dimension m B) (degree m B) (gapDenom m B))

def chosenLocal (m B : ℕ) : CheckMatrix (Fin (localRows m B)) (Fin (degree m B)) :=
  LocalCode.localMatrix (degree m B) B (logSize m) (localRows m B)

theorem chosenLocal_distance (m : ℕ) {B : ℕ} (hB : 0 < B) :
    HasRelativeDistance (chosenLocal m B) (1 / (100 * (B : ℝ) * logSize m)) :=
  LocalCode.localMatrix_relativeDistance _ _ _ _ hB (logSize_pos m)
    (degree_le_power m B) (localRows_lower hB)

theorem chosenGraph_mixing {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    (chosenGraph m B).HasMixing (1 / (gapDenom m B : ℝ)) := by
  unfold chosenGraph
  apply Cayley.hasMixing_of_smallWalsh
  · positivity
  · by_cases hr : dimension m B = 0
    · have hz : ∀ r D q : ℕ, r = 0 →
          Cayley.SmallWalsh (WalshExistence.construct r D q) (1 / (q : ℝ)) := by
        intro r D q hr
        subst r
        exact WalshExistence.construct_smallWalsh_zero_dim D q
      exact hz _ _ _ hr
    · exact WalshExistence.construct_smallWalsh _ _ _ (gapDenom_pos m hB)
        (walsh_degree_bound hm hB hr)

def positiveMatrix (m B : ℕ) (hm : 0 < m) (hB : 0 < B) :
    CheckMatrix (Fin (totalRows m B)) (Fin m) :=
  fun r c => (chosenGraph m B).matrix (chosenLocal m B)
    (rowEquiv m B r) (columnEmbedding m B hm hB c)

theorem positiveMatrix_distance {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    HasRelativeDistance (positiveMatrix m B hm hB) (1 / (distanceDenom m B : ℝ)) := by
  have hV : 0 < Fintype.card (Cayley.Cube (dimension m B)) := Fintype.card_pos
  have hP : 0 < Fintype.card (Fin (degree m B)) := by simpa using degree_pos hm hB
  have hlocal := chosenLocal_distance m hB
  have hglobal := (chosenGraph m B).matrix_relativeDistance hV hP
    (by positivity : (0 : ℝ) ≤ 1 / (100 * (B : ℝ) * logSize m))
    hlocal (chosenGraph_mixing hm hB)
  rw [relative_fraction m hB] at hglobal
  have hshort := relativeDistance_shorten _ (columnEmbedding m B hm hB)
    (by positivity : (0 : ℝ) ≤ 1 / (distanceDenom m B : ℝ)) hglobal
  intro w hw hw0
  apply hshort w _ hw0
  intro r
  obtain ⟨i, rfl⟩ := (rowEquiv m B).surjective r
  exact hw i

theorem positiveMatrix_row_support {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (r : Fin (totalRows m B)) :
    weight (positiveMatrix m B hm hB r) ≤ degreeBound m B := by
  have hshort := rowSupport_shorten_card_le ((chosenGraph m B).matrix (chosenLocal m B))
    (columnEmbedding m B hm hB) (rowEquiv m B r)
  have hfull := (chosenGraph m B).matrix_rowSupport_card_le (chosenLocal m B) (rowEquiv m B r)
  exact (hshort.trans (by simpa using hfull)).trans (degree_le_bound m B)

/-- Total matrix constructor; zero columns and invalid B use the explicit
zero matrix. The final correctness theorem assumes B is positive. -/
def constructedMatrix (m B : ℕ) : CheckMatrix (Fin (totalRows m B)) (Fin m) :=
  if h : 0 < m ∧ 0 < B then positiveMatrix m B h.1 h.2 else 0

def rows (m B : ℕ) : List (Fin m → F3) := List.ofFn (constructedMatrix m B)

@[simp] theorem rows_length (m B : ℕ) : (rows m B).length = totalRows m B := by
  unfold rows
  exact List.length_ofFn

theorem rows_length_le {n m B : ℕ} (hn : 0 < n) (hB : 0 < B)
    (hmb : m ≤ n * B) : (rows m B).length ≤ 3 * n := by
  rw [rows_length]
  by_cases hm : 0 < m
  · exact totalRows_le hn hm hB hmb
  · have hzero : m = 0 := by omega
    subst m
    simp [totalRows, localRows, degree, dimension, dimensionFor]
    omega

theorem rows_row_support (m B : ℕ) (r : Fin m → F3) (hr : r ∈ rows m B) :
    weight r ≤ degreeBound m B := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  by_cases h : 0 < m ∧ 0 < B
  · simpa [constructedMatrix, h] using positiveMatrix_row_support h.1 h.2 i
  · simp only [constructedMatrix, dite_eq_right h]
    change weight (0 : Fin m → F3) ≤ degreeBound m B
    simp

theorem rows_accept_iff (m B : ℕ) (w : Fin m → F3) :
    (∀ r ∈ rows m B, (∑ c, r c * w c) = 0) ↔
      IsCodeword (constructedMatrix m B) w := by
  constructor
  · intro h r
    exact h (constructedMatrix m B r) (List.mem_ofFn.mpr ⟨r, rfl⟩)
  · intro h r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact h i

/-- Unconditional small-weight detection, stated in the integer form needed
by the tuple-sampler interface. -/
theorem rows_kernel_bound {m B : ℕ} (hB : 0 < B) (w : Fin m → F3)
    (hw : ∀ r ∈ rows m B, (∑ c, r c * w c) = 0) (hw0 : w ≠ 0) :
    m ≤ distanceDenom m B * weight w := by
  by_cases hm : 0 < m
  · have hc := (rows_accept_iff m B w).mp hw
    have hp : IsCodeword (positiveMatrix m B hm hB) w := by
      simpa [constructedMatrix, hm, hB] using hc
    simpa using relativeDistance_integer (distanceDenom_pos m hB)
      (positiveMatrix_distance hm hB) w hp hw0
  · omega

theorem list_weight_sum_le {m : ℕ} (rs : List (Fin m → F3)) (D : ℕ)
    (h : ∀ r ∈ rs, weight r ≤ D) : (rs.map weight).sum ≤ rs.length * D := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr := h r (by simp)
    have hs : ∀ x ∈ rs, weight x ≤ D := fun x hx => h x (by simp [hx])
    have hi := ih hs
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem rows_total_support {n m B : ℕ} (hn : 0 < n) (hB : 0 < B)
    (hmb : m ≤ n * B) :
    ((rows m B).map weight).sum ≤ 3 * n * degreeBound m B := by
  exact (list_weight_sum_le (rows m B) (degreeBound m B)
    (rows_row_support m B)).trans
      (Nat.mul_le_mul_right _ (rows_length_le hn hB hmb))

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
