import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeTanner

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode.PortGraph

open scoped BigOperators

variable {V P R : Type*} [Fintype V] [Fintype P]
    [DecidableEq V] [DecidableEq P]

/-- One explicit check row for each vertex and each local check, on both
sides of the bipartite graph. -/
def matrix (G : PortGraph V P) (Q : CheckMatrix R P) :
    CheckMatrix ((V × R) ⊕ (V × R)) (V × P)
  | Sum.inl (v, r), e => if e.1 = v then Q r e.2 else 0
  | Sum.inr (v, r), e => if (G.rotation e).1 = v then Q r (G.rotation e).2 else 0

omit [DecidableEq P] in
@[simp] theorem check_matrix_left (G : PortGraph V P) (Q : CheckMatrix R P)
    (w : V × P → F3) (v : V) (r : R) :
    check (G.matrix Q) w (Sum.inl (v, r)) = check Q (leftWord w v) r := by
  simp [check, matrix, Fintype.sum_prod_type, leftWord, ite_mul]

omit [DecidableEq P] in
@[simp] theorem check_matrix_right (G : PortGraph V P) (Q : CheckMatrix R P)
    (w : V × P → F3) (v : V) (r : R) :
    check (G.matrix Q) w (Sum.inr (v, r)) = check Q (G.rightWord w v) r := by
  calc
    _ = ∑ e : V × P, (if e.1 = v then Q r e.2 else 0) * w (G.rotation.symm e) := by
      simpa [check, matrix] using
        G.rotation.sum_comp
          (fun e : V × P => (if e.1 = v then Q r e.2 else 0) * w (G.rotation.symm e))
    _ = _ := by simp [check, rightWord, Fintype.sum_prod_type, ite_mul]

omit [DecidableEq P] in
theorem isCodeword_matrix_iff (G : PortGraph V P) (Q : CheckMatrix R P)
    (w : V × P → F3) : IsCodeword (G.matrix Q) w ↔ G.IsTannerCodeword Q w := by
  constructor
  · intro hw
    constructor
    · intro v r
      simpa using hw (Sum.inl (v, r))
    · intro v r
      simpa using hw (Sum.inr (v, r))
  · rintro ⟨hleft, hright⟩ r
    rcases r with ⟨v, r⟩ | ⟨v, r⟩
    · exact (check_matrix_left G Q w v r).trans (hleft v r)
    · exact (check_matrix_right G Q w v r).trans (hright v r)

omit [DecidableEq P] in
theorem matrix_relativeDistance (G : PortGraph V P) {Q : CheckMatrix R P}
    {δ ε : ℝ} (hV : 0 < Fintype.card V) (hP : 0 < Fintype.card P)
    (hδ : 0 ≤ δ) (hQ : HasRelativeDistance Q δ) (hG : G.HasMixing ε) :
    HasRelativeDistance (G.matrix Q) (δ * (δ - ε)) := by
  intro w hw hw0
  have ht := G.tanner_distance hV hP hδ hQ hG w
    ((G.isCodeword_matrix_iff Q w).mp hw) hw0
  simpa only [Fintype.card_prod, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using ht

theorem left_rowSupport_subset (G : PortGraph V P) (Q : CheckMatrix R P)
    (v : V) (r : R) :
    rowSupport (G.matrix Q) (Sum.inl (v, r)) ⊆
      Finset.univ.image (fun p : P => (v, p)) := by
  intro e he
  have hh := (mem_support _ e).mp he
  have hev : e.1 = v := by
    by_contra hne
    exact hh (by simp [matrix, hne])
  refine Finset.mem_image.mpr ⟨e.2, Finset.mem_univ _, ?_⟩
  exact Prod.ext hev.symm rfl

theorem right_rowSupport_subset (G : PortGraph V P) (Q : CheckMatrix R P)
    (v : V) (r : R) :
    rowSupport (G.matrix Q) (Sum.inr (v, r)) ⊆
      Finset.univ.image (fun p : P => G.rotation.symm (v, p)) := by
  intro e he
  have hh := (mem_support _ e).mp he
  have hev : (G.rotation e).1 = v := by
    by_contra hne
    exact hh (by simp [matrix, hne])
  refine Finset.mem_image.mpr ⟨(G.rotation e).2, Finset.mem_univ _, ?_⟩
  have hp : (v, (G.rotation e).2) = G.rotation e := Prod.ext hev.symm rfl
  simp [hp]

theorem matrix_rowSupport_card_le (G : PortGraph V P) (Q : CheckMatrix R P)
    (r : (V × R) ⊕ (V × R)) :
    (rowSupport (G.matrix Q) r).card ≤ Fintype.card P := by
  rcases r with ⟨v, r⟩ | ⟨v, r⟩
  · exact (Finset.card_le_card (G.left_rowSupport_subset Q v r)).trans
      (Finset.card_image_le.trans_eq (by simp))
  · exact (Finset.card_le_card (G.right_rowSupport_subset Q v r)).trans
      (Finset.card_image_le.trans_eq (by simp))

omit [DecidableEq V] in
theorem matrix_row_count [Fintype R] :
    Fintype.card ((V × R) ⊕ (V × R)) = 2 * Fintype.card V * Fintype.card R := by
  simp only [Fintype.card_sum, Fintype.card_prod]
  ring

theorem matrix_totalSupport_le [Fintype R] (G : PortGraph V P) (Q : CheckMatrix R P) :
    (∑ r, (rowSupport (G.matrix Q) r).card) ≤
      2 * Fintype.card V * Fintype.card R * Fintype.card P := by
  calc
    _ ≤ ∑ _r : (V × R) ⊕ (V × R), Fintype.card P :=
      Finset.sum_le_sum (fun r _ => G.matrix_rowSupport_card_le Q r)
    _ = Fintype.card ((V × R) ⊕ (V × R)) * Fintype.card P := by simp
    _ = _ := by rw [matrix_row_count]

omit [Fintype P] [DecidableEq P] in
theorem matrix_columnSupport_card_le [Fintype R] [DecidableEq R]
    (G : PortGraph V P) (Q : CheckMatrix R P) (e : V × P) :
    (columnSupport (G.matrix Q) e).card ≤ 2 * Fintype.card R := by
  let L : Finset ((V × R) ⊕ (V × R)) :=
    Finset.univ.image fun r : R => Sum.inl (e.1, r)
  let T : Finset ((V × R) ⊕ (V × R)) :=
    Finset.univ.image fun r : R => Sum.inr ((G.rotation e).1, r)
  have hs : columnSupport (G.matrix Q) e ⊆ L ∪ T := by
    intro a ha
    have hne := (mem_support _ a).mp ha
    rcases a with ⟨v, r⟩ | ⟨v, r⟩
    · have hv : e.1 = v := by
        by_contra hn
        exact hne (by simp [matrix, hn])
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, by simp [hv]⟩
    · have hv : (G.rotation e).1 = v := by
        by_contra hn
        exact hne (by simp [matrix, hn])
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, by simp [hv]⟩
  have hL : L.card ≤ Fintype.card R := Finset.card_image_le.trans_eq (by simp)
  have hT : T.card ≤ Fintype.card R := Finset.card_image_le.trans_eq (by simp)
  exact (Finset.card_le_card hs).trans
    ((Finset.card_union_le L T).trans (by omega))

end SubexponentialSAT.SqrtLog.SparseCode.PortGraph

end OAI.Algorithms
