import OAI.Geometry.Nikodym.Projective

noncomputable section
open Set
namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def linePiece (x v : E) (a b : ℝ) : Set (E × ℝ) :=
  {p | ∃ t ∈ Icc a b, p = (x+t • v,t)}

def transformedLinePiece (x v : E) (a b : ℝ) : Set (E × ℝ) :=
  {p | ∃ s ∈ Icc b⁻¹ a⁻¹, p = (v,0)+s • (x,1)}

def neighborhood {X : Type*} [PseudoMetricSpace X] (δ : ℝ) (A : Set X) : Set X :=
  {p | ∃ q ∈ A, dist p q < δ}

theorem isOpen_neighborhood {X : Type*} [PseudoMetricSpace X] (δ : ℝ) (A : Set X) :
    IsOpen (neighborhood δ A) := by
  have he : neighborhood δ A = ⋃ q ∈ A, Metric.ball q δ := by
    ext p
    simp only [neighborhood, mem_ofPred_eq, mem_iUnion, Metric.mem_ball, exists_prop]
  rw [he]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball

theorem projective_linePiece {x v : E} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    projective '' linePiece x v a b = transformedLinePiece x v a b := by
  ext p
  constructor
  · rintro ⟨q,⟨t,ht,rfl⟩,rfl⟩
    refine ⟨t⁻¹,⟨inv_anti₀ (ha.trans_le ht.1) ht.2,inv_anti₀ ha ht.1⟩,?_⟩
    exact projective_line x v (ha.trans_le ht.1).ne'
  · rintro ⟨s,hs,rfl⟩
    have hb : 0 < b := ha.trans_le hab
    have hs0 : 0 < s := (inv_pos.mpr hb).trans_le hs.1
    refine ⟨(x+s⁻¹ • v,s⁻¹),⟨s⁻¹,?_,rfl⟩,?_⟩
    · constructor
      · simpa only [inv_inv] using inv_anti₀ hs0 hs.2
      · simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hb) hs.1
    · simpa only [inv_inv] using projective_line x v (inv_ne_zero hs0.ne')

theorem norm_line_first_le {x v : E} {a b X V t : ℝ}
    (ha : 0 ≤ a) (ht : t ∈ Icc a b) (hx : ‖x‖ ≤ X) (hv : ‖v‖ ≤ V) :
    ‖x+t • v‖ ≤ X+b*V := by
  have ht0 : 0 ≤ t := ha.trans ht.1
  calc
    _ ≤ ‖x‖+‖t • v‖ := norm_add_le _ _
    _ = ‖x‖+t*‖v‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
    _ ≤ X+b*V := add_le_add hx (mul_le_mul ht.2 hv (norm_nonneg _) (ht0.trans ht.2))

/-- Rounded tubes on a positive time strip are sent into comparable
rounded tubes around the projectively transformed line piece. -/
theorem projective_neighborhood_linePiece {x v : E} {a b X V δ : ℝ}
    (ha : 0 < a) (hX : 0 ≤ X) (hV : 0 ≤ V) (hx : ‖x‖ ≤ X) (hv : ‖v‖ ≤ V)
    (hδ : 0 < δ) (hδa : δ ≤ a/2) :
    projective '' neighborhood δ (linePiece x v a b) ⊆
      neighborhood (((a/2)⁻¹+(X+b*V+1)/(a/2)^2)*δ)
        (transformedLinePiece x v a b) := by
  rintro p ⟨q,⟨w,⟨t,ht,rfl⟩,hq⟩,rfl⟩
  have ht0 : 0 < t := ha.trans_le ht.1
  have hat : a ≤ t := ht.1
  have hb0 : 0 ≤ b := ht0.le.trans ht.2
  have hqtime : |q.2-t| < δ := by
    apply lt_of_le_of_lt _ hq
    rw [dist_eq_norm,Prod.norm_def]
    exact le_max_right _ _
  have hqt : a/2 ≤ |q.2| := by
    have h := (abs_lt.mp hqtime).1
    have hqpos : 0 < q.2 := by linarith
    rw [abs_of_pos hqpos]
    linarith
  have htabs : a/2 ≤ |t| := by rw [abs_of_pos ht0]; linarith
  have hR : 0 ≤ X+b*V := by positivity
  have hC : 0 < (a/2)⁻¹+(X+b*V+1)/(a/2)^2 := by positivity
  refine ⟨projective (x+t • v,t),?_,?_⟩
  · refine ⟨t⁻¹,⟨inv_anti₀ ht0 ht.2,inv_anti₀ ha ht.1⟩,projective_line x v ht0.ne'⟩
  · exact (dist_projective_le (by linarith : 0 < a/2) hR q (x+t • v,t)
      hqt htabs (norm_line_first_le ha.le ht hx hv)).trans_lt
        (mul_lt_mul_of_pos_left hq hC)

theorem normalized_neighborhood_in_strip {x v : E} {X V δ : ℝ}
    (hx : ‖x‖ ≤ X) (hv : ‖v‖ ≤ V) (hδ : δ ≤ 1/2) :
    ∀ p ∈ neighborhood δ (linePiece x v 1 2),
      (1/2 : ℝ) ≤ |p.2| ∧ |p.2| ≤ 3 ∧ ‖p.1‖ ≤ X+2*V+1 := by
  rintro p ⟨q,⟨t,ht,rfl⟩,hp⟩
  have ht1 : 1 ≤ t := ht.1
  have ht2 : t ≤ 2 := ht.2
  have htime : |p.2-t| < δ := by
    apply lt_of_le_of_lt _ hp
    rw [dist_eq_norm,Prod.norm_def]
    exact le_max_right _ _
  have hfst : ‖p.1-(x+t • v)‖ < δ := by
    apply lt_of_le_of_lt _ hp
    rw [dist_eq_norm,Prod.norm_def]
    exact le_max_left _ _
  have hlow := (abs_lt.mp htime).1
  have hhigh := (abs_lt.mp htime).2
  have hpos : 0 < p.2 := by linarith
  rw [abs_of_pos hpos]
  refine ⟨by linarith,by linarith,?_⟩
  calc
    ‖p.1‖ ≤ ‖p.1-(x+t • v)‖+‖x+t • v‖ := norm_le_norm_sub_add _ _
    _ ≤ δ+(X+2*V) := add_le_add hfst.le (norm_line_first_le (by norm_num) ht hx hv)
    _ ≤ X+2*V+1 := by linarith

end OAI.Geometry.Nikodym
