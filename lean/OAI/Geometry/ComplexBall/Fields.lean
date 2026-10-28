import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

/-! # Fields -/

namespace OAI.Geometry.ComplexBall.Fields.ArithmeticQuotient

noncomputable section

/-! Weak approximation and the definite-place argument for the actual diagonal
form in ArithmeticQuotient. No normalization or arithmetic-group assertion is assumed here. -/

open scoped BigOperators Classical
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData _root_.NumberField

universe u

/-- WeakApproximation, with its original completion-valued conclusion. -/
def WeakApproximationInput (E : Type u) [Field E] [NumberField E] : Prop :=
  ∀ {ι : Type u} [Finite ι] (v : ι → AbsoluteValue E ℝ),
    (∀ i, (v i).IsNontrivial) →
    (Pairwise fun i j => ¬ (v i).IsEquiv (v j)) →
    DenseRange (fun x : E => fun i : ι => (x : (v i).Completion))

variable {E : Type u} [Field E] [NumberField E] [NumberField.IsCMField E]

omit [NumberField E] [NumberField.IsCMField E] in
lemma complexHermitian_self_re (b : E) (μ : E →+* ℂ) (x : ArithmeticQuotientEquationsData.Vec ℂ) :
    (ArithmeticQuotientEquationsData.complexHermitian b μ x x).re =
      Complex.normSq (x 0) + Complex.normSq (x 1) +
        (μ b).re * Complex.normSq (x 2) := by
  simp [ArithmeticQuotientEquationsData.complexHermitian, Fin.sum_univ_succ, Complex.mul_re,
    Complex.mul_im, Complex.normSq_apply]
  ring

lemma hermitian_axis (b : E) (x : ArithmeticQuotientEquationsData.Vec E) (i : Fin 3) :
    ArithmeticQuotientEquationsData.hermitian b x (Pi.single i 1) = (if i = 2 then b else 1) * x i := by
  by_cases hi : i = 2 <;> simp [ArithmeticQuotientEquationsData.hermitian, Pi.single_apply, apply_ite, hi]

lemma hermitian_nondegenerate (b : E) (hb : b ≠ 0) (x : ArithmeticQuotientEquationsData.Vec E)
    (hx : ∀ y : ArithmeticQuotientEquationsData.Vec E, ArithmeticQuotientEquationsData.hermitian b x y = 0) : x = 0 := by
  ext i
  have h := hx (Pi.single i 1)
  rw [hermitian_axis] at h
  have hc : (if i = 2 then b else 1) ≠ 0 := by split_ifs <;> simp_all
  exact (mul_eq_zero.mp h).resolve_left hc

lemma embedding_hermitian (b : E) (ν : E →+* ℂ) (x y : ArithmeticQuotientEquationsData.Vec E) :
    ν (ArithmeticQuotientEquationsData.hermitian b x y) =
      ArithmeticQuotientEquationsData.complexHermitian b ν (fun i => ν (x i)) (fun i => ν (y i)) := by
  simp only [ArithmeticQuotientEquationsData.hermitian, ArithmeticQuotientEquationsData.complexHermitian, map_sum, map_mul, apply_ite,
    map_one, IsCMField.complexEmbedding_complexConj]
  rfl

omit [NumberField E] [NumberField.IsCMField E] in
lemma positive_definite_at_embedding (b : E) (ν : E →+* ℂ)
    (hb : 0 < (ν b).re) (x : ArithmeticQuotientEquationsData.Vec ℂ) (hx : x ≠ 0) :
    0 < (ArithmeticQuotientEquationsData.complexHermitian b ν x x).re := by
  rw [complexHermitian_self_re]
  have h0 := Complex.normSq_nonneg (x 0)
  have h1 := Complex.normSq_nonneg (x 1)
  have h2 := mul_nonneg hb.le (Complex.normSq_nonneg (x 2))
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hp := Complex.normSq_pos.mpr hi
  fin_cases i
  · change 0 < Complex.normSq (x 0) at hp
    linarith
  · change 0 < Complex.normSq (x 1) at hp
    linarith
  · change 0 < Complex.normSq (x 2) at hp
    have hh := mul_pos hb hp
    linarith

/-- A definite embedding rules out nonzero isotropic vectors over E. -/
lemma anisotropic_of_definite_embedding (b : E) (ν : E →+* ℂ)
    (hb : 0 < (ν b).re) (x : ArithmeticQuotientEquationsData.Vec E) (hx : ArithmeticQuotientEquationsData.hermitian b x x = 0) : x = 0 := by
  by_contra hn
  have hnx : (fun i => ν (x i)) ≠ (0 : ArithmeticQuotientEquationsData.Vec ℂ) := by
    intro h
    apply hn
    ext i
    exact ν.injective (by simpa using congrFun h i)
  have hp := positive_definite_at_embedding b ν hb _ hnx
  rw [← embedding_hermitian, hx, map_zero] at hp
  exact (lt_irrefl 0) hp

omit [NumberField E] [NumberField.IsCMField E] in
lemma different_infinite_place (μ ν : E →+* ℂ)
    (hν : ν ≠ μ) (hνc : ν ≠ (starRingEnd ℂ).comp μ) :
    InfinitePlace.mk ν ≠ InfinitePlace.mk μ := by
  intro h
  rcases InfinitePlace.mk_eq_iff.mp h with h | h
  · exact hν h
  · apply hνc
    ext x
    have hx := congrArg (fun f : E →+* ℂ => star (f x)) h
    simpa using hx

/-- A single coefficient realizes the prescribed signs. The symmetrization
`x + c(x)` lies in E⁺ and preserves the approximated real-part signs. -/
theorem exists_signature_coefficient (hWeakApproximation : WeakApproximationInput E)
    (μ : E →+* ℂ) :
    ∃ b : E, IsCMField.complexConj E b = b ∧ b ≠ 0 ∧
      (μ b).re < 0 ∧
      ∀ ν : E →+* ℂ, ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ →
        0 < (ν b).re := by
  let t : InfinitePlace E → E := fun w => if w = InfinitePlace.mk μ then -1 else 1
  let O : Set ((w : InfinitePlace E) → w.val.Completion) :=
    {z | ∀ w, dist (z w) (t w : w.val.Completion) < (1 / 2 : ℝ)}
  have hO : IsOpen O := by
    simp only [O, Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro w
    exact isOpen_lt ((continuous_apply w).dist continuous_const) continuous_const
  have hOn : O.Nonempty := ⟨fun w => (t w : w.val.Completion), by
    intro w
    simp⟩
  have hd := hWeakApproximation (fun w : InfinitePlace E => w.val)
    (fun w => w.isNontrivial)
    (fun v w h => (InfinitePlace.eq_iff_isEquiv (K := E)).not.mp h)
  obtain ⟨x, hx⟩ := hd.exists_mem_open hO hOn
  have hn (ν : E →+* ℂ) :
      ‖ν x - ν (t (InfinitePlace.mk ν))‖ < (1 / 2 : ℝ) := by
    have h := hx (InfinitePlace.mk ν)
    change dist
      ((WithAbs.toAbs (InfinitePlace.mk ν).val x : WithAbs (InfinitePlace.mk ν).val) :
        (InfinitePlace.mk ν).val.Completion)
      ((WithAbs.toAbs (InfinitePlace.mk ν).val (t (InfinitePlace.mk ν)) :
        WithAbs (InfinitePlace.mk ν).val) :
        (InfinitePlace.mk ν).val.Completion) < (1 / 2 : ℝ) at h
    rw [UniformSpace.Completion.dist_eq, dist_eq_norm] at h
    change ‖ν (x - t (InfinitePlace.mk ν))‖ < (1 / 2 : ℝ) at h
    simpa only [map_sub] using h
  have hμ : (μ x).re < 0 := by
    have h := (Complex.abs_re_le_norm _).trans_lt (hn μ)
    simp only [t, ite_eq_left rfl, map_neg, map_one, sub_neg_eq_add,
      Complex.add_re, Complex.one_re] at h
    have hh := (abs_lt.mp h).2
    linarith
  have hν (ν : E →+* ℂ) (hν : ν ≠ μ)
      (hνc : ν ≠ (starRingEnd ℂ).comp μ) : 0 < (ν x).re := by
    have h := (Complex.abs_re_le_norm _).trans_lt (hn ν)
    simp only [t, ite_eq_right (different_infinite_place μ ν hν hνc), map_one,
      Complex.sub_re, Complex.one_re] at h
    have hh := (abs_lt.mp h).1
    linarith
  let b := x + IsCMField.complexConj E x
  have hb (ν : E →+* ℂ) : (ν b).re = 2 * (ν x).re := by
    simp only [b, map_add, IsCMField.complexEmbedding_complexConj,
      Complex.add_re]
    change (ν x).re + (ν x).re = _
    ring
  have hbμ : (μ b).re < 0 := by rw [hb]; linarith
  refine ⟨b, ?_, ?_, hbμ, ?_⟩
  · simp [b, map_add, IsCMField.complexConj_apply_apply, add_comm]
  · intro h
    simp [h] at hbμ
  · intro ν hv hvc
    rw [hb]
    exact mul_pos (by norm_num) (hν ν hv hvc)

/-- The entire coefficient and anisotropy portion of ArithmeticQuotient, conditional on WeakApproximation. -/
theorem exists_anisotropic_signature (hWeakApproximation : WeakApproximationInput E)
    (μ : E →+* ℂ)
    (h_other_place : ∃ ν : E →+* ℂ, ν ≠ μ ∧ ν ≠ (starRingEnd ℂ).comp μ) :
    ∃ b : E, IsCMField.complexConj E b = b ∧ b ≠ 0 ∧
      (μ b).re < 0 ∧
      (∀ ν : E →+* ℂ, ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ → 0 < (ν b).re) ∧
      (∀ x : ArithmeticQuotientEquationsData.Vec E, (∀ y : ArithmeticQuotientEquationsData.Vec E, ArithmeticQuotientEquationsData.hermitian b x y = 0) → x = 0) ∧
      (∀ x : ArithmeticQuotientEquationsData.Vec E, ArithmeticQuotientEquationsData.hermitian b x x = 0 → x = 0) := by
  obtain ⟨b, hbc, hb, hμ, hs⟩ := exists_signature_coefficient hWeakApproximation μ
  obtain ⟨ν, hν, hνc⟩ := h_other_place
  exact ⟨b, hbc, hb, hμ, hs, hermitian_nondegenerate b hb,
    anisotropic_of_definite_embedding b ν (hs ν hν hνc)⟩

end

end OAI.Geometry.ComplexBall.Fields.ArithmeticQuotient
