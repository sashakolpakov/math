import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData
import OAI.Geometry.ComplexBall.Fields

/-! # Arithmetic Quotient Boost Ball -/

namespace OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall

noncomputable section

section

/-! The definite archimedean matrix group is compact in its actual matrix
topology. This proves the compact-real-place input from coordinate bounds. -/

open scoped BigOperators Classical _root_.Matrix.Norms.Elementwise
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData _root_.Topology

lemma complex_unitary_closed (b : ℂ) :
    IsClosed (ArithmeticQuotientEquationsData.unitarySubgroup (starRingEnd ℂ) b : Set (ArithmeticQuotientEquationsData.SL ℂ)) := by
  have he : (ArithmeticQuotientEquationsData.unitarySubgroup (starRingEnd ℂ) b : Set (ArithmeticQuotientEquationsData.SL ℂ)) =
      ⋂ i : Fin 3, ⋂ j : Fin 3,
        {g : ArithmeticQuotientEquationsData.SL ℂ | (∑ k, ArithmeticQuotientEquationsData.diagonalCoefficient b k * g k i * star (g k j)) =
          if i = j then ArithmeticQuotientEquationsData.diagonalCoefficient b i else 0} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact ArithmeticQuotientEquationsData.unitary_iff_columns _ b g
  rw [he]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_eq _ continuous_const
  fun_prop

lemma complex_matrix_closedEmbedding (b : ℂ) :
    IsClosedEmbedding (ArithmeticQuotientEquationsData.matrixOf (starRingEnd ℂ) b) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.comp
    (complex_unitary_closed b).isClosedEmbedding_subtypeVal

instance complexUnitaryT2 (b : ℂ) : T2Space (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) :=
  (complex_matrix_closedEmbedding b).isEmbedding.t2Space

instance complexUnitaryLocallyCompact (b : ℂ) :
    LocallyCompactSpace (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) := by
  let : LocallyCompactSpace (ArithmeticQuotientEquationsData.Mat ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℂ))
  exact (complex_matrix_closedEmbedding b).locallyCompactSpace

instance complexUnitarySecondCountable (b : ℂ) :
    SecondCountableTopology (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) := by
  let : SecondCountableTopology (ArithmeticQuotientEquationsData.Mat ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℂ))
  exact (complex_matrix_closedEmbedding b).isEmbedding.secondCountableTopology

lemma complex_column_norm (b : ℂ) (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (j : Fin 3) :
    Complex.normSq (g.val 0 j) + Complex.normSq (g.val 1 j) +
      b.re * Complex.normSq (g.val 2 j) = (ArithmeticQuotientEquationsData.diagonalCoefficient b j).re := by
  have h := (ArithmeticQuotientEquationsData.unitary_iff_columns _ b g.val).mp g.property j j
  have h' := congrArg Complex.re h
  have he := Fields.ArithmeticQuotient.complexHermitian_self_re b (RingHom.id ℂ) (fun i => g.val i j)
  exact he.symm.trans (by
    simpa only [ArithmeticQuotientEquationsData.complexHermitian, ArithmeticQuotientEquationsData.diagonalCoefficient, RingHom.id_apply,
      starRingEnd_apply, ↓reduceIte] using h')

lemma complex_unitary_bounded (b : ℂ) (hb : 0 < b.re) :
    Bornology.IsBounded (Set.range (ArithmeticQuotientEquationsData.matrixOf (starRingEnd ℂ) b)) := by
  let M := max 1 b.re
  let R := max 1 (max M (M / b.re))
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 ≤ R := le_trans zero_le_one hR1
  have hMR : M ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hdivR : M / b.re ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R, ?_⟩
  rintro _ ⟨g, rfl⟩
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro j
  have h0 := Complex.normSq_nonneg (g.val 0 j)
  have h1 := Complex.normSq_nonneg (g.val 1 j)
  have h2 := Complex.normSq_nonneg (g.val 2 j)
  have hc : (ArithmeticQuotientEquationsData.diagonalCoefficient b j).re ≤ M := by
    unfold ArithmeticQuotientEquationsData.diagonalCoefficient
    split_ifs
    · exact le_max_right _ _
    · exact le_max_left _ _
  have hcol := complex_column_norm b g j
  have hs : Complex.normSq (g.val i j) ≤ R := by
    fin_cases i
    · change Complex.normSq (g.val 0 j) ≤ R
      nlinarith [mul_nonneg hb.le h2]
    · change Complex.normSq (g.val 1 j) ≤ R
      nlinarith [mul_nonneg hb.le h2]
    · change Complex.normSq (g.val 2 j) ≤ R
      have hh : Complex.normSq (g.val 2 j) ≤ M / b.re := by
        apply (le_div_iff₀ hb).mpr
        nlinarith
      exact hh.trans hdivR
  rw [Complex.normSq_eq_norm_sq] at hs
  change ‖g.val i j‖ ≤ R
  nlinarith [sq_nonneg (R - 1)]

/-- Positive definiteness gives compactness of the complete real group. -/
theorem compact_complex_unitary_of_positive (b : ℂ) (hb : 0 < b.re) :
    CompactSpace (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) := by
  let : ProperSpace (ArithmeticQuotientEquationsData.Mat ℂ) := inferInstanceAs (ProperSpace (Fin 3 → Fin 3 → ℂ))
  have he := complex_matrix_closedEmbedding b
  have hc : IsCompact (Set.range (ArithmeticQuotientEquationsData.matrixOf (starRingEnd ℂ) b)) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨he.isClosed_range, complex_unitary_bounded b hb⟩
  constructor
  apply he.isEmbedding.isCompact_iff.mpr
  simpa only [Set.image_univ] using hc

end

section

/-! The negative-line domain in an affine chart. Its coordinate maps are
defined on the actual negative cone used in the ArithmeticQuotient specification. -/

open scoped BigOperators Classical _root_.Manifold
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData _root_.Topology

abbrev BallCoordinates := Fin 2 → ℂ
abbrev Cone (b : ℂ) := ArithmeticQuotientEquationsData.NegativeVectors b (RingHom.id ℂ)

def ballOpen (b : ℂ) : TopologicalSpace.Opens BallCoordinates :=
  ⟨{w | Complex.normSq (w 0) + Complex.normSq (w 1) < -b.re}, by
    apply isOpen_lt _ continuous_const
    fun_prop⟩

abbrev Ball (b : ℂ) := ↥(ballOpen b)

def liftVector (w : BallCoordinates) : ArithmeticQuotientEquationsData.Vec ℂ := ![w 0, w 1, 1]

lemma cone_last_ne_zero (b : ℂ) (z : Cone b) : z.val 2 ≠ 0 := by
  intro h
  have hn := z.property
  rw [Fields.ArithmeticQuotient.complexHermitian_self_re, h] at hn
  simp only [Complex.normSq_zero, mul_zero, add_zero] at hn
  exact (not_lt_of_ge (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))) hn

def liftBall (b : ℂ) (w : Ball b) : Cone b :=
  ⟨liftVector w.val, by
    rw [Fields.ArithmeticQuotient.complexHermitian_self_re]
    have hw := w.property
    change Complex.normSq (w.val 0) + Complex.normSq (w.val 1) < -b.re at hw
    change Complex.normSq (w.val 0) + Complex.normSq (w.val 1) +
      b.re * Complex.normSq (1 : ℂ) < 0
    rw [Complex.normSq_one, mul_one]
    linarith⟩

def normalize (b : ℂ) (z : Cone b) : Ball b :=
  ⟨fun i => z.val i.castSucc / z.val 2, by
    change Complex.normSq (z.val 0 / z.val 2) +
      Complex.normSq (z.val 1 / z.val 2) < -b.re
    rw [Complex.normSq_div, Complex.normSq_div, ← add_div]
    apply (div_lt_iff₀ (Complex.normSq_pos.mpr (cone_last_ne_zero b z))).mpr
    have hz := z.property
    rw [Fields.ArithmeticQuotient.complexHermitian_self_re] at hz
    change Complex.normSq (z.val 0) + Complex.normSq (z.val 1) +
      b.re * Complex.normSq (z.val 2) < 0 at hz
    linarith⟩

@[simp] lemma normalize_lift (b : ℂ) (w : Ball b) :
    normalize b (liftBall b w) = w := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [normalize, liftBall, liftVector]

lemma lift_normalize (b : ℂ) (z : Cone b) :
    (liftBall b (normalize b z)).val = (z.val 2)⁻¹ • z.val := by
  ext i
  fin_cases i
  · simp [liftBall, liftVector, normalize, div_eq_mul_inv, mul_comm]
  · simp [liftBall, liftVector, normalize, div_eq_mul_inv, mul_comm]
  · simp [liftBall, liftVector, cone_last_ne_zero b z]

lemma continuous_liftBall (b : ℂ) : Continuous (liftBall b) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun w : Ball b => w.val 0)
    exact (continuous_apply 0).comp continuous_subtype_val
  · change Continuous (fun w : Ball b => w.val 1)
    exact (continuous_apply 1).comp continuous_subtype_val
  · exact continuous_const

lemma continuous_normalize (b : ℂ) : Continuous (normalize b) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((continuous_apply i.castSucc).comp continuous_subtype_val).div
    ((continuous_apply 2).comp continuous_subtype_val) (cone_last_ne_zero b)

lemma ball_starConvex (b : ℂ) :
    StarConvex ℝ (0 : BallCoordinates) (ballOpen b : Set BallCoordinates) := by
  intro y hy a t ha ht hat
  have ht1 : t ≤ 1 := by linarith
  change Complex.normSq (y 0) + Complex.normSq (y 1) < -b.re at hy
  change Complex.normSq ((a • (0 : BallCoordinates) + t • y) 0) +
    Complex.normSq ((a • (0 : BallCoordinates) + t • y) 1) < -b.re
  simp only [smul_zero, zero_add, Pi.smul_apply, Complex.real_smul,
    Complex.normSq_mul, Complex.normSq_ofReal]
  have hq := add_nonneg (Complex.normSq_nonneg (y 0)) (Complex.normSq_nonneg (y 1))
  have htsq : t ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr htsq) hq]

lemma ball_pathConnected (b : ℂ) (hb : b.re < 0) :
    IsPathConnected (ballOpen b : Set BallCoordinates) := by
  apply (ball_starConvex b).isPathConnected
  change Complex.normSq 0 + Complex.normSq 0 < -b.re
  simpa using neg_pos.mpr hb

theorem ball_connected (b : ℂ) (hb : b.re < 0) : ConnectedSpace (Ball b) :=
  isConnected_iff_connectedSpace.mp (ball_pathConnected b hb).isConnected

end

section

/-! The actual special unitary action on the negative cone and on negative
lines. Equality of normalized vectors is exactly nonzero scalar equivalence. -/

open scoped BigOperators Classical
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

lemma form_star_eq_complex (b : ℂ) (x y : ArithmeticQuotientEquationsData.Vec ℂ) :
    ArithmeticQuotientEquationsData.form (starRingEnd ℂ) b x y = ArithmeticQuotientEquationsData.complexHermitian b (RingHom.id ℂ) x y := by
  simp [ArithmeticQuotientEquationsData.form, ArithmeticQuotientEquationsData.diagonalCoefficient, ArithmeticQuotientEquationsData.complexHermitian]

lemma normalize_eq_iff_scalar (b : ℂ) (z w : Cone b) :
    normalize b z = normalize b w ↔
      ∃ t : ℂ, t ≠ 0 ∧ w.val = t • z.val := by
  constructor
  · intro h
    refine ⟨w.val 2 / z.val 2, div_ne_zero (cone_last_ne_zero b w) (cone_last_ne_zero b z), ?_⟩
    have hc (i : Fin 2) : z.val i.castSucc / z.val 2 = w.val i.castSucc / w.val 2 :=
      congrArg (fun a : Ball b => a.val i) h
    have hc' (i : Fin 2) : w.val i.castSucc = (w.val 2 / z.val 2) * z.val i.castSucc := by
      calc
        w.val i.castSucc = (w.val i.castSucc / w.val 2) * w.val 2 :=
          (div_mul_cancel₀ _ (cone_last_ne_zero b w)).symm
        _ = (z.val i.castSucc / z.val 2) * w.val 2 := by rw [← hc]
        _ = (w.val 2 / z.val 2) * z.val i.castSucc := by ring
    ext i
    fin_cases i
    · exact hc' 0
    · exact hc' 1
    · exact (div_mul_cancel₀ _ (cone_last_ne_zero b z)).symm
  · rintro ⟨t, ht, h⟩
    apply Subtype.ext
    ext i
    change z.val i.castSucc / z.val 2 = w.val i.castSucc / w.val 2
    rw [h]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp

def coneAction (b : ℂ) (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (z : Cone b) : Cone b :=
  ⟨Matrix.SpecialLinearGroup.toLin' g.val z.val, by
    have hg := g.property z.val z.val
    rw [form_star_eq_complex, form_star_eq_complex] at hg
    rw [hg]
    exact z.property⟩

instance coneMulAction (b : ℂ) : MulAction (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (Cone b) where
  smul := coneAction b
  one_smul z := by
    apply Subtype.ext
    change Matrix.SpecialLinearGroup.toLin' (1 : ArithmeticQuotientEquationsData.SL ℂ) z.val = z.val
    rw [map_one]
    rfl
  mul_smul g h z := by
    apply Subtype.ext
    change Matrix.SpecialLinearGroup.toLin' (g.val * h.val) z.val =
      Matrix.SpecialLinearGroup.toLin' g.val (Matrix.SpecialLinearGroup.toLin' h.val z.val)
    rw [map_mul, LinearEquiv.mul_apply]

lemma cone_smul_val (b : ℂ) (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (z : Cone b) :
    (g • z).val = (ArithmeticQuotientEquationsData.matrixOf (starRingEnd ℂ) b g).mulVec z.val := rfl

lemma normalize_cone_smul_congr (b : ℂ) (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b)
    (z w : Cone b) (h : normalize b z = normalize b w) :
    normalize b (g • z) = normalize b (g • w) := by
  obtain ⟨t, ht, hw⟩ := (normalize_eq_iff_scalar b z w).mp h
  apply (normalize_eq_iff_scalar b _ _).mpr
  refine ⟨t, ht, ?_⟩
  change Matrix.SpecialLinearGroup.toLin' g.val w.val =
    t • Matrix.SpecialLinearGroup.toLin' g.val z.val
  rw [hw, map_smul]

instance ballMulAction (b : ℂ) : MulAction (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (Ball b) where
  smul g w := normalize b (g • liftBall b w)
  one_smul w := by
    change normalize b ((1 : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) • liftBall b w) = w
    rw [one_smul, normalize_lift]
  mul_smul g h w := by
    change normalize b ((g * h) • liftBall b w) =
      normalize b (g • liftBall b (normalize b (h • liftBall b w)))
    rw [mul_smul]
    apply normalize_cone_smul_congr
    exact (normalize_lift b _).symm

lemma normalize_equivariant (b : ℂ) (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (z : Cone b) :
    normalize b (g • z) = g • normalize b z := by
  change normalize b (g • z) = normalize b (g • liftBall b (normalize b z))
  apply normalize_cone_smul_congr
  exact (normalize_lift b _).symm

instance coneContinuousSMul (b : ℂ) : ContinuousSMul (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (Cone b) where
  continuous_smul := by
    apply Continuous.subtype_mk
    change Continuous (fun p : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b × Cone b =>
      (ArithmeticQuotientEquationsData.matrixOf (starRingEnd ℂ) b p.1).mulVec p.2.val)
    have hg : Continuous (fun p : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b × Cone b =>
        ArithmeticQuotientEquationsData.matrixOf (starRingEnd ℂ) b p.1) :=
      (complex_matrix_closedEmbedding b).continuous.comp continuous_fst
    exact hg.matrix_mulVec (continuous_subtype_val.comp continuous_snd)

instance ballContinuousSMul (b : ℂ) : ContinuousSMul (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (Ball b) where
  continuous_smul :=
    (continuous_normalize b).comp
      (continuous_fst.smul ((continuous_liftBall b).comp continuous_snd))

end

section

/-! Explicit special unitary matrices moving the ball origin to a given
point. The rank-one formula stays continuous at the origin. -/

open scoped Classical BigOperators
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

def ballNormSq (w : BallCoordinates) : ℝ := Complex.normSq (w 0) + Complex.normSq (w 1)

def boostRaw (w : BallCoordinates) (a t s : ℝ) : ArithmeticQuotientEquationsData.Mat ℂ :=
  !![1 + a * w 0 * star (w 0), a * w 0 * star (w 1), t * w 0;
    a * w 1 * star (w 0), 1 + a * w 1 * star (w 1), t * w 1;
    s * star (w 0), s * star (w 1), t]

lemma ballNormSq_complex (w : BallCoordinates) :
    (ballNormSq w : ℂ) = w 0 * star (w 0) + w 1 * star (w 1) := by
  simp [ballNormSq, Complex.mul_conj]

lemma boostRaw_det (w : BallCoordinates) (a t s : ℝ) :
    (boostRaw w a t s).det = (t * (1 + a * ballNormSq w) - s * t * ballNormSq w : ℝ) := by
  simp only [boostRaw, Matrix.det_fin_three]
  push_cast
  rw [ballNormSq_complex]
  simp
  ring

lemma boostRaw_column (w : BallCoordinates) (m a t s : ℝ)
    (ha : 2 * a + a ^ 2 * ballNormSq w = m * s ^ 2)
    (hat : t * (1 + a * ballNormSq w) = m * s * t)
    (hn : t ^ 2 * (ballNormSq w - m) = -m) (i j : Fin 3) :
    (∑ k, ArithmeticQuotientEquationsData.diagonalCoefficient (-(m : ℂ)) k * boostRaw w a t s k i *
      star (boostRaw w a t s k j)) = if i = j then ArithmeticQuotientEquationsData.diagonalCoefficient (-(m : ℂ)) i else 0 := by
  have ha' : (2 : ℂ) * a + (a : ℂ) ^ 2 * ballNormSq w = (m : ℂ) * (s : ℂ) ^ 2 := by exact_mod_cast ha
  have hat' : (t : ℂ) * (1 + (a : ℂ) * ballNormSq w) = (m : ℂ) * s * t := by exact_mod_cast hat
  have hn' : (t : ℂ) ^ 2 * ((ballNormSq w : ℂ) - m) = -(m : ℂ) := by exact_mod_cast hn
  rw [ballNormSq_complex] at ha' hat' hn'
  simp only [← starRingEnd_apply] at ha' hat' hn'
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, ArithmeticQuotientEquationsData.diagonalCoefficient, boostRaw]
  · linear_combination (w 0 * (starRingEnd ℂ) (w 0)) * ha'
  · linear_combination ((starRingEnd ℂ) (w 0) * w 1) * ha'
  · linear_combination (starRingEnd ℂ) (w 0) * hat'
  · linear_combination ((starRingEnd ℂ) (w 1) * w 0) * ha'
  · linear_combination (w 1 * (starRingEnd ℂ) (w 1)) * ha'
  · linear_combination (starRingEnd ℂ) (w 1) * hat'
  · linear_combination w 0 * hat'
  · linear_combination w 1 * hat'
  · linear_combination hn'

end

section

/-! The real coefficients in the continuous ball section. -/

def boostTime (m q : ℝ) : ℝ := Real.sqrt (m / (m - q))
def boostRank (m q : ℝ) : ℝ := boostTime m q ^ 2 / (m * (boostTime m q + 1))

lemma boostTime_pos (m q : ℝ) (hm : 0 < m) (hq : q < m) : 0 < boostTime m q :=
  Real.sqrt_pos.mpr (div_pos hm (sub_pos.mpr hq))

lemma boostTime_relation (m q : ℝ) (hm : 0 < m) (hq : q < m) :
    boostTime m q ^ 2 * (m - q) = m := by
  rw [boostTime, Real.sq_sqrt (le_of_lt (div_pos hm (sub_pos.mpr hq)))]
  exact div_mul_cancel₀ m (sub_pos.mpr hq).ne'

lemma boostRank_relation (m q : ℝ) (hm : 0 < m) (hq : q < m) :
    boostRank m q * q = boostTime m q - 1 := by
  have ht := boostTime_pos m q hm hq
  have hs := boostTime_relation m q hm hq
  have ht1 : boostTime m q + 1 ≠ 0 := by positivity
  dsimp [boostRank]
  field_simp
  nlinarith

lemma boost_parameters (m q : ℝ) (hm : 0 < m) (hq : q < m) :
    (2 * boostRank m q + boostRank m q ^ 2 * q = m * (boostTime m q / m) ^ 2) ∧
    (boostTime m q * (1 + boostRank m q * q) = m * (boostTime m q / m) * boostTime m q) ∧
    (boostTime m q ^ 2 * (q - m) = -m) ∧
    (boostTime m q * (1 + boostRank m q * q) -
      (boostTime m q / m) * boostTime m q * q = 1) := by
  have ht := boostTime_pos m q hm hq
  have hs := boostTime_relation m q hm hq
  have ha := boostRank_relation m q hm hq
  have ht1 : boostTime m q + 1 ≠ 0 := by positivity
  have hm0 := hm.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ = boostRank m q * (2 + boostRank m q * q) := by ring
      _ = boostRank m q * (boostTime m q + 1) := by rw [ha]; ring
      _ = m * (boostTime m q / m) ^ 2 := by
        dsimp [boostRank]
        field_simp
  · rw [ha]
    field_simp
    ring
  · nlinarith
  · rw [ha]
    field_simp
    nlinarith

end

section

/-! A continuous section of the orbit map from SU(2,1) to its negative-line
ball, using the explicit rank-one boost. -/

open scoped Classical
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData _root_.Topology

lemma real_negative_coefficient (b : ℂ) (hbim : b.im = 0) : b = -((-b.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [hbim]

def ballOrigin (b : ℂ) (hb : b.re < 0) : Ball b :=
  ⟨0, by change Complex.normSq 0 + Complex.normSq 0 < -b.re; simp; linarith⟩

def ballBoost (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0) (w : Ball b) : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b := by
  let m := -b.re
  let q := ballNormSq w.val
  have hm : 0 < m := neg_pos.mpr hb
  have hq : q < m := w.property
  let t := boostTime m q
  let a := boostRank m q
  have hp := boost_parameters m q hm hq
  let A : ArithmeticQuotientEquationsData.SL ℂ := ⟨boostRaw w.val a t (t / m), by
    rw [boostRaw_det]
    exact_mod_cast hp.2.2.2⟩
  refine ⟨A, (ArithmeticQuotientEquationsData.unitary_iff_columns _ b A).mpr ?_⟩
  intro i j
  have hc := boostRaw_column w.val m a t (t / m) hp.1 hp.2.1 hp.2.2.1 i j
  rw [← real_negative_coefficient b hbim] at hc
  exact hc

lemma ballBoost_matrix (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0) (w : Ball b) :
    (ballBoost b hbim hb w).val.val = boostRaw w.val
      (boostRank (-b.re) (ballNormSq w.val)) (boostTime (-b.re) (ballNormSq w.val))
      (boostTime (-b.re) (ballNormSq w.val) / (-b.re)) := rfl

lemma ballBoost_origin (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0) (w : Ball b) :
    ballBoost b hbim hb w • ballOrigin b hb = w := by
  have ht : (boostTime (-b.re) (ballNormSq w.val) : ℂ) ≠ 0 := by
    exact_mod_cast (boostTime_pos (-b.re) (ballNormSq w.val) (neg_pos.mpr hb) w.property).ne'
  apply Subtype.ext
  funext i
  change ((ballBoost b hbim hb w).val.val.mulVec (liftVector 0)) i.castSucc /
    ((ballBoost b hbim hb w).val.val.mulVec (liftVector 0)) 2 = w.val i
  rw [ballBoost_matrix]
  fin_cases i <;> simp [boostRaw, Matrix.mulVec, dotProduct, liftVector, Fin.sum_univ_succ, ht]

lemma continuous_ballNormSq : Continuous ballNormSq := by
  unfold ballNormSq
  fun_prop

lemma continuous_boostTime (b : ℂ) :
    Continuous (fun w : Ball b => boostTime (-b.re) (ballNormSq w.val)) := by
  unfold boostTime
  apply Continuous.sqrt
  apply Continuous.div continuous_const
  · exact continuous_const.sub (continuous_ballNormSq.comp continuous_subtype_val)
  · intro w
    exact (sub_pos.mpr w.property).ne'

lemma continuous_boostRank (b : ℂ) (hb : b.re < 0) :
    Continuous (fun w : Ball b => boostRank (-b.re) (ballNormSq w.val)) := by
  unfold boostRank
  apply Continuous.div ((continuous_boostTime b).pow 2)
  · exact continuous_const.mul ((continuous_boostTime b).add continuous_const)
  · intro w
    exact mul_ne_zero (neg_ne_zero.mpr hb.ne)
      (ne_of_gt (by have h := boostTime_pos (-b.re) (ballNormSq w.val) (neg_pos.mpr hb) w.property; linarith))

lemma continuous_ballBoost (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0) :
    Continuous (ballBoost b hbim hb) := by
  apply IsInducing.subtypeVal.continuous_iff.mpr
  apply IsInducing.subtypeVal.continuous_iff.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun w : Ball b => (ballBoost b hbim hb w).val.val i j)
  simp_rw [ballBoost_matrix]
  have ht : Continuous (fun w : Ball b => (boostTime (-b.re) (ballNormSq w.val) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_boostTime b)
  have ha : Continuous (fun w : Ball b => (boostRank (-b.re) (ballNormSq w.val) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_boostRank b hb)
  have hw (k : Fin 2) : Continuous (fun w : Ball b => w.val k) :=
    (continuous_apply k).comp continuous_subtype_val
  have hc (k : Fin 2) : Continuous (fun w : Ball b => (starRingEnd ℂ) (w.val k)) := (hw k).star
  fin_cases i <;> fin_cases j <;> simp [boostRaw]
  · exact continuous_const.add ((ha.mul (hw 0)).mul (hc 0))
  · exact (ha.mul (hw 0)).mul (hc 1)
  · exact ht.mul (hw 0)
  · exact (ha.mul (hw 1)).mul (hc 0)
  · exact continuous_const.add ((ha.mul (hw 1)).mul (hc 1))
  · exact ht.mul (hw 1)
  · exact (ht.div_const _).mul (hc 0)
  · exact (ht.div_const _).mul (hc 1)
  · exact ht

lemma ballAction_pretransitive (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0) :
    MulAction.IsPretransitive (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (Ball b) := by
  refine ⟨fun x y => ⟨ballBoost b hbim hb y * (ballBoost b hbim hb x)⁻¹, ?_⟩⟩
  conv_lhs => arg 2; rw [← ballBoost_origin b hbim hb x]
  rw [mul_smul, inv_smul_smul, ballBoost_origin]

end

section

/-! The stabilizer of the ball origin is compact, by explicit bounds on
its block-diagonal unitary matrices. -/

open scoped Classical BigOperators _root_.Matrix.Norms.Elementwise
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData _root_.Topology

lemma ball_smul_origin_coordinate (b : ℂ) (hb : b.re < 0)
    (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (i : Fin 2) :
    (g • ballOrigin b hb).val i = g.val i.castSucc 2 / g.val 2 2 := by
  change ((ArithmeticQuotientEquationsData.matrixOf (starRingEnd ℂ) b g).mulVec (liftVector 0)) i.castSucc /
    ((ArithmeticQuotientEquationsData.matrixOf (starRingEnd ℂ) b g).mulVec (liftVector 0)) 2 = _
  simp [Matrix.mulVec, dotProduct, liftVector, Fin.sum_univ_succ, ArithmeticQuotientEquationsData.matrixOf]

lemma unitary_last_entry_ne_zero (b : ℂ) (hb : b.re < 0) (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) :
    g.val 2 2 ≠ 0 := by
  have h := cone_last_ne_zero b (g • liftBall b (ballOrigin b hb))
  change ((ArithmeticQuotientEquationsData.matrixOf (starRingEnd ℂ) b g).mulVec (liftVector 0)) 2 ≠ 0 at h
  simpa [Matrix.mulVec, dotProduct, liftVector, Fin.sum_univ_succ, ArithmeticQuotientEquationsData.matrixOf] using h

lemma origin_stabilizer_last_column (b : ℂ) (hb : b.re < 0)
    (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (hg : g • ballOrigin b hb = ballOrigin b hb) (i : Fin 2) :
    g.val i.castSucc 2 = 0 := by
  have he := congrArg (fun w : Ball b => w.val i) hg
  rw [ball_smul_origin_coordinate] at he
  change g.val i.castSucc 2 / g.val 2 2 = 0 at he
  exact (div_eq_zero_iff.mp he).resolve_right (unitary_last_entry_ne_zero b hb g)

lemma origin_stabilizer_last_row (b : ℂ) (hb : b.re < 0)
    (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (hg : g • ballOrigin b hb = ballOrigin b hb) (i : Fin 2) :
    g.val 2 i.castSucc = 0 := by
  have h0 := origin_stabilizer_last_column b hb g hg 0
  have h1 := origin_stabilizer_last_column b hb g hg 1
  change g.val 0 2 = 0 at h0
  change g.val 1 2 = 0 at h1
  have h := (ArithmeticQuotientEquationsData.unitary_iff_columns _ b g.val).mp g.property 2 i.castSucc
  have hi : (2 : Fin 3) ≠ i.castSucc := by fin_cases i <;> decide
  simp [Fin.sum_univ_succ, ArithmeticQuotientEquationsData.diagonalCoefficient, h0, h1, hi] at h
  have hb0 : b ≠ 0 := by intro he; simp [he] at hb
  have hlast := unitary_last_entry_ne_zero b hb g
  exact h.resolve_left (not_or_intro hb0 hlast)

lemma origin_stabilizer_entry_norm_le (b : ℂ) (hb : b.re < 0)
    (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (hg : g • ballOrigin b hb = ballOrigin b hb) (i j : Fin 3) :
    ‖g.val i j‖ ≤ 1 := by
  have h0 := origin_stabilizer_last_column b hb g hg 0
  have h1 := origin_stabilizer_last_column b hb g hg 1
  change g.val 0 2 = 0 at h0
  change g.val 1 2 = 0 at h1
  have hr0 := origin_stabilizer_last_row b hb g hg 0
  have hr1 := origin_stabilizer_last_row b hb g hg 1
  change g.val 2 0 = 0 at hr0
  change g.val 2 1 = 0 at hr1
  have hj0 := complex_column_norm b g 0
  have hj1 := complex_column_norm b g 1
  have hj2 := complex_column_norm b g 2
  simp only [ArithmeticQuotientEquationsData.diagonalCoefficient, Fin.reduceEq, ↓reduceIte, Complex.one_re, hr0, hr1,
    h0, h1, Complex.normSq_zero, mul_zero, zero_add, add_zero] at hj0 hj1 hj2
  have hl : Complex.normSq (g.val 2 2) = 1 := by nlinarith
  have h00 := Complex.normSq_nonneg (g.val 0 0)
  have h10 := Complex.normSq_nonneg (g.val 1 0)
  have h01 := Complex.normSq_nonneg (g.val 0 1)
  have h11 := Complex.normSq_nonneg (g.val 1 1)
  have hs : Complex.normSq (g.val i j) ≤ 1 := by
    fin_cases i <;> fin_cases j
    · change Complex.normSq (g.val 0 0) ≤ 1
      linarith
    · change Complex.normSq (g.val 0 1) ≤ 1
      linarith
    · change Complex.normSq (g.val 0 2) ≤ 1
      rw [h0, Complex.normSq_zero]
      norm_num
    · change Complex.normSq (g.val 1 0) ≤ 1
      linarith
    · change Complex.normSq (g.val 1 1) ≤ 1
      linarith
    · change Complex.normSq (g.val 1 2) ≤ 1
      rw [h1, Complex.normSq_zero]
      norm_num
    · change Complex.normSq (g.val 2 0) ≤ 1
      rw [hr0, Complex.normSq_zero]
      norm_num
    · change Complex.normSq (g.val 2 1) ≤ 1
      rw [hr1, Complex.normSq_zero]
      norm_num
    · change Complex.normSq (g.val 2 2) ≤ 1
      exact hl.le
  rw [Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (g.val i j)]

lemma ball_origin_stabilizer_compact (b : ℂ) (hb : b.re < 0) :
    IsCompact {g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b | g • ballOrigin b hb = ballOrigin b hb} := by
  let : ProperSpace (ArithmeticQuotientEquationsData.Mat ℂ) := inferInstanceAs (ProperSpace (Fin 3 → Fin 3 → ℂ))
  have he := complex_matrix_closedEmbedding b
  apply he.isEmbedding.isCompact_iff.mpr
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨he.isClosedMap _ (isClosed_eq (continuous_id.smul continuous_const) continuous_const), ?_⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  exact origin_stabilizer_entry_norm_le b hb g hg i j

end

section

/-! Properness of the ball action, from the continuous section and compact
origin stabilizer. Closed discrete subgroups act properly discontinuously. -/

open scoped Classical Pointwise
open _root_.Topology

instance ballLocallyCompact (b : ℂ) : LocallyCompactSpace (Ball b) := by
  let : LocallyCompactSpace BallCoordinates :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → ℂ))
  exact (ballOpen b).isOpen.locallyCompactSpace

instance ballSecondCountable (b : ℂ) : SecondCountableTopology (Ball b) := by
  let : SecondCountableTopology BallCoordinates :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → ℂ))
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

lemma proper_orbitMap_of_section {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousSMul G X]
    (x : X) (s : X → G) (hs : Continuous s) (hsec : ∀ y, s y • x = y)
    (hstab : IsCompact {g : G | g • x = x}) : IsProperMap (fun g : G => g • x) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_id.smul continuous_const, ?_⟩
  intro K hK
  apply ((hK.image hs).mul hstab).of_isClosed_subset
    (hK.isClosed.preimage (continuous_id.smul continuous_const))
  intro g hg
  refine Set.mem_mul.mpr ⟨s (g • x), ⟨g • x, hg, rfl⟩, (s (g • x))⁻¹ * g, ?_, ?_⟩
  · change ((s (g • x))⁻¹ * g) • x = x
    rw [mul_smul]
    exact (congrArg (fun y : X => (s (g • x))⁻¹ • y) (hsec (g • x)).symm).trans
      (inv_smul_smul _ _)
  · simp

lemma ballAction_proper (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0) :
    ProperSMul (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (Ball b) := by
  let : MulAction.IsPretransitive (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (Ball b) :=
    ballAction_pretransitive b hbim hb
  exact MulAction.properSMul_of_proper_orbitMap
    (proper_orbitMap_of_section (ballOrigin b hb) (ballBoost b hbim hb)
      (continuous_ballBoost b hbim hb) (ballBoost_origin b hbim hb)
      (ball_origin_stabilizer_compact b hb))

lemma discrete_ballAction_properlyDiscontinuous (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0)
    (Γ : Subgroup (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b)) [DiscreteTopology Γ] :
    ProperlyDiscontinuousSMul Γ (Ball b) := by
  let : ProperSMul (ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (Ball b) := ballAction_proper b hbim hb
  have : ProperSMul Γ (Ball b) := inferInstance
  exact properlyDiscontinuousSMul_iff_properSMul.mpr this

end

/-! The fractional-linear ball action is holomorphic in affine coordinates. -/

open scoped Classical ContDiff
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

def affineRow (A : ArithmeticQuotientEquationsData.Mat ℂ) (i : Fin 3) (w : BallCoordinates) : ℂ :=
  A i 0 * w 0 + A i 1 * w 1 + A i 2

def ballActionCoordinates (A : ArithmeticQuotientEquationsData.Mat ℂ) (w : BallCoordinates) : BallCoordinates :=
  fun i => affineRow A i.castSucc w / affineRow A 2 w

lemma mulVec_liftVector (A : ArithmeticQuotientEquationsData.Mat ℂ) (w : BallCoordinates) (i : Fin 3) :
    A.mulVec (liftVector w) i = affineRow A i w := by
  simp [affineRow, Matrix.mulVec, dotProduct, liftVector, Fin.sum_univ_succ, add_assoc]

lemma ball_smul_coordinates (b : ℂ) (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (w : Ball b) :
    (g • w).val = ballActionCoordinates g.val.val w.val := by
  funext i
  change g.val.val.mulVec (liftVector w.val) i.castSucc /
    g.val.val.mulVec (liftVector w.val) 2 = _
  simp only [mulVec_liftVector, ballActionCoordinates]

lemma affineRow_last_ne_zero (b : ℂ) (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (w : Ball b) :
    affineRow g.val.val 2 w.val ≠ 0 := by
  have h := cone_last_ne_zero b (g • liftBall b w)
  change g.val.val.mulVec (liftVector w.val) 2 ≠ 0 at h
  rwa [mulVec_liftVector] at h

lemma contDiff_affineRow (A : ArithmeticQuotientEquationsData.Mat ℂ) (i : Fin 3) (n : ℕ∞ω) : ContDiff ℂ n (affineRow A i) := by
  unfold affineRow
  fun_prop

lemma contDiffAt_ballActionCoordinates (b : ℂ) (g : ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b) (w : Ball b)
    (n : ℕ∞ω) : ContDiffAt ℂ n (ballActionCoordinates g.val.val) w.val := by
  apply contDiffAt_pi.mpr
  intro i
  exact (contDiff_affineRow g.val.val i.castSucc n).contDiffAt.div
    (contDiff_affineRow g.val.val 2 n).contDiffAt (affineRow_last_ne_zero b g w)

end

end OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall
