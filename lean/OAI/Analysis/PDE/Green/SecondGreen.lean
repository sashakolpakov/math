import OAI.Analysis.PDE.Green.RegularBoundary

/-! The second Green identity when the normal quadratic coefficient vanishes. -/

noncomputable section
open Set Filter _root_.MeasureTheory Measure
open scoped Topology

namespace OAI.Analysis.PDE.Green

section Differential
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]

def secondGreenFlux (d : I → E) (K : I → I → E → ℝ) (u v : E → ℝ)
    (i : I) (x : E) : ℝ := u x * realFlux d K v i x - v x * realFlux d K u i x

theorem contDiff_secondGreenFlux (d : I → E) (K : I → I → E → ℝ)
    {u v : E → ℝ} (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (i : I) :
    ContDiff ℝ 1 (secondGreenFlux d K u v i) :=
  ((hu.of_le (by norm_num)).mul (contDiff_realFlux d K hK hv i)).sub
    ((hv.of_le (by norm_num)).mul (contDiff_realFlux d K hK hu i))

theorem weightedFlux_divergence (d : I → E) (F : I → E → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) {u : E → ℝ} (hu : ContDiff ℝ 1 u) (x : E) :
    (∑ i, fderiv ℝ (fun y => u y * F i y) x (d i)) =
      (∑ i, fderiv ℝ u x (d i) * F i x) + u x * (∑ i, fderiv ℝ (F i) x (d i)) := by
  simp_rw [fderiv_fun_mul (hu.differentiable (by norm_num) x)
    ((hF _).differentiable (by norm_num) x), _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem secondGreenFlux_divergence (d : I → E) (K : I → I → E → ℝ)
    {u v : E → ℝ} (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hKs : ∀ i j x, K i j x = K j i x) (x : E) :
    (∑ i, fderiv ℝ (secondGreenFlux d K u v i) x (d i)) =
      u x * (∑ i, fderiv ℝ (realFlux d K v i) x (d i)) -
      v x * (∑ i, fderiv ℝ (realFlux d K u i) x (d i)) := by
  have hcross : (∑ i, fderiv ℝ u x (d i) * realFlux d K v i x) =
      ∑ i, fderiv ℝ v x (d i) * realFlux d K u i x := by
    simp only [realFlux, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hKs j i x]
    ring
  unfold secondGreenFlux
  simp_rw [fderiv_fun_sub
    (((hu.of_le (by norm_num)).mul (contDiff_realFlux d K hK hv _)).differentiable (by norm_num) x)
    (((hv.of_le (by norm_num)).mul (contDiff_realFlux d K hK hu _)).differentiable (by norm_num) x),
    _root_.sub_apply]
  rw [Finset.sum_sub_distrib,
    weightedFlux_divergence d _ (contDiff_realFlux d K hK hv) (hu.of_le (by norm_num)),
    weightedFlux_divergence d _ (contDiff_realFlux d K hK hu) (hv.of_le (by norm_num)), hcross]
  ring

end Differential

section Boundary
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [Fintype I]

/-- Vanishing Dirichlet data and vanishing normal quadratic coefficient make
the second-Green flux tangent, even if the full coefficient matrix is indefinite. -/
theorem secondGreenFlux_tangent (d : I → E) (K : I → I → E → ℝ)
    {r u v : E → ℝ} (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 2 u)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hnormal : ∀ x, r x = 0 →
      (∑ i, ∑ j, K i j x * (fderiv ℝ r x (d i) * fderiv ℝ r x (d j))) = 0)
    (x : E) (hx : r x = 0) :
    (∑ i, fderiv ℝ r x (d i) * secondGreenFlux d K u v i x) = 0 := by
  by_cases hd : fderiv ℝ r x = 0
  · simp only [hd, _root_.zero_apply, zero_mul, Finset.sum_const_zero]
  obtain ⟨a, ha⟩ := OAI.Analysis.PDE.Dirichlet.level_set_gradient_factor
    (hr.hasStrictFDerivAt (by norm_num)) hd (hu.differentiable (by norm_num) x)
    (Filter.Eventually.of_forall (fun y hy => huz y (hy.trans hx)))
  have hflux (i : I) : secondGreenFlux d K u v i x =
      -v x * (∑ j, K i j x * (a * fderiv ℝ r x (d j))) := by
    unfold secondGreenFlux
    rw [huz x hx, zero_mul, zero_sub]
    simp only [realFlux, ha, _root_.smul_apply, smul_eq_mul]
    ring
  calc
    _ = -(v x * a) * (∑ i, ∑ j, K i j x *
        (fderiv ℝ r x (d i) * fderiv ℝ r x (d j))) := by
      simp only [hflux, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [hnormal x hx]; ring

end Boundary

section Integral
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)] [Fintype I]

/-- Second Green identity on a bounded regular sublevel set. The normal
quadratic coefficient can vanish without the full matrix being positive. -/
theorem real_operator_second_green (d : I → E) (K : I → I → E → ℝ)
    {r u v : E → ℝ} (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hKs : ∀ i j x, K i j x = K j i x)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (d i) = 0)
    (hb : Bornology.IsBounded {x | r x < 0})
    (hrne : ∀ x ∈ closure {x | r x < 0}, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hnormal : ∀ x, r x = 0 →
      (∑ i, ∑ j, K i j x * (fderiv ℝ r x (d i) * fderiv ℝ r x (d j))) = 0) :
    (∫ x in {x | r x < 0}, u x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x (d i) (d j))) =
    ∫ x in {x | r x < 0}, v x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ u) x (d i) (d j)) := by
  have hvF := contDiff_realFlux d K hK hv
  have huF := contDiff_realFlux d K hK hu
  have hvi : IntegrableOn (fun x => u x *
      (∑ i, fderiv ℝ (realFlux d K v i) x (d i))) {x | r x < 0} :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hu.continuous.mul
      (continuous_finsetSum _ (fun i _ => continuous_directional (hvF i) (d i))))
  have hui : IntegrableOn (fun x => v x *
      (∑ i, fderiv ℝ (realFlux d K u i) x (d i))) {x | r x < 0} :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hv.continuous.mul
      (continuous_finsetSum _ (fun i _ => continuous_directional (huF i) (d i))))
  have he := integral_divergence_zero_of_tangent d (secondGreenFlux d K u v)
    (contDiff_secondGreenFlux d K hK hu hv) hr hb hrne
    (secondGreenFlux_tangent d K hr hu huz hnormal)
  simp_rw [secondGreenFlux_divergence d K hK hu hv hKs] at he
  rw [integral_sub hvi hui] at he
  have heq := sub_eq_zero.mp he
  simpa only [realFlux_divergence d K hK hv hdiv,
    realFlux_divergence d K hK hu hdiv] using heq

end Integral

end OAI.Analysis.PDE.Green
