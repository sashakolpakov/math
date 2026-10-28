import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoChartMetric
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedOneMixedDerivatives

/-! # Closed Two -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedTwo.CM.Construction

noncomputable section

section

/-! The mixed component of the actual exterior derivative of a one-form
is the difference of the two Dolbeault coefficient derivatives. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem oneForm_extDeriv_apply (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (hf : DifferentiableAt ℝ f x) (u v : E) :
    KahlerDifferential.CM.Construction.twoFormBilinear (extDeriv f x) u v =
      fderiv ℝ (fun y => f y (fun _ => v)) x u -
        fderiv ℝ (fun y => f y (fun _ => u)) x v := by
  rw [KahlerDifferential.CM.Construction.twoFormBilinear_apply, extDeriv_apply hf, Fin.sum_univ_two]
  have h0 : (0 : Fin 2).removeNth ![u, v] = fun _ => v := by ext i; fin_cases i; rfl
  have h1 : (1 : Fin 2).removeNth ![u, v] = fun _ => u := by ext i; fin_cases i; rfl
  rw [h0, h1]
  change (1 : ℤ) • fderiv ℝ (fun y => f y (fun _ => v)) x u +
    (-1 : ℤ) • fderiv ℝ (fun y => f y (fun _ => u)) x v = _
  simp only [one_smul, neg_one_smul, sub_eq_add_neg]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem mixedTwoCoefficient_extDeriv (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (hf : DifferentiableAt ℝ f x) (u v : E) :
    MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (extDeriv f x) u v =
      AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative
        (fun y => ComplexCovector.CM.Construction.holomorphicCovectorProjection (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) v) x u -
      MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
        (fun y => Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) u) x v := by
  rw [MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient_apply]
  simp only [oneForm_extDeriv_apply f hf]
  rw [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative,
    ClosedOneMixedDerivatives.CM.Construction.holomorphic_projection_coefficient_derivative f hf,
    ClosedOneMixedDerivatives.CM.Construction.holomorphic_projection_coefficient_derivative f hf,
    ClosedOneMixedDerivatives.CM.Construction.antiholomorphic_projection_coefficient_derivative f hf,
    ClosedOneMixedDerivatives.CM.Construction.antiholomorphic_projection_coefficient_derivative f hf]
  ring_nf
  simp only [Complex.I_sq]
  ring

end

section

/-! Closedness and type (1,1) force symmetry of the holomorphic
derivative of the actual mixed two-form coefficients. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

def holomorphicMixedTwoTensor (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℂ) (u v w : E) : ℂ :=
  (1 / 4 : ℂ) * (T u v w - Complex.I * T u v (Complex.I • w) -
    Complex.I * T (Complex.I • u) v w - T (Complex.I • u) v (Complex.I • w))

theorem closedTwoTensor_holomorphic_symmetric
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℂ)
    (hS : ∀ a b c : E, T a b c = -T a c b)
    (hJ : ∀ a b c : E, T a (Complex.I • b) c = -T a b (Complex.I • c))
    (hclosed : ∀ a b c : E, T a b c - T b a c + T c a b = 0)
    (u v w : E) : holomorphicMixedTwoTensor T u v w = holomorphicMixedTwoTensor T w v u := by
  have hJJ (a b c : E) : T a (Complex.I • b) (Complex.I • c) = T a b c := by
    rw [hJ, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, neg_neg]
  have hR₁ := hclosed u w v
  rw [hS u w v, hS w u v] at hR₁
  have hR₂ := hclosed (Complex.I • u) (Complex.I • w) v
  rw [hS (Complex.I • u) (Complex.I • w) v,
    hS (Complex.I • w) (Complex.I • u) v, hJJ] at hR₂
  have hR : T u v w - T (Complex.I • u) v (Complex.I • w) =
      T w v u - T (Complex.I • w) v (Complex.I • u) := by
    linear_combination hR₂ - hR₁
  have hI₁ := hclosed u w (Complex.I • v)
  rw [hS u w (Complex.I • v), hJ u v w,
    hS w u (Complex.I • v), hJ w v u] at hI₁
  have hI₂ := hclosed (Complex.I • u) (Complex.I • w) (Complex.I • v)
  rw [hJJ, hJJ, hJJ, hS (Complex.I • u) w v, hS (Complex.I • w) u v] at hI₂
  have hI : T u v (Complex.I • w) + T (Complex.I • u) v w =
      T w v (Complex.I • u) + T (Complex.I • w) v u := by
    linear_combination hI₁ - hI₂
  unfold holomorphicMixedTwoTensor
  linear_combination (hR - Complex.I * hI) / 4

end

/-! The tensor symmetry is the genuine holomorphic coefficient identity
for a smooth closed form of type (1,1), on any open chart domain. -/

open Filter
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def twoFormFirstDerivative (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (x : E) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℂ := KahlerDifferential.CM.Construction.twoFormBilinear.comp (fderiv ℝ f x)

theorem twoFormFirstDerivative_apply (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E}
    (hf : DifferentiableAt ℝ f x) (u v w : E) :
    twoFormFirstDerivative f x u v w = fderiv ℝ (fun y => f y ![v, w]) x u := by
  rw [fderiv_continuousAlternatingMap_apply_const_apply hf]
  exact KahlerDifferential.CM.Construction.twoFormBilinear_apply _ v w

theorem twoFormFirstDerivative_skew (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (x u v w : E) :
    twoFormFirstDerivative f x u v w = -twoFormFirstDerivative f x u w v :=
  MixedTwoCoefficient.CM.Construction.twoFormBilinear_skew _ w v

theorem twoFormFirstDerivative_closed (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : extDeriv f x = 0) (u v w : E) :
    twoFormFirstDerivative f x u v w - twoFormFirstDerivative f x v u w +
      twoFormFirstDerivative f x w u v = 0 := by
  simpa only [twoFormFirstDerivative_apply f hf] using KahlerDifferential.CM.Construction.closed_twoForm_derivative f hf hc u v w

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
theorem type11_fderiv (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E} (hf : DifferentiableAt ℝ f x)
    (ht : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 (f y)) (u : E) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 (fderiv ℝ f x u) := by
  intro z v
  have heq : (fun y => f y (fun i => (z : ℂ) • v i)) =ᶠ[𝓝 x]
      (fun y => Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 1 z * f y v) := by
    filter_upwards [ht] with y hy
    exact hy z v
  have h := congrArg (fun L : E →L[ℝ] ℂ => L u) heq.fderiv_eq
  rw [fderiv_continuousAlternatingMap_apply_const_apply hf,
    fderiv_const_mul (hf.continuousAlternatingMap_apply_const v)] at h
  simpa only [smul_apply, smul_eq_mul, fderiv_continuousAlternatingMap_apply_const_apply hf] using h

omit [IsScalarTower ℝ ℂ E] in
theorem twoFormFirstDerivative_J_left (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E}
    (hf : DifferentiableAt ℝ f x) (ht : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 (f y)) (u v w : E) :
    twoFormFirstDerivative f x u (Complex.I • v) w =
      -twoFormFirstDerivative f x u v (Complex.I • w) :=
  MixedTwoCoefficient.CM.Construction.twoFormBilinear_type11_J_left _ (type11_fderiv f hf ht u) v w

theorem mixedTwoCoefficient_fderiv (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E}
    (hf : DifferentiableAt ℝ f x) (u v w : E) :
    fderiv ℝ (fun y => MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (f y) v w) x u =
      MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (fderiv ℝ f x u) v w := by
  let C : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2 →L[ℝ] ℂ :=
    (ContinuousAlternatingMap.apply ℝ E ℂ ![v, w] +
      ContinuousAlternatingMap.apply ℝ E ℂ ![Complex.I • v, Complex.I • w] -
      Complex.I • ContinuousAlternatingMap.apply ℝ E ℂ ![v, Complex.I • w] +
      Complex.I • ContinuousAlternatingMap.apply ℝ E ℂ ![Complex.I • v, w])
  have hC (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) : (1 / 4 : ℂ) * C a = MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient a v w := by
    rw [MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient_apply]
    simp only [KahlerDifferential.CM.Construction.twoFormBilinear_apply]
    rfl
  have hd := ((C.hasFDerivAt.comp x hf.hasFDerivAt).const_mul (1 / 4 : ℂ)).fderiv
  have h := congrArg (fun L : E →L[ℝ] ℂ => L u) hd
  change fderiv ℝ (fun y => (1 / 4 : ℂ) * C (f y)) x u =
    (1 / 4 : ℂ) * C (fderiv ℝ f x u) at h
  simpa only [hC] using h

theorem holomorphicMixedTwoTensor_eq_derivative (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E}
    (hf : DifferentiableAt ℝ f x) (ht : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 (f y)) (u v w : E) :
    holomorphicMixedTwoTensor (twoFormFirstDerivative f x) u v w =
      MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (f y) v w) x u := by
  rw [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative, mixedTwoCoefficient_fderiv f hf,
    mixedTwoCoefficient_fderiv f hf, MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient_type11 _ (type11_fderiv f hf ht u),
    MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient_type11 _ (type11_fderiv f hf ht (Complex.I • u))]
  change (1 / 4 : ℂ) * (KahlerDifferential.CM.Construction.twoFormBilinear (fderiv ℝ f x u) v w -
    Complex.I * KahlerDifferential.CM.Construction.twoFormBilinear (fderiv ℝ f x u) v (Complex.I • w) -
    Complex.I * KahlerDifferential.CM.Construction.twoFormBilinear (fderiv ℝ f x (Complex.I • u)) v w -
    KahlerDifferential.CM.Construction.twoFormBilinear (fderiv ℝ f x (Complex.I • u)) v (Complex.I • w)) = _
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem closed_type11_holomorphic_derivative (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) {x : E}
    (hf : DifferentiableAt ℝ f x) (ht : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 (f y))
    (hc : extDeriv f x = 0) (u v w : E) :
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (f y) v w) x u =
      MetricDerivative.CM.Construction.holomorphicDirectionalDerivative (fun y => MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient (f y) v u) x w := by
  rw [← holomorphicMixedTwoTensor_eq_derivative f hf ht,
    ← holomorphicMixedTwoTensor_eq_derivative f hf ht]
  exact closedTwoTensor_holomorphic_symmetric _ (twoFormFirstDerivative_skew f x)
    (twoFormFirstDerivative_J_left f hf ht) (twoFormFirstDerivative_closed f hf hc) u v w

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedTwo.CM.Construction
