import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetricTransport

/-! # Two Form Flux Algebra -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormFluxAlgebra.CM.Construction

noncomputable section

section

/-! The finite coefficient calculation reducing the divergence of a
raised mixed two-tensor to the derivative of its Hermitian trace. -/

theorem sum_three_reverse {ι R : Type*} [Fintype ι] [AddCommMonoid R] (f : ι → ι → ι → R) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
  calc
    _ = ∑ j, ∑ i, ∑ k, f i j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, f i j k :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

variable {ι R : Type*} [Fintype ι] [CommRing R]

theorem weighted_two_flux_coefficient_zero (P S : Matrix ι ι R) (DW : ι → Matrix ι ι R)
    (hW : ∀ a, ∑ d, DW d a d = 0) (j : ι) :
    (∑ d, ∑ a, ∑ k, DW d a d * P j k * S a k) = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  rw [← Finset.sum_mul, ← Finset.sum_mul, hW, zero_mul, zero_mul]

theorem raised_two_flux_metric_derivative (P S : Matrix ι ι R) (DP : ι → Matrix ι ι R)
    (hP : ∀ a j k, (∑ d, P a d * DP d j k) = ∑ d, P j d * DP d a k) (j : ι) :
    (∑ d, ∑ a, ∑ k, P a d * DP d j k * S a k) =
      ∑ d, P j d * ∑ a, ∑ k, DP d a k * S a k := by
  calc
    _ = ∑ k, ∑ a, ∑ d, P a d * DP d j k * S a k := sum_three_reverse _
    _ = ∑ k, ∑ a, ∑ d, P j d * DP d a k * S a k := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_mul, hP, Finset.sum_mul]
    _ = ∑ d, ∑ a, ∑ k, P j d * DP d a k * S a k := (sum_three_reverse _).symm
    _ = _ := by
      simp only [Finset.mul_sum, mul_assoc]

theorem raised_two_flux_form_derivative (P : Matrix ι ι R) (DS : ι → Matrix ι ι R)
    (hS : ∀ d a k, DS d a k = DS k a d) (j : ι) :
    (∑ d, ∑ a, ∑ k, P a d * P j k * DS d a k) =
      ∑ k, P j k * ∑ a, ∑ d, P a d * DS k a d := by
  rw [sum_three_reverse]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  rw [hS]
  ring

theorem raised_two_flux_trace_identity (ρ : R) (P S : Matrix ι ι R)
    (DW DP DS : ι → Matrix ι ι R)
    (hW : ∀ a, ∑ d, DW d a d = 0)
    (hP : ∀ a j k, (∑ d, P a d * DP d j k) = ∑ d, P j d * DP d a k)
    (hS : ∀ d a k, DS d a k = DS k a d) (j : ι) :
    (∑ d, ∑ a, ∑ k, (DW d a d * P j k * S a k +
      ρ * (P a d * DP d j k * S a k + P a d * P j k * DS d a k))) =
      ρ * ∑ d, P j d * ∑ a, ∑ k, (DP d a k * S a k + P a k * DS d a k) := by
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [weighted_two_flux_coefficient_zero P S DW hW j,
    raised_two_flux_metric_derivative P S DP hP j, raised_two_flux_form_derivative P DS hS j,
    zero_add]

end

/-! The finite divergence-to-trace identity applied to actual
antiholomorphic directional derivatives of smooth coefficient functions. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

theorem antiholomorphicDirectionalDerivative_sum {ι : Type*} [Fintype ι]
    (f : ι → E → ℂ) {x : E} (hf : ∀ i, DifferentiableAt ℝ (f i) x) (u : E) :
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => ∑ i, f i y) x u =
      ∑ i, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (f i) x u := by
  simp only [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative]
  rw [fderiv_fun_sum (fun i _ => hf i)]
  simp only [sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]

theorem antiholomorphicDirectionalDerivative_three (f g h : E → ℂ) {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (u : E) :
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => f y * g y * h y) x u =
      AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative f x u * g x * h x +
      f x * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative g x u * h x +
      f x * g x * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative h x u := by
  rw [InverseMetricTransport.CM.Construction.antiholomorphicDirectionalDerivative_mul (fun y => f y * g y) h (hf.mul hg) hh,
    InverseMetricTransport.CM.Construction.antiholomorphicDirectionalDerivative_mul f g hf hg]
  ring

variable {ι : Type*} [Fintype ι]

def raisedTwoFlux (ρ : E → ℂ) (P S : E → Matrix ι ι ℂ) (j d : ι) (x : E) : ℂ :=
  ∑ a, ∑ k, (ρ x * P x a d) * P x j k * S x a k

def raisedTwoTrace (P S : E → Matrix ι ι ℂ) (x : E) : ℂ :=
  ∑ a, ∑ k, P x a k * S x a k

theorem raisedTwoFlux_derivative (ρ : E → ℂ) (P S : E → Matrix ι ι ℂ) {x : E}
    (hρ : DifferentiableAt ℝ ρ x)
    (hP : ∀ a k, DifferentiableAt ℝ (fun y => P y a k) x)
    (hS : ∀ a k, DifferentiableAt ℝ (fun y => S y a k) x) (v : ι → E) (j d : ι) :
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (raisedTwoFlux ρ P S j d) x (v d) =
      ∑ a, ∑ k, (AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => ρ y * P y a d) x (v d) *
        P x j k * S x a k + ρ x *
          (P x a d * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => P y j k) x (v d) * S x a k +
            P x a d * P x j k * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => S y a k) x (v d))) := by
  have h (a k : ι) : DifferentiableAt ℝ (fun y => (ρ y * P y a d) * P y j k * S y a k) x :=
    ((hρ.mul (hP a d)).mul (hP j k)).mul (hS a k)
  have hout := antiholomorphicDirectionalDerivative_sum
    (fun a y => ∑ k, (ρ y * P y a d) * P y j k * S y a k)
    (fun a => DifferentiableAt.fun_sum (fun k _ => h a k)) (v d)
  refine hout.trans (Finset.sum_congr rfl (fun a _ => ?_))
  have hin := antiholomorphicDirectionalDerivative_sum
    (fun k y => (ρ y * P y a d) * P y j k * S y a k) (h a) (v d)
  refine hin.trans (Finset.sum_congr rfl (fun k _ => ?_))
  have ht := antiholomorphicDirectionalDerivative_three
    (fun y => ρ y * P y a d) (fun y => P y j k) (fun y => S y a k)
    (hρ.mul (hP a d)) (hP j k) (hS a k) (v d)
  exact ht.trans (by ring)

theorem raisedTwoTrace_derivative (P S : E → Matrix ι ι ℂ) {x : E}
    (hP : ∀ a k, DifferentiableAt ℝ (fun y => P y a k) x)
    (hS : ∀ a k, DifferentiableAt ℝ (fun y => S y a k) x) (u : E) :
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (raisedTwoTrace P S) x u =
      ∑ a, ∑ k, (AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => P y a k) x u * S x a k +
        P x a k * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => S y a k) x u) := by
  have hout := antiholomorphicDirectionalDerivative_sum
    (fun a y => ∑ k, P y a k * S y a k)
    (fun a => DifferentiableAt.fun_sum (fun k _ => (hP a k).mul (hS a k))) u
  refine hout.trans (Finset.sum_congr rfl (fun a _ => ?_))
  have hin := antiholomorphicDirectionalDerivative_sum
    (fun k y => P y a k * S y a k) (fun k => (hP a k).mul (hS a k)) u
  refine hin.trans (Finset.sum_congr rfl (fun k _ => ?_))
  exact (InverseMetricTransport.CM.Construction.antiholomorphicDirectionalDerivative_mul (fun y => P y a k) (fun y => S y a k)
    (hP a k) (hS a k) u).trans (by ring)

theorem raisedTwoFlux_divergence_trace (ρ : E → ℂ) (P S : E → Matrix ι ι ℂ) {x : E}
    (hρ : DifferentiableAt ℝ ρ x)
    (hP : ∀ a k, DifferentiableAt ℝ (fun y => P y a k) x)
    (hS : ∀ a k, DifferentiableAt ℝ (fun y => S y a k) x) (v : ι → E)
    (hW : ∀ a, (∑ d, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => ρ y * P y a d) x (v d)) = 0)
    (hT : ∀ a j k,
      (∑ d, P x a d * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => P y j k) x (v d)) =
        ∑ d, P x j d * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => P y a k) x (v d))
    (hC : ∀ d a k, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => S y a k) x (v d) =
      AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => S y a d) x (v k)) (j : ι) :
    (∑ d, AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (raisedTwoFlux ρ P S j d) x (v d)) =
      ρ x * ∑ d, P x j d * AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (raisedTwoTrace P S) x (v d) := by
  let DW := fun d => Matrix.of fun a k =>
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => ρ y * P y a k) x (v d)
  let DP := fun d => Matrix.of fun a k =>
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => P y a k) x (v d)
  let DS := fun d => Matrix.of fun a k =>
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative (fun y => S y a k) x (v d)
  calc
    _ = ∑ d, ∑ a, ∑ k, (DW d a d * P x j k * S x a k +
        ρ x * (P x a d * DP d j k * S x a k + P x a d * P x j k * DS d a k)) :=
      Finset.sum_congr rfl (fun d _ => raisedTwoFlux_derivative ρ P S hρ hP hS v j d)
    _ = ρ x * ∑ d, P x j d * ∑ a, ∑ k, (DP d a k * S x a k + P x a k * DS d a k) :=
      raised_two_flux_trace_identity (ρ x) (P x) (S x) DW DP DS hW hT hC j
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      congr 1
      exact (raisedTwoTrace_derivative P S hP hS (v d)).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TwoFormFluxAlgebra.CM.Construction
