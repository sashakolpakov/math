import OAI.Analysis.PDE.Dirichlet.Periodic.Linearized
import OAI.Analysis.PDE.Dirichlet.SecondDerivative

open Set Module
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem quaternionic_gradient_estimate_lattice {n : ℕ} (hn : 1 ≤ n)
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C)
    {ψ r F : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 3 ψ) (hr : ContDiff ℝ 2 r)
    (hF : DifferentiableOn ℝ F {x | r x < 0})
    (hrper : LatticePeriodic e lat r) (hψper : LatticePeriodic e lat ψ)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x)
    (v : CoordinateSpace n 4) {m M r₀ L B : ℝ} (hm : 0 < m) (hr₀ : 0 < r₀) (hL : 0 ≤ L)
    (hdataBounds : ∀ x, r x < 0 → m ≤ F x ∧ F x ≤ M)
    (hconvex : ∀ x, r x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef)
    (hdata : ∀ x, r x < 0 → |directionalDerivative F v x| ≤ L)
    (hboundary : ∀ x, r x = 0 → |directionalDerivative ψ v x| ≤ B) :
    ∀ x, r x ≤ 0 → |directionalDerivative ψ v x| ≤
      B - (L / (r₀ * (m / (2 * (M ^ 2 + 1))))) * r x := by
  let κ := r₀ * (m / (2 * (M ^ 2 + 1)))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hcoercive (x) (hx : r x < 0) :
      κ ≤ mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) r x := by
    apply mooreDifferential_defining_lower hn _ _ (hA x hx) hr₀
    · rw [heq x hx]; exact (hdataBounds x hx).1
    · rw [heq x hx]; exact (hdataBounds x hx).2
    · exact hconvex x hx
  apply moore_linearized_barrier_estimate_lattice e lat hC hr
    (contDiff_directionalDerivative hψ (by norm_num) v) hrper
    (hψper.fderiv.comp (fun D ↦ D v)) hbounded hA
  · intro x hx
    rw [mooreLinearization_directional_eq_on_open hψ
      (isOpen_lt hr.continuous continuous_const) hF heq v hx]
    calc
      |directionalDerivative F v x| ≤ L := hdata x hx
      _ = (L / κ) * κ := (div_mul_cancel₀ L hκ.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcoercive x hx) (div_nonneg hL hκ.le)
  · exact fun x hx ↦ hκ.trans_le (hcoercive x hx)
  · exact hboundary

theorem quaternionic_second_directional_estimate_lattice {n : ℕ} (hn : 1 ≤ n)
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C)
    {ψ r F : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 4 ψ) (hr : ContDiff ℝ 2 r)
    (hrper : LatticePeriodic e lat r) (hψper : LatticePeriodic e lat ψ)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x)
    (v : CoordinateSpace n 4) {m M r₀ L B : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hr₀ : 0 < r₀) (hL : 0 ≤ L)
    (hdataBounds : ∀ x, r x < 0 → m ≤ F x ∧ F x ≤ M)
    (hconvex : ∀ x, r x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef)
    (hdata : ∀ x, r x < 0 →
      -L ≤ deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0)
    (hboundary : ∀ x, r x = 0 →
      directionalDerivative (directionalDerivative ψ v) v x ≤ B) :
    ∀ x, r x ≤ 0 → directionalDerivative (directionalDerivative ψ v) v x ≤
      B - ((L * M) / (r₀ * (m / (2 * (M ^ 2 + 1))))) * r x := by
  let κ := r₀ * (m / (2 * (M ^ 2 + 1)))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hcoercive (x) (hx : r x < 0) :
      κ ≤ mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) r x := by
    apply mooreDifferential_defining_lower hn _ _ (hA x hx) hr₀
    · rw [heq x hx]; exact (hdataBounds x hx).1
    · rw [heq x hx]; exact (hdataBounds x hx).2
    · exact hconvex x hx
  have hv3 : ContDiff ℝ 3 (directionalDerivative ψ v) :=
    contDiff_directionalDerivative hψ (by norm_num) v
  have hvper : LatticePeriodic e lat (directionalDerivative ψ v) :=
    hψper.fderiv.comp (fun D ↦ D v)
  apply moore_linearized_upper_estimate_lattice e lat hC hr
    (contDiff_directionalDerivative hv3 (by norm_num) v) hrper
    (hvper.fderiv.comp (fun D ↦ D v)) hbounded hA
  · intro x hx
    have hFx : 0 ≤ F x := (hm.trans_le (hdataBounds x hx).1).le
    have hprod := mul_le_mul_of_nonneg_left (hdata x hx) hFx
    have hLM := mul_le_mul_of_nonneg_left (hdataBounds x hx).2 hL
    have hsecond := mooreLinearization_second_directional_ge hψ
      (isOpen_lt hr.continuous continuous_const) hA heq v hx
    have hc := mul_le_mul_of_nonneg_left (hcoercive x hx)
      (div_nonneg (mul_nonneg hL hM) hκ.le)
    rw [div_mul_cancel₀ _ hκ.ne'] at hc
    change 0 ≤ _ + ((L * M) / κ) * _
    nlinarith
  · exact fun x hx ↦ hκ.trans_le (hcoercive x hx)
  · exact hboundary

end OAI.Analysis.PDE.Dirichlet
