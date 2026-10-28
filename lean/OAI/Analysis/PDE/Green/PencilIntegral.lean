import OAI.Analysis.PDE.Green.PencilBoundary
import OAI.LinearAlgebra.Moore.Variation
import Mathlib.MeasureTheory.Integral.Prod

/-! Integrating the genuine second Green identity along a determinant pencil. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory Measure OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore

section Fubini
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

theorem integral_interval_swap_bounded {S : Set E} (hb : Bornology.IsBounded S)
    {f : ℝ × E → ℝ} (hf : Continuous f) :
    (∫ t in (0 : ℝ)..1, ∫ x in S, f (t, x)) =
      ∫ x in S, ∫ t in (0 : ℝ)..1, f (t, x) := by
  simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  apply integral_integral_swap
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hbI : Bornology.IsBounded (Ioc (0 : ℝ) 1) :=
    isCompact_Icc.isBounded.subset Ioc_subset_Icc_self
  exact OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded (hbI.prod hb) hf

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure E)] in
theorem continuous_pencil_density {n : ℕ} {w : E → ℝ}
    {A D V : E → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hw : Continuous w) (hA : Continuous A) (hD : Continuous D) (hV : Continuous V) :
    Continuous (fun p : ℝ × E => w p.2 * OAI.LinearAlgebra.Moore.mooreDifferential n
      (A p.2 + p.1 • D p.2) (V p.2)) := by
  have hmat : Continuous (fun p : ℝ × E => A p.2 + p.1 • D p.2) :=
    (hA.comp continuous_snd).add (continuous_fst.smul (hD.comp continuous_snd))
  have hp : Continuous (fun p : ℝ × E =>
      (A p.2 + p.1 • D p.2, V p.2)) := hmat.prodMk (hV.comp continuous_snd)
  have hd : Continuous (fun p : ℝ × E =>
      OAI.LinearAlgebra.Moore.mooreDifferential n (A p.2 + p.1 • D p.2) (V p.2)) := by
    simpa only using! (OAI.LinearAlgebra.Moore.continuous_mooreDifferential n).comp hp
  exact (hw.comp continuous_snd).mul hd

theorem integrate_pencil_green {n : ℕ} {S : Set E} (hb : Bornology.IsBounded S)
    {u v : E → ℝ} {A D V : E → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hu : Continuous u) (hv : Continuous v)
    (hA : Continuous A) (hD : Continuous D) (hV : Continuous V)
    (hgreen : ∀ t : ℝ,
      (∫ x in S, u x * OAI.LinearAlgebra.Moore.mooreDifferential n (A x + t • D x) (V x)) =
      ∫ x in S, v x * OAI.LinearAlgebra.Moore.mooreDifferential n (A x + t • D x) (D x)) :
    (∫ x in S, ∫ t in (0 : ℝ)..1, u x * OAI.LinearAlgebra.Moore.mooreDifferential n (A x + t • D x) (V x)) =
      ∫ x in S, v x * (OAI.LinearAlgebra.Moore.mooreDet n (A x + D x) - OAI.LinearAlgebra.Moore.mooreDet n (A x)) := by
  rw [← integral_interval_swap_bounded hb (continuous_pencil_density hu hA hD hV)]
  simp_rw [hgreen]
  rw [integral_interval_swap_bounded hb (continuous_pencil_density hv hA hD hD)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [intervalIntegral.integral_const_mul, OAI.LinearAlgebra.Moore.integral_mooreDifferential_affine]
  simp

end Fubini

/-- Actual determinant-pencil energy variation, with the boundary cancellation
proved from shared fiber geometry rather than assumed as a Green identity. -/
theorem determinant_pencil_energy_variation {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {r u B v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B) (hv : ContDiff ℝ 3 v)
    (hb : Bornology.IsBounded {x | r x < 0})
    (hrne : ∀ x ∈ closure {x | r x < 0}, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ y, r y = 0 → u y = 0)
    (hcommon : ∀ x, r x = 0 → ∃ w : Fin n → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0) :
    (∫ x in {x | r x < 0}, ∫ t in (0 : ℝ)..1, u x * OAI.LinearAlgebra.Moore.mooreDifferential n
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in {x | r x < 0}, v x *
      (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) -
        OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) := by
  have hgreen (t : ℝ) := pencil_second_green e hr hu hB (hv.of_le (by norm_num)) t
    hb hrne huz hcommon
  simp_rw [quaternionHessian_add_mul e (hB.of_le (by norm_num)) (hu.of_le (by norm_num))] at hgreen ⊢
  have he := integrate_pencil_green hb hu.continuous hv.continuous
    (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hB)
    (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hu)
    (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hv) hgreen
  simpa only [OAI.Analysis.PDE.Energy.hessian_sum e (hB.of_le (by norm_num)) (hu.of_le (by norm_num))] using he

end OAI.Analysis.PDE.Green
