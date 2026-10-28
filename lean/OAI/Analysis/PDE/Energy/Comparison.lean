import OAI.Analysis.PDE.Green.BoundedGreen
import OAI.LinearAlgebra.Moore.OuterPencil

/-! The determinant-segment energy comparison, with the cofactor estimate
derived from actual zero-boundary integration by parts. -/

noncomputable section
namespace OAI.Analysis.PDE.Energy

open Matrix Set _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open OAI.Analysis.PDE.Green
open scoped MatrixOrder ComplexOrder

theorem continuous_integrableOn_bounded {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsFiniteMeasureOnCompacts (volume : Measure E)]
    {S : Set E} (hb : Bornology.IsBounded S)
    {f : E → ℝ} (hf : Continuous f) : IntegrableOn f S := by
  have hk : IsCompact (closure S) := Metric.isCompact_of_isClosed_isBounded
    isClosed_closure hb.closure
  exact (hf.continuousOn.integrableOn_compact hk).mono_set subset_closure

def determinantMass {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)) (ψ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) : ℝ :=
  ∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)

def determinantSegmentEnergy {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)) (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) : ℝ :=
  ∫ x in S, u x * ∫ t in (0 : ℝ)..1,
    OAI.LinearAlgebra.Moore.mooreDet n (t • OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y) x +
      (1 - t) • OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)

def cofactorBackgroundMass {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)) (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) : ℝ :=
  ∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n
    (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y) x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)

section HessianContinuity
open scoped Matrix.Norms.Elementwise

theorem continuous_quaternionHessian_three {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {ψ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ) :
    Continuous (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ) :=
  (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one e hψ).continuous

end HessianContinuity

theorem continuous_mass_integrand {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {ψ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ) (hu : Continuous u) :
    Continuous (fun x ↦ (-u x) * OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) :=
  hu.neg.mul ((OAI.LinearAlgebra.Moore.continuous_mooreDet n).comp (continuous_quaternionHessian_three e hψ))

theorem continuous_background_integrand {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u) :
    Continuous (fun x ↦ (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y) x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) := by
  have hAc : Continuous (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y)) :=
    continuous_quaternionHessian_three e (hB.add hu)
  have hDc : Continuous (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B) :=
    continuous_quaternionHessian_three e hB
  have hpair : Continuous (fun x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s ↦
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y) x, OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) :=
    hAc.prodMk hDc
  have hd : Continuous (fun x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s ↦ OAI.LinearAlgebra.Moore.mooreDifferential n
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y) x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) := by
    simpa only using! (OAI.LinearAlgebra.Moore.continuous_mooreDifferential n).comp hpair
  exact hu.continuous.neg.mul hd

theorem hessian_sum {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y) x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x + OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x := by
  simpa only [one_smul] using OAI.Analysis.PDE.Dirichlet.quaternionHessian_add_smul e hB hu 1 x

theorem hessian_segment {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u)
    (t : ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + t • u y) x =
      t • OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y) x +
        (1 - t) • OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x := by
  rw [OAI.Analysis.PDE.Dirichlet.quaternionHessian_add_smul e hB hu, hessian_sum e hB hu]
  module

/-- The matrix pencil in the definition is exactly the Hessian of the
potential segment used in the paper. -/
theorem determinantSegmentEnergy_eq_potential_integral {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u) :
    determinantSegmentEnergy e S B u =
      ∫ x in S, u x * ∫ t in (0 : ℝ)..1,
        OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + t • u y) x) := by
  simp_rw [hessian_segment e hB hu]
  rfl

theorem cofactor_background_bound {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : volume (frontier S) = 0)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hz : ∀ x ∈ frontier S, u x = 0)
    (hpos : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y) x)).PosSemidef) :
    cofactorBackgroundMass e S B u ≤
      (n : ℝ) * determinantMass e S (fun y ↦ B y + u y) u := by
  let A := OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y)
  have hXi := continuous_integrableOn_bounded hb (continuous_mass_integrand e (hB.add hu) hu.continuous)
  have hYi := continuous_integrableOn_bounded hb (continuous_background_integrand e hB hu)
  have hp (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) =
        (n : ℝ) * ((-u x) * OAI.LinearAlgebra.Moore.mooreDet n (A x)) -
          (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) := by
    have he : OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) +
        OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) =
          (n : ℝ) * OAI.LinearAlgebra.Moore.mooreDet n (A x) := by
      rw [← OAI.LinearAlgebra.Moore.mooreDifferential_add,
        ← hessian_sum e (hB.of_le (by norm_num)) (hu.of_le (by norm_num)) x]
      exact OAI.LinearAlgebra.Moore.mooreDifferential_self n (A x)
    linear_combination (-u x) * he
  have hg := OAI.Analysis.PDE.Green.moore_cofactor_energy_bounded_nonneg e hS hb hnull (hB.add hu)
    (hu.of_le (by norm_num)) hz hpos
  change 0 ≤ ∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) at hg
  simp_rw [hp] at hg
  rw [integral_sub (hXi.const_mul _) hYi, integral_const_mul] at hg
  exact sub_nonneg.mp hg

theorem determinant_segment_energy_formula {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s)} (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hrank : ∀ x ∈ S, ∃ w : Fin (n + 2) → Quaternion ℝ,
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x = OAI.Analysis.Calculus.Quaternion.outer w) :
    determinantSegmentEnergy e S B u =
      -(determinantMass e S (fun y ↦ B y + u y) u / ((n : ℝ) + 3) +
        cofactorBackgroundMass e S B u / (((n : ℝ) + 2) * ((n : ℝ) + 3))) := by
  let A := OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y)
  let D := OAI.Analysis.PDE.Dirichlet.quaternionHessian e B
  have hXi := continuous_integrableOn_bounded hb (continuous_mass_integrand e (hB.add hu) hu.continuous)
  have hYi := continuous_integrableOn_bounded hb (continuous_background_integrand e hB hu)
  have he : determinantSegmentEnergy e S B u =
      ∫ x in S, -(((-u x) * OAI.LinearAlgebra.Moore.mooreDet (n + 2) (A x)) / ((n : ℝ) + 3) +
        ((-u x) * OAI.LinearAlgebra.Moore.mooreDifferential (n + 2) (A x) (D x)) /
          (((n : ℝ) + 2) * ((n : ℝ) + 3))) := by
    apply setIntegral_congr_fun hS
    intro x hx
    dsimp only
    obtain ⟨w,hw⟩ := hrank x hx
    change u x * (∫ t in (0 : ℝ)..1, OAI.LinearAlgebra.Moore.mooreDet (n + 2) (t • A x + (1-t) • D x)) = _
    have hw' : D x = OAI.Analysis.Calculus.Quaternion.outer w := hw
    rw [hw', OAI.LinearAlgebra.Moore.integral_mooreDet_outer_segment]
    ring
  rw [he, integral_neg, integral_add (hXi.div_const _) (hYi.div_const _),
    integral_div, integral_div]
  rfl

/-- The exact energy comparison from the paper, before division by the
positive right-hand-side normalization `λ`. The background Hessian is genuinely
rank one, and the only inequality needed from integration by parts is proved. -/
theorem determinant_energy_comparison {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s)}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : volume (frontier S) = 0)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hz : ∀ x ∈ frontier S, u x = 0) (hu0 : ∀ x ∈ S, u x ≤ 0)
    (hpos : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y) x)).PosSemidef)
    (hrank : ∀ x ∈ S, ∃ w : Fin (n + 2) → Quaternion ℝ,
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x = OAI.Analysis.Calculus.Quaternion.outer w) :
    ((n : ℝ) + 1) / ((n : ℝ) + 3) *
        determinantMass e S (fun y ↦ B y + u y) u ≤
      determinantMass e S (fun y ↦ B y + u y) u + determinantSegmentEnergy e S B u ∧
      determinantMass e S (fun y ↦ B y + u y) u + determinantSegmentEnergy e S B u ≤
        determinantMass e S (fun y ↦ B y + u y) u := by
  let X := determinantMass e S (fun y ↦ B y + u y) u
  let Y := cofactorBackgroundMass e S B u
  have hX : 0 ≤ X := by
    apply setIntegral_nonneg hS.measurableSet
    intro x hx
    exact mul_nonneg (neg_nonneg.mpr (hu0 x hx))
      (OAI.LinearAlgebra.Moore.mooreDet_nonneg_of_complexify_posSemidef _ (hpos x hx))
  have hY : 0 ≤ Y := by
    apply setIntegral_nonneg hS.measurableSet
    intro x hx
    obtain ⟨w,hw⟩ := hrank x hx
    rw [hw]
    exact mul_nonneg (neg_nonneg.mpr (hu0 x hx))
      (OAI.LinearAlgebra.Moore.mooreDifferential_outer_nonneg _ w (hpos x hx))
  have hYX : Y ≤ ((n : ℝ) + 2) * X := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      cofactor_background_bound e hS hb hnull hB hu hz hpos
  have hdim : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  have hc := segment_energy_comparison (n + 1) hX hY (by rw [hdim]; exact hYX)
  dsimp only at hc
  rw [integral_segment] at hc
  have hn : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
  rw [hn] at hc
  change _ ≤ X + determinantSegmentEnergy e S B u ∧
    X + determinantSegmentEnergy e S B u ≤ X
  rw [determinant_segment_energy_formula e hS.measurableSet hb hB hu hrank]
  have hn3 : (n : ℝ) + 1 + 2 = (n : ℝ) + 3 := by ring
  have hn2 : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
  rw [hn3, hn2] at hc
  simpa only [X, Y] using hc

theorem determinantMass_of_equation {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : MeasurableSet S)
    (ψ u μ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (lam : ℝ)
    (heq : ∀ x ∈ S, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) = lam * μ x) :
    determinantMass e S ψ u = lam * ∫ x in S, (-u x) * μ x := by
  rw [determinantMass, ← integral_const_mul]
  apply setIntegral_congr_fun hS
  intro x hx
  dsimp only
  rw [heq x hx]
  ring

theorem scaled_energy_comparison {a X R lam : ℝ} (hlam : 0 < lam)
    (h : a * (lam * X) ≤ lam * X + R ∧ lam * X + R ≤ lam * X) :
    a * X ≤ X + R / lam ∧ X + R / lam ≤ X := by
  have he : lam * (R / lam) = R := by field_simp
  constructor
  · apply (mul_le_mul_iff_left₀ hlam).mp
    nlinarith [h.1]
  · apply (mul_le_mul_iff_left₀ hlam).mp
    nlinarith [h.2]

/-- Lemma `energy-comparison` in the source normalization `det H(B+u)=λμ`.
All energy integrals are actual Lebesgue integrals; no Green identity or
cofactor bound is an extra hypothesis. -/
theorem normalized_determinant_energy_comparison {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s)}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : volume (frontier S) = 0)
    {B u μ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hz : ∀ x ∈ frontier S, u x = 0) (hu0 : ∀ x ∈ S, u x ≤ 0)
    (hpos : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y) x)).PosSemidef)
    (hrank : ∀ x ∈ S, ∃ w : Fin (n + 2) → Quaternion ℝ,
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x = OAI.Analysis.Calculus.Quaternion.outer w) {lam : ℝ} (hlam : 0 < lam)
    (heq : ∀ x ∈ S,
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y ↦ B y + u y) x) = lam * μ x) :
    let X₀ := ∫ x in S, (-u x) * μ x
    let E := determinantSegmentEnergy e S B u / lam
    ((n : ℝ) + 1) / ((n : ℝ) + 3) * X₀ ≤ X₀ + E ∧ X₀ + E ≤ X₀ := by
  have h := determinant_energy_comparison e hS hb hnull hB hu hz hu0 hpos hrank
  rw [determinantMass_of_equation e hS.measurableSet _ _ _ lam heq] at h
  exact scaled_energy_comparison hlam h

end OAI.Analysis.PDE.Energy
