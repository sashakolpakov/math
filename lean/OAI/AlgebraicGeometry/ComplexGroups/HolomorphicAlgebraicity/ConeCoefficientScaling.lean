import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PuncturedFiberPolynomial
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-! # Cone Coefficient Scaling -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCoefficientScaling.Constructions.Cone

noncomputable section

/-!
# Scaling of the canonical cone-fiber polynomial
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

theorem separable_scaleRoots {P : ℂ[X]} (hP : P.Separable) {t : ℂ} (ht : t ≠ 0) :
    (P.scaleRoots t).Separable := by
  apply (nodup_roots_iff_of_splits (scaleRoots_ne_zero hP.ne_zero t) (IsAlgClosed.splits _)).mp
  rw [roots_scaleRoots P (isUnit_iff_ne_zero.mpr ht)]
  exact (nodup_roots hP).map (mul_right_injective₀ ht)

theorem nonzero_germ_comp_smul {n : ℕ} {c : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    {t : ℂ} (ht : t ≠ 0) (hn : ¬∀ᶠ y in 𝓝 (t • x), c y = 0) :
    ¬∀ᶠ y in 𝓝 x, c (t • y) = 0 := by
  intro hz
  apply hn
  have hinv : Tendsto (fun y : Fin n → ℂ => t⁻¹ • y) (𝓝 (t • x)) (𝓝 x) := by
    simpa only [inv_smul_smul₀ ht] using
      (continuous_const_smul t⁻¹).tendsto (t • x)
  filter_upwards [hinv.eventually hz] with y hy
  simpa only [smul_inv_smul₀ ht] using hy

theorem fiber_polynomial_scaleRoots {n d : ℕ}
    {S : Set ((Fin n → ℂ) × ℂ)}
    (hcone : ∀ t : ℂ, ∀ p ∈ S, t • p ∈ S)
    {P : (Fin n → ℂ) → ℂ[X]}
    (hcoeff : ∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) {0}ᶜ)
    (hP : ∀ y, y ≠ 0 → (P y).Monic ∧ (P y).natDegree = d)
    (hnear : ∀ x, x ≠ 0 → ∃ (U : Set (Fin n → ℂ)) (c : (Fin n → ℂ) → ℂ),
      IsOpen U ∧ x ∈ U ∧ U ⊆ {0}ᶜ ∧ DifferentiableOn ℂ c U ∧
      (¬∀ᶠ y in 𝓝 x, c y = 0) ∧
      ∀ y ∈ U, c y ≠ 0 → (P y).Separable ∧
        ∀ z : ℂ, (y, z) ∈ S ↔ (P y).eval z = 0)
    {t : ℂ} (ht : t ≠ 0) {x : Fin n → ℂ} (hx : x ≠ 0) :
    P (t • x) = (P x).scaleRoots t := by
  have htx : t • x ≠ 0 := smul_ne_zero ht hx
  obtain ⟨U₁, c₁, hU₁, hxU₁, hU₁0, hc₁, hc₁n, hroot₁⟩ := hnear x hx
  obtain ⟨U₂, c₂, hU₂, hxU₂, hU₂0, hc₂, hc₂n, hroot₂⟩ := hnear (t • x) htx
  have hscale : Differentiable ℂ (fun y : Fin n → ℂ => t • y) := differentiable_id.const_smul t
  let W := U₁ ∩ (fun y : Fin n → ℂ => t • y) ⁻¹' U₂
  have hW : IsOpen W := hU₁.inter (hU₂.preimage hscale.continuous)
  have hxW : x ∈ W := ⟨hxU₁, hxU₂⟩
  have hW0 : W ⊆ ({0}ᶜ : Set (Fin n → ℂ)) := fun y hy => hU₁0 hy.1
  let A : (Fin n → ℂ) → ℂ[X] := fun y => (P y).scaleRoots t
  let B : (Fin n → ℂ) → ℂ[X] := fun y => P (t • y)
  have hAcoeff (j : ℕ) : DifferentiableOn ℂ (fun y => (A y).coeff j) W := by
    apply ((hcoeff j).mono hW0).mul_const (t ^ (d - j)) |>.congr
    intro y hy
    exact (coeff_scaleRoots (P y) t j).trans (by rw [(hP y (hW0 hy)).2])
  have hBcoeff (j : ℕ) : DifferentiableOn ℂ (fun y => (B y).coeff j) W :=
    (hcoeff j).comp hscale.differentiableOn (fun y hy => hU₂0 hy.2)
  have hc₂W : DifferentiableOn ℂ (fun y => c₂ (t • y)) W :=
    hc₂.comp hscale.differentiableOn (fun _ hy => hy.2)
  have heq : A =ᶠ[𝓝 x] B := by
    apply CoefficientExtension.Constructions.GenericPolynomial.eventually_eq_of_generic_roots hW hxW
      (hc₁.mono inter_subset_left) hc₂W hc₁n (nonzero_germ_comp_smul ht hc₂n)
      (fun j => (hAcoeff j).continuousOn) (fun j => (hBcoeff j).continuousOn)
    intro y hy hcy₁ hcy₂
    have hy0 : y ≠ 0 := hW0 hy
    have hty0 : t • y ≠ 0 := hU₂0 hy.2
    obtain ⟨hsep₁, hroots₁⟩ := hroot₁ y hy.1 hcy₁
    obtain ⟨hsep₂, hroots₂⟩ := hroot₂ (t • y) hy.2 hcy₂
    refine ⟨(monic_scaleRoots_iff t).mpr (hP y hy0).1, (hP (t • y) hty0).1,
      separable_scaleRoots hsep₁ ht, hsep₂, ?_⟩
    intro z
    have hz : t * (t⁻¹ * z) = z := by rw [← mul_assoc, mul_inv_cancel₀ ht, one_mul]
    change ((P y).scaleRoots t).eval z = 0 ↔ (P (t • y)).eval z = 0
    rw [← hz, scaleRoots_eval_mul, mul_eq_zero, or_iff_right (pow_ne_zero _ ht)]
    rw [← hroots₁, ← hroots₂]
    constructor
    · intro hp
      have h := hcone t (y, t⁻¹ * z) hp
      exact h
    · intro hp
      have h := hcone t⁻¹ (t • y, t * (t⁻¹ * z)) hp
      change (t⁻¹ • (t • y), t⁻¹ * (t * (t⁻¹ * z))) ∈ S at h
      simpa only [inv_smul_smul₀ ht, inv_mul_cancel_left₀ ht] using h
  exact heq.eq_of_nhds.symm

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCoefficientScaling.Constructions.Cone
