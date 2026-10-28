import OAI.Analysis.PDE.Dirichlet.C2HolderCoefficient
import OAI.Analysis.Normed.Function.Holder.Banach.Bilinear
import OAI.LinearAlgebra.Moore.Monotone

/-! Uniform Hölder bounds for the true logarithmic Moore coefficient.
The only denominator bound is the actual positive determinant bound; it
is also derived here from a uniform positive Hessian lower bound. -/

noncomputable section
open Set
open scoped Matrix.Norms.Elementwise BoundedContinuousFunction MatrixOrder ComplexOrder

namespace OAI.Analysis.Normed.Function.Holder.HolderMap

variable {X : Type*} [MetricSpace X] {α : ℝ}

theorem exists_positive_reciprocal (hα : 0 ≤ α) (f : HolderMap X ℝ α)
    {μ : ℝ} (hμ : 0 < μ) (hf : ∀ x, μ ≤ HolderMap.value f x) :
    ∃ g : HolderMap X ℝ α, (∀ x, HolderMap.value g x = (HolderMap.value f x)⁻¹) ∧
      ‖g‖ ≤ μ⁻¹ + (μ*μ)⁻¹ * ‖f‖ := by
  have hp (x : X) : 0 < HolderMap.value f x := hμ.trans_le (hf x)
  let g : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (HolderMap.value f x)⁻¹)
    ((HolderMap.value f).continuous.inv₀ (fun x => (hp x).ne')) μ⁻¹ (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hp x))]
      exact inv_anti₀ hμ (hf x))
  have hg : ∀ x y, ‖g x-g y‖ ≤ ((μ*μ)⁻¹ * ‖f‖) * (dist x y)^α := by
    intro x y
    have hxy : 0 < HolderMap.value f x * HolderMap.value f y := mul_pos (hp x) (hp y)
    have hprod : μ*μ ≤ HolderMap.value f x * HolderMap.value f y := mul_le_mul (hf x) (hf y) hμ.le (hp x).le
    have hi : (HolderMap.value f x)⁻¹-(HolderMap.value f y)⁻¹ =
        (HolderMap.value f y-HolderMap.value f x)/(HolderMap.value f x*HolderMap.value f y) := by
      field_simp [(hp x).ne', (hp y).ne']
    change ‖(HolderMap.value f x)⁻¹-(HolderMap.value f y)⁻¹‖ ≤ _
    rw [hi, norm_div, Real.norm_of_nonneg hxy.le, norm_sub_rev]
    calc
      _ ≤ (‖f‖*(dist x y)^α)/(μ*μ) :=
        div_le_div₀ (by positivity) (HolderMap.norm_sub_le f x y) (mul_pos hμ hμ) hprod
      _ = _ := by ring
  refine ⟨HolderMap.ofBounded hα g hg, fun x => rfl, ?_⟩
  have hgn : ‖g‖ ≤ μ⁻¹ := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (inv_nonneg.mpr hμ.le) _
  apply (HolderMap.norm_ofBounded_le hα g (by positivity) hg).trans
  exact max_le ((hgn.trans (le_add_of_nonneg_right (by positivity))))
    (le_add_of_nonneg_left (by positivity))

end OAI.Analysis.Normed.Function.Holder.HolderMap
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic OAI.Analysis.Normed.Function.Holder

local instance logCoefficientEndGroup (n : ℕ) :
    NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) := inferInstance
local instance logCoefficientEndSpace (n : ℕ) :
    NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) := inferInstance
local instance logCoefficientEndEndGroup (n : ℕ) :
    NormedAddCommGroup ((OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) →L[ℝ]
      (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)) := inferInstance
local instance logCoefficientEndEndSpace (n : ℕ) :
    NormedSpace ℝ ((OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) →L[ℝ]
      (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)) := inferInstance

theorem logRealOperator_eq_smul_detRealOperator {n : ℕ}
    (A : Matrix (Fin n) (Fin n) OAI.Analysis.PDE.Dirichlet.Q) :
    OAI.Analysis.PDE.Dirichlet.logRealOperator A = (OAI.LinearAlgebra.Moore.mooreDet n A)⁻¹ • OAI.Analysis.PDE.Dirichlet.detRealOperator A := by
  unfold OAI.Analysis.PDE.Dirichlet.logRealOperator OAI.Analysis.PDE.Dirichlet.detRealOperator OAI.Analysis.PDE.Elliptic.symmetricTraceDual
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  change ((OAI.LinearAlgebra.Moore.mooreDet n A)⁻¹ * OAI.Analysis.PDE.Dirichlet.detOperatorFunctional A _) / 2 = _
  ring

/-- The constants are chosen before the field and its base metric space
points. No derivatives of the Hessian field enter this estimate. -/
theorem exists_logRealOperator_holder_bound {X : Type*} [MetricSpace X]
    (n : ℕ) {α R μ : ℝ} (hα : 0 ≤ α) (hR : 0 ≤ R) (hμ : 0 < μ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ A : HolderMap X (Matrix (Fin n) (Fin n) OAI.Analysis.PDE.Dirichlet.Q) α, ‖A‖ ≤ R →
      (∀ x, μ ≤ OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x)) →
      ∃ B : HolderMap X (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x)) ∧ ‖B‖ ≤ C := by
  obtain ⟨Cd, hCd, hd⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_compose_contDiff_bound
    (X := X) (OAI.LinearAlgebra.Moore.contDiff_mooreDet n 1) hα hR
  obtain ⟨Ca, hCa, ha⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_compose_contDiff_bound
    (X := X) (OAI.Analysis.PDE.Dirichlet.contDiff_detRealOperator n 1) hα hR
  let L : ℝ →L[ℝ] (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) →L[ℝ]
      (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) := ContinuousLinearMap.lsmul ℝ ℝ
  let C := (2*‖L‖) * (μ⁻¹+(μ*μ)⁻¹*(Cd*(1+R))) * (Ca*(1+R))
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro A hA hdet
  obtain ⟨d, hed, hdn⟩ := hd A hA
  obtain ⟨a, hea, han⟩ := ha A hA
  obtain ⟨dI, heI, hIn⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_positive_reciprocal hα d hμ
    (fun x => by rw [hed]; exact hdet x)
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.bilinear hα L dI a, ?_, ?_⟩
  · intro x
    rw [OAI.Analysis.Normed.Function.Holder.HolderMap.value_bilinear, heI, hed, hea, OAI.Analysis.PDE.Dirichlet.logRealOperator_eq_smul_detRealOperator]
    rfl
  · apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_bilinear_le hα L dI a).trans
    have hd' : ‖d‖ ≤ Cd*(1+R) := hdn.trans (mul_le_mul_of_nonneg_left (by linarith) hCd)
    have ha' : ‖a‖ ≤ Ca*(1+R) := han.trans (mul_le_mul_of_nonneg_left (by linarith) hCa)
    have hi' : ‖dI‖ ≤ μ⁻¹+(μ*μ)⁻¹*(Cd*(1+R)) := hIn.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd'
        (inv_nonneg.mpr (mul_nonneg hμ.le hμ.le))))
    dsimp only [C]
    gcongr

theorem mooreDet_lower_of_uniform_positive {n : ℕ}
    (A : Matrix (Fin n) (Fin n) OAI.Analysis.PDE.Dirichlet.Q) {lam : ℝ} (hlam : 0 < lam)
    (hA : (OAI.LinearAlgebra.Moore.complexify (A - lam • 1)).PosSemidef) : lam^n ≤ OAI.LinearAlgebra.Moore.mooreDet n A := by
  have hI : (OAI.LinearAlgebra.Moore.complexify (lam • (1 : Matrix (Fin n) (Fin n) OAI.Analysis.PDE.Dirichlet.Q))).PosDef := by
    rw [OAI.LinearAlgebra.Moore.complexify_real_smul, OAI.LinearAlgebra.Moore.complexify_one]
    exact Matrix.PosDef.one.smul hlam
  simpa only [OAI.LinearAlgebra.Moore.mooreDet_smul, OAI.LinearAlgebra.Moore.mooreDet_identity, mul_one] using
    OAI.LinearAlgebra.Moore.mooreDet_le_of_posSemidef_difference (lam • 1) A hI hA

/-- Uniform positive Hessians on a bounded Hölder ball yield a bounded
Hölder logarithmic coefficient field. The determinant lower bound is
proved, not an extra hypothesis. -/
theorem exists_logRealOperator_holder_bound_of_uniform_positive
    {X : Type*} [MetricSpace X] (n : ℕ) {α R lam : ℝ}
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ A : HolderMap X (Matrix (Fin n) (Fin n) OAI.Analysis.PDE.Dirichlet.Q) α, ‖A‖ ≤ R →
      (∀ x, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x - lam • 1)).PosSemidef) →
      ∃ B : HolderMap X (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x)) ∧ ‖B‖ ≤ C := by
  obtain ⟨C, hC, hc⟩ := OAI.Analysis.PDE.Dirichlet.exists_logRealOperator_holder_bound (X := X) n hα hR (pow_pos hlam n)
  exact ⟨C, hC, fun A hA hp => hc A hA (fun x =>
    OAI.Analysis.PDE.Dirichlet.mooreDet_lower_of_uniform_positive _ hlam (hp x))⟩

/-- Banach-space form used by the nonlinear boundary bootstrap.  The
constant is uniform over the entire bounded family of potentials. -/
theorem exists_logRealCoefficient_bound {n : ℕ}
    {Ω K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} {hΩK : Ω ⊆ K} {α R μ : ℝ}
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hμ : 0 < μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : C2Holder (F := ℝ) hΩK α, ‖U‖ ≤ R →
      (∀ x : K, μ ≤ OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots U) x)) →
      ∃ B : HolderMap K (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) α,
        (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x =
          OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots U) x)) ∧
        ‖B‖ ≤ C := by
  let J := OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots
  obtain ⟨C, hC, hc⟩ := OAI.Analysis.PDE.Dirichlet.exists_logRealOperator_holder_bound (X := K) n hα
    (mul_nonneg (norm_nonneg J) hR) hμ
  refine ⟨C, hC, fun U hU hdet => hc (J U) ?_ hdet⟩
  exact (J.le_opNorm U).trans (mul_le_mul_of_nonneg_left hU (norm_nonneg J))

theorem exists_logRealCoefficient_bound_of_uniform_positive {n : ℕ}
    {Ω K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} {hΩK : Ω ⊆ K} {α R lam : ℝ}
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : C2Holder (F := ℝ) hΩK α, ‖U‖ ≤ R →
      (∀ x : K, (OAI.LinearAlgebra.Moore.complexify
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots U) x - lam • 1)).PosSemidef) →
      ∃ B : HolderMap K (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) α,
        (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x =
          OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots U) x)) ∧
        ‖B‖ ≤ C := by
  obtain ⟨C, hC, hc⟩ := OAI.Analysis.PDE.Dirichlet.exists_logRealCoefficient_bound (hΩK := hΩK) hα hR (pow_pos hlam n)
  exact ⟨C, hC, fun U hU hp => hc U hU (fun x =>
    OAI.Analysis.PDE.Dirichlet.mooreDet_lower_of_uniform_positive _ hlam (hp x))⟩

end OAI.Analysis.PDE.Dirichlet
