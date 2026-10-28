import OAI.Analysis.Fourier.Estimates

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section
namespace OAI.Analysis.Fourier.Cone

/-- The usual parametrization of the forward light cone. -/
def coneParam {n : ℕ} (p : ℝ × Space n) : Space n × ℝ :=
  (p.1 • p.2, p.1)

/-- Euclidean inner product on spatial/time pairs, written explicitly to avoid
using the max product norm. -/
def coneInner {n : ℕ} (v w : Space n × ℝ) : ℝ :=
  inner ℝ v.1 w.1 + v.2 * w.2

/-- Tangent vectors of the cone parametrization in an orthonormal spherical
frame: the radial vector first, then the angular vectors. -/
def coneTangent {n d : ℕ} (ρ : ℝ) (ω : Space n) (v : Fin d → Space n) :
    Option (Fin d) → Space n × ℝ
  | none => (ω, 1)
  | some i => (ρ • v i, 0)

theorem coneTangent_gram {n d : ℕ} (ρ : ℝ) (ω : Space n)
    (v : Fin d → Space n) (hω : inner ℝ ω ω = 1)
    (hv : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (ht : ∀ i, inner ℝ ω (v i) = 0) :
    (fun i j => coneInner (coneTangent ρ ω v i) (coneTangent ρ ω v j)) =
      Matrix.diagonal (fun i : Option (Fin d) => match i with
        | none => 2 | some _ => ρ ^ 2) := by
  funext i j
  cases i with
  | none =>
    cases j with
    | none => simpa only [coneTangent, coneInner, hω, Matrix.diagonal_apply_eq] using
        (show (1 : ℝ) + 1 * 1 = 2 by norm_num)
    | some j =>
      change inner ℝ ω (ρ • v j) + 1 * 0 = 0
      rw [real_inner_smul_right, ht]
      ring
  | some i =>
    cases j with
    | none =>
      change inner ℝ (ρ • v i) ω + 0 * 1 = 0
      rw [real_inner_smul_left, real_inner_comm, ht]
      ring
    | some j =>
      simp only [coneTangent, coneInner, real_inner_smul_left, real_inner_smul_right,
        hv, mul_zero, add_zero, Matrix.diagonal_apply, Option.some.injEq]
      split_ifs <;> simp [pow_two]

/-- The first fundamental form has determinant `2 ρ^(2d)`. Thus its volume
density is exactly the standard induced cone surface density. -/
theorem coneTangent_volume_density {n d : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (ω : Space n) (v : Fin d → Space n) (hω : inner ℝ ω ω = 1)
    (hv : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (ht : ∀ i, inner ℝ ω (v i) = 0) :
    Real.sqrt (Matrix.det (fun i j =>
      coneInner (coneTangent ρ ω v i) (coneTangent ρ ω v j))) =
      Real.sqrt 2 * ρ ^ d := by
  rw [coneTangent_gram ρ ω v hω hv ht, Matrix.det_diagonal]
  simp only [Fintype.prod_option, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm 2 d, pow_mul, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (pow_nonneg hρ d)]

theorem hasFDerivAt_coneParam {n : ℕ} (ρ : ℝ) (ω : Space n) :
    HasFDerivAt (@coneParam n)
      (((ContinuousLinearMap.fst ℝ ℝ (Space n)).smulRight ω +
        ρ • ContinuousLinearMap.snd ℝ ℝ (Space n)).prod
          (ContinuousLinearMap.fst ℝ ℝ (Space n))) (ρ, ω) := by
  have h1 : HasFDerivAt (fun p : ℝ × Space n => p.1)
      (ContinuousLinearMap.fst ℝ ℝ (Space n)) (ρ, ω) := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p : ℝ × Space n => p.2)
      (ContinuousLinearMap.snd ℝ ℝ (Space n)) (ρ, ω) := hasFDerivAt_snd
  simpa only [coneParam, Pi.smul_apply, add_comm] using! (h1.smul h2).prodMk h1

end OAI.Analysis.Fourier.Cone
