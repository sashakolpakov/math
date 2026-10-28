import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ConvergenceLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.EulerIndex
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpectralSequenceEuler

/-! # Convergence Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ConvergenceEuler

noncomputable section

/-! Euler characteristics of a finite tensor spectral page agree with
those of the actual total tensor complex. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExactLength

variable (R : Type) [CommRing R] (A K : CochainComplex (ModuleCat.{0} R) ℤ)

theorem zero_length (M : ModuleCat.{0} R) (h : IsZero M) : Module.length R M = 0 := by
  let := ModuleCat.subsingleton_of_isZero h
  exact Module.length_eq_zero

theorem rationalLength_zero (M : ModuleCat.{0} R) (h : IsZero M) : ExactLength.rationalLength R M = 0 := by
  simp only [ExactLength.rationalLength, zero_length R M h, ENat.toNat_zero, Nat.cast_zero]

theorem length_finite (M : ℤ × ℤ → ModuleCat.{0} R) (F : Finset (ℤ × ℤ))
    (hout : ∀ pq, pq ∉ F → IsZero (M pq)) (hlen : ∀ pq ∈ F, Module.length R (M pq) ≠ ⊤)
    (pq : ℤ × ℤ) : Module.length R (M pq) ≠ ⊤ := by
  by_cases h : pq ∈ F
  · exact hlen pq h
  · rw [zero_length R _ (hout pq h)]
    simp

theorem late_euler (d : ℕ) (hl : ∀ i, i < -(d : ℤ) → IsZero (A.X i))
    (hu : ∀ i, 0 < i → IsZero (A.X i)) (r : ℤ) (hr : (d : ℤ) + 3 ≤ r)
    (F : Finset (ℤ × ℤ)) (N : Finset ℤ)
    (hout : ∀ pq, pq ∉ F → IsZero (((BrutalTensorSpectralSequence.spectralSequence R A K).page r (by omega)).X pq))
    (hlen : ∀ pq ∈ F, Module.length R (((BrutalTensorSpectralSequence.spectralSequence R A K).page r (by omega)).X pq) ≠ ⊤)
    (hdegree : ∀ pq ∈ F, pq.1 + pq.2 ∈ N)
    (hstrip : ∀ pq ∈ F, 0 ≤ pq.2 + 1 ∧ pq.2 + 1 ≤ (d : ℤ)) (w : ℤ → ℚ) :
    (∑ n ∈ N, w n * ExactLength.rationalLength R (((Homotopy.complexFunctor R K).obj A).homology n)) =
      ∑ pq ∈ F, w (pq.1 + pq.2) * ExactLength.rationalLength R
        (((BrutalTensorSpectralSequence.spectralSequence R A K).page r (by omega)).X pq) := by
  let S : ℤ × ℤ → ModuleCat.{0} R :=
    ((BrutalTensorSpectralSequence.spectralSequence R A K).page r (by omega)).X
  have hfinite := length_finite R S F hout hlen
  have hzero : ∀ pq, pq ∉ F → ExactLength.rationalLength R (S pq) = 0 :=
    fun pq hpq => rationalLength_zero R _ (hout pq hpq)
  calc
    _ = ∑ n ∈ N, w n * ∑ i ∈ Finset.range (d + 1),
        ExactLength.rationalLength R (S (EulerIndex.position (n, i))) := by
      apply Finset.sum_congr rfl
      intro n _
      congr 1
      exact ConvergenceLength.total_rationalLength_latePage R A K d hl hu r hr n
        (fun i _ => hfinite _)
    _ = _ := EulerIndex.sum_by_degree F N d hdegree hstrip (fun pq => ExactLength.rationalLength R (S pq)) hzero w

theorem euler_from_third_page (d : ℕ) (hl : ∀ i, i < -(d : ℤ) → IsZero (A.X i))
    (hu : ∀ i, 0 < i → IsZero (A.X i)) (F : Finset (ℤ × ℤ)) (N : Finset ℤ)
    (hout : ∀ pq, pq ∉ F → IsZero (((BrutalTensorSpectralSequence.spectralSequence R A K).page 3).X pq))
    (hlen : ∀ pq ∈ F, Module.length R (((BrutalTensorSpectralSequence.spectralSequence R A K).page 3).X pq) ≠ ⊤)
    (hdegree : ∀ pq ∈ F, pq.1 + pq.2 ∈ N)
    (hstrip : ∀ pq ∈ F, 0 ≤ pq.2 + 1 ∧ pq.2 + 1 ≤ (d : ℤ))
    (w : ℤ → ℚ)
    (hw : ∀ r : ℤ, 3 ≤ r → ∀ pq pq' : ℤ × ℤ,
      (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel pq pq' → w (pq.1 + pq.2) + w (pq'.1 + pq'.2) = 0) :
    (∑ n ∈ N, w n * ExactLength.rationalLength R (((Homotopy.complexFunctor R K).obj A).homology n)) =
      ∑ pq ∈ F, w (pq.1 + pq.2) * ExactLength.rationalLength R
        (((BrutalTensorSpectralSequence.spectralSequence R A K).page 3).X pq) := by
  have hp := SpectralSequenceEuler.later_pages_from R
    (BrutalTensorSpectralSequence.spectralSequence R A K) 3 (by omega) F hout hlen
    (fun pq => w (pq.1 + pq.2)) hw d
  exact (late_euler R A K d hl hu (3 + d) (by omega) F N hp.1 hp.2.1 hdegree hstrip w).trans hp.2.2

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ConvergenceEuler
