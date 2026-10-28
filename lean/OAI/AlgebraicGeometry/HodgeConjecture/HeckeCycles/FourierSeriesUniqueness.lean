import Mathlib.Analysis.Fourier.AddCircleMulti

/-! # Fourier Series Uniqueness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FourierSeriesUniqueness

noncomputable section

/-! The coefficients of a uniformly convergent torus Fourier series are
uniquely determined, using the actual orthonormal Fourier basis in L2. -/

open scoped Classical ComplexConjugate InnerProductSpace
open _root_.MeasureTheory UnitAddTorus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace CM

variable {I : Type} [Fintype I]

theorem coefficient {c : (I → ℤ) → ℂ} {f : C(UnitAddTorus I, ℂ)}
    (h : HasSum (fun n => c n • mFourier n) f) (k : I → ℤ) :
    mFourierCoeff f k = c k := by
  have hL := h.mapL (ContinuousMap.toLp 2 volume ℂ)
  let l : Lp ℂ 2 (volume : Measure (UnitAddTorus I)) →L[ℂ] ℂ := innerSL ℂ (mFourierLp 2 k)
  have hi := l.hasSum hL
  have he : (fun n => inner ℂ (mFourierLp 2 k)
      ((ContinuousMap.toLp 2 volume ℂ) (c n • mFourier n))) =
      (fun n => if n = k then c k else 0) := by
    funext n
    rw [map_smul]
    change inner ℂ (mFourierLp 2 k) (c n • mFourierLp 2 n) = _
    rw [inner_smul_right, (orthonormal_iff_ite.mp orthonormal_mFourier) k n]
    by_cases hn : n = k
    · subst n
      simp
    · simp [hn, Ne.symm hn]
  change HasSum (fun n => inner ℂ (mFourierLp 2 k)
    ((ContinuousMap.toLp 2 volume ℂ) (c n • mFourier n))) _ at hi
  rw [he] at hi
  have hv : inner ℂ (mFourierLp 2 k) ((ContinuousMap.toLp 2 volume ℂ) f) = c k :=
    hi.unique (hasSum_ite_eq k (c k))
  calc
    mFourierCoeff f k = mFourierCoeff ((ContinuousMap.toLp 2 volume ℂ) f) k :=
      (mFourierCoeff_toLp f k).symm
    _ = mFourierBasis.repr ((ContinuousMap.toLp 2 volume ℂ) f) k := (mFourierBasis_repr _ k).symm
    _ = inner ℂ (mFourierLp 2 k) ((ContinuousMap.toLp 2 volume ℂ) f) := by
      rw [HilbertBasis.repr_apply_apply, coe_mFourierBasis]
    _ = c k := hv

theorem coefficients_eq {c b : (I → ℤ) → ℂ} {f : C(UnitAddTorus I, ℂ)}
    (hc : HasSum (fun n => c n • mFourier n) f)
    (hb : HasSum (fun n => b n • mFourier n) f) : c = b := by
  funext k
  exact (coefficient hc k).symm.trans (coefficient hb k)

theorem summable {c : (I → ℤ) → ℂ} (hc : Summable (fun n => ‖c n‖)) :
    Summable (fun n => c n • mFourier n) := by
  apply Summable.of_norm
  simpa only [norm_smul, mFourier_norm, mul_one] using hc

theorem tsum_injective {c b : (I → ℤ) → ℂ}
    (hc : Summable (fun n => ‖c n‖)) (hb : Summable (fun n => ‖b n‖))
    (h : (∑' n, c n • mFourier n) = ∑' n, b n • mFourier n) : c = b :=
  coefficients_eq (h ▸ (summable hc).hasSum) (summable hb).hasSum

end CM

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FourierSeriesUniqueness
