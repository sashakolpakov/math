import OAI.Analysis.PDE.Green.BoxGreen
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory

def coordinateDivergence {m : ℕ} (F : (Fin m → ℝ) → (Fin m → ℝ)) (x : Fin m → ℝ) : ℝ :=
  ∑ i, (fderiv ℝ F x (Pi.single i 1)) i

theorem coordinateDivergence_eq_trace {m : ℕ}
    (F : (Fin m → ℝ) → (Fin m → ℝ)) (x : Fin m → ℝ) :
    coordinateDivergence F x = LinearMap.trace ℝ (Fin m → ℝ) (fderiv ℝ F x).toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin m))]
  simp [coordinateDivergence, Matrix.trace]

theorem coordinateDivergence_eq_components {m : ℕ}
    {F : (Fin m → ℝ) → (Fin m → ℝ)} {x : Fin m → ℝ} (hF : DifferentiableAt ℝ F x) :
    coordinateDivergence F x = ∑ i, fderiv ℝ (fun y => F y i) x (Pi.single i 1) := by
  apply Finset.sum_congr rfl
  intro i hi
  have h := ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x
    hF.hasFDerivAt).fderiv
  exact (congrArg (fun D : (Fin m → ℝ) →L[ℝ] ℝ => D (Pi.single i 1)) h).symm

/-- The constant-linear Piola pullback, with its common Jacobian factor
omitted. The factor cancels from every zero-divergence Green identity. -/
def linearPiola {m : ℕ} (L : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    (F : (Fin m → ℝ) → (Fin m → ℝ)) : (Fin m → ℝ) → (Fin m → ℝ) :=
  L.symm ∘ F ∘ L

theorem coordinateDivergence_linearPiola {m : ℕ}
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    {F : (Fin m → ℝ) → (Fin m → ℝ)} {x : Fin m → ℝ}
    (hF : DifferentiableAt ℝ F (L x)) :
    coordinateDivergence (linearPiola L F) x = coordinateDivergence F (L x) := by
  have hd := L.symm.toContinuousLinearMap.hasFDerivAt.comp x
    (hF.hasFDerivAt.comp x L.toContinuousLinearMap.hasFDerivAt)
  have he : fderiv ℝ (linearPiola L F) x =
      L.symm.toContinuousLinearMap.comp ((fderiv ℝ F (L x)).comp L.toContinuousLinearMap) :=
    hd.fderiv
  rw [coordinateDivergence_eq_trace, coordinateDivergence_eq_trace]
  rw [he]
  exact LinearMap.trace_conj' (fderiv ℝ F (L x)).toLinearMap L.symm.toLinearEquiv

theorem contDiff_linearPiola {m : ℕ}
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    {F : (Fin m → ℝ) → (Fin m → ℝ)} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (linearPiola L F) :=
  L.symm.contDiff.comp (hF.comp L.contDiff)

theorem sum_fderiv_coordinate_mul {m : ℕ} (f : (Fin m → ℝ) → ℝ)
    (x v : Fin m → ℝ) :
    (∑ i, fderiv ℝ f x (Pi.single i 1) * v i) = fderiv ℝ f x v := by
  have hv : (∑ i, v i • Pi.single i (1 : ℝ)) = v := by
    ext j
    simp [Pi.single_apply]
  calc
    _ = fderiv ℝ f x (∑ i, v i • Pi.single i 1) := by
      simp [map_sum, map_smul, smul_eq_mul, mul_comm]
    _ = _ := congrArg (fderiv ℝ f x) hv

theorem fderiv_linearPiola_normal {m : ℕ}
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) (F : (Fin m → ℝ) → (Fin m → ℝ))
    {r : (Fin m → ℝ) → ℝ} {x : Fin m → ℝ} (hr : DifferentiableAt ℝ r (L x)) :
    fderiv ℝ (r ∘ L) x (linearPiola L F x) = fderiv ℝ r (L x) (F (L x)) := by
  have hd : fderiv ℝ (r ∘ L) x = (fderiv ℝ r (L x)).comp L.toContinuousLinearMap :=
    (hr.hasFDerivAt.comp x L.toContinuousLinearMap.hasFDerivAt).fderiv
  rw [hd]
  simp [linearPiola, Function.comp_def]

theorem fderiv_comp_equiv_ne_zero {m : ℕ}
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    {r : (Fin m → ℝ) → ℝ} {x : Fin m → ℝ} (hr : DifferentiableAt ℝ r (L x))
    (hne : fderiv ℝ r (L x) ≠ 0) : fderiv ℝ (r ∘ L) x ≠ 0 := by
  have hd : fderiv ℝ (r ∘ L) x = (fderiv ℝ r (L x)).comp L.toContinuousLinearMap :=
    (hr.hasFDerivAt.comp x L.toContinuousLinearMap.hasFDerivAt).fderiv
  intro hz
  apply hne
  ext v
  have hh := congrArg (fun D : (Fin m → ℝ) →L[ℝ] ℝ => D (L.symm v)) (hd.symm.trans hz)
  simpa using hh

end OAI.Analysis.PDE.Concentration
