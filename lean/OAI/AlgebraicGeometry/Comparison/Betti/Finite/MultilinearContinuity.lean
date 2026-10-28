import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! # Multilinear Continuity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.MultilinearContinuity.LinearAlgebra

noncomputable section

/-! Scalar multilinear maps on finite-dimensional complex spaces are continuous. -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem multilinear_continuous (n : ℕ) (f : MultilinearMap ℂ (fun _ : Fin n => E) ℂ) :
    Continuous f := by
  classical
  let bE := Module.finBasis ℂ E
  let bF := Module.finBasis ℂ ℂ
  let b := Basis.multilinearMap (fun _ : Fin n => bE) bF
  have hB (i : (Fin n → Fin (Module.finrank ℂ E)) × Fin (Module.finrank ℂ ℂ)) :
      Continuous (b i) := by
    have hi : (b i : (Fin n → E) → ℂ) =
        fun v => (∏ j, bE.repr (v j) (i.1 j)) • bF i.2 :=
      funext (Basis.multilinearMap_apply_apply (fun _ : Fin n => bE) bF i)
    rw [hi]
    change Continuous (fun v : Fin n → E => (∏ j, bE.repr (v j) (i.1 j)) * bF i.2)
    have hp : Continuous (fun v : Fin n → E => ∏ j, bE.repr (v j) (i.1 j)) := by
      apply continuous_finsetProd
      intro j _
      exact ((bE.coord (i.1 j)).toContinuousLinearMap.continuous).comp (continuous_apply j)
    exact hp.mul_const (bF i.2)
  have heq : (f : (Fin n → E) → ℂ) = fun v => ∑ i, b.repr f i • b i v := by
    funext v
    have h := congrArg (fun g : MultilinearMap ℂ (fun _ : Fin n => E) ℂ => g v) (b.sum_repr f)
    simpa only [sum_apply, smul_apply] using h.symm
  rw [heq]
  apply continuous_finsetSum
  intro i _
  change Continuous (fun v => b.repr f i * b i v)
  exact (hB i).const_mul _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.MultilinearContinuity.LinearAlgebra
