import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorCoordinates
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ScalarCoefficients
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Covector Reconstruction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorReconstruction.Holomorphic

noncomputable section

/-! A fixed continuous complex-linear reconstruction from finitely many actual coordinate values. -/

variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [Fintype ι] (b : Module.Basis ι ℂ E) (n : ℕ)

def rawCovectorCoordinates : (E [⋀^Fin n]→L[ℝ] ℂ) →L[ℂ] ((Fin n → ι) → ℂ) :=
  ContinuousLinearMap.pi (fun v => Holomorphic.ScalarCoefficients.complexCovectorEvaluation (fun i => b (v i)))

def pureCovectorReconstruction (b : Module.Basis ι ℂ E) (n : ℕ) :
    ((Fin n → ι) → ℂ) →L[ℂ] OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0 := by
  classical
  let L : ((Fin n → ι) → ℂ) →ₗ[ℂ] OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0 :=
    LinearMap.leftInverse (K := ℂ) (V := OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0)
      (V' := ((Fin n → ι) → ℂ)) (CovectorCoordinates.Holomorphic.pureCovectorCoordinates b n)
  exact LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ((Fin n → ι) → ℂ))
    (F' := OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) L

theorem pureCovectorReconstruction_coordinates (a : OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0) :
    pureCovectorReconstruction b n (CovectorCoordinates.Holomorphic.pureCovectorCoordinates b n a) = a :=
  LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (CovectorCoordinates.Holomorphic.pureCovectorCoordinates_injective b n)) a

def pureCovectorProjection : (E [⋀^Fin n]→L[ℝ] ℂ) →L[ℂ] OAI.Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0 :=
  (pureCovectorReconstruction b n).comp (rawCovectorCoordinates b n)

theorem pureCovectorProjection_eq_self (a : E [⋀^Fin n]→L[ℝ] ℂ) (ha : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 a) :
    (pureCovectorProjection b n a).val = a :=
  congrArg Subtype.val (pureCovectorReconstruction_coordinates b n ⟨a, ha⟩)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorReconstruction.Holomorphic
