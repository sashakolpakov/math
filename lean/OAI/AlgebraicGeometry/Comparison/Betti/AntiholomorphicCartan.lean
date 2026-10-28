import OAI.AlgebraicGeometry.Comparison.Betti.DolbeaultContractionAlgebra
import OAI.AlgebraicGeometry.Comparison.Betti.AntilinearCoefficientMap

/-! # Antiholomorphic Cartan -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicCartan.Dolbeault

noncomputable section

section

/-! The actual Cartan identity for antiholomorphic contraction and the
antiholomorphic exterior differential, in every positive form degree. -/

open _root_.ContinuousAlternatingMap

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
theorem antiContraction_derivative (n : ℕ) (v : E)
    (D : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    (AntiholomorphicContraction.Dolbeault.antiContraction n v).restrictScalars ℝ ∘L D =
      (1 / 2 : ℂ) • (AlgebraicTopology.DeRham.Comparison.RadialOne.contractionDerivative D v +
        Complex.I • AlgebraicTopology.DeRham.Comparison.RadialOne.contractionDerivative D (Complex.I • v)) := by
  ext u w
  rfl

theorem dolbeault_antiContraction_add (n : ℕ) (v : E)
    (D : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    alternatizeUncurryFin
        (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E [⋀^Fin n]→L[ℝ] ℂ)
          ((AntiholomorphicContraction.Dolbeault.antiContraction n v).restrictScalars ℝ ∘L D)) +
      AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) v
        (alternatizeUncurryFin
          (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E [⋀^Fin (n + 1)]→L[ℝ] ℂ) D)) =
      Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E [⋀^Fin (n + 1)]→L[ℝ] ℂ) D v := by
  let A := Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E [⋀^Fin (n + 1)]→L[ℝ] ℂ) D
  rw [AntilinearCoefficientMap.Dolbeault.complexAntilinearPart_comp_coefficients, antiContraction_derivative,
    alternatizeUncurryFin_smul, alternatizeUncurryFin_add, alternatizeUncurryFin_smul]
  change (1 / 2 : ℂ) • (alternatizeUncurryFin (AlgebraicTopology.DeRham.Comparison.RadialOne.contractionDerivative A v) +
      Complex.I • alternatizeUncurryFin (AlgebraicTopology.DeRham.Comparison.RadialOne.contractionDerivative A (Complex.I • v))) +
    (1 / 2 : ℂ) • ((alternatizeUncurryFin A).curryLeft v +
      Complex.I • (alternatizeUncurryFin A).curryLeft (Complex.I • v)) = A v
  calc
    _ = (1 / 2 : ℂ) •
        ((alternatizeUncurryFin (AlgebraicTopology.DeRham.Comparison.RadialOne.contractionDerivative A v) +
          (alternatizeUncurryFin A).curryLeft v) +
        Complex.I • (alternatizeUncurryFin (AlgebraicTopology.DeRham.Comparison.RadialOne.contractionDerivative A (Complex.I • v)) +
          (alternatizeUncurryFin A).curryLeft (Complex.I • v))) := by module
    _ = (1 / 2 : ℂ) • (A v + Complex.I • A (Complex.I • v)) := by
      rw [AlgebraicTopology.DeRham.Comparison.RadialOne.alternatize_contractionDerivative_add,
        AlgebraicTopology.DeRham.Comparison.RadialOne.alternatize_contractionDerivative_add]
    _ = A v := by
      have hI : A (Complex.I • v) = -Complex.I • A v :=
        Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_I_smul E (E [⋀^Fin (n + 1)]→L[ℝ] ℂ) D v
      rw [hI, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
      module

end

/-! The actual local Cartan formula for constant antiholomorphic tangent
contraction, with the genuine Fréchet and exterior derivatives. -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

theorem extDerivDoublePrime_antiContraction (n : ℕ) (v : E)
    (a : Analysis.DifferentialForms.Manifold.Basic.RawForm E (n + 1)) {x : E} (ha : DifferentiableAt ℝ a x) :
    Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (fun y => AntiholomorphicContraction.Dolbeault.antiContraction n v (a y)) x +
      AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) v (Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a x) =
        Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E [⋀^Fin (n + 1)]→L[ℝ] ℂ) (fderiv ℝ a x) v := by
  have hd : fderiv ℝ (fun y => AntiholomorphicContraction.Dolbeault.antiContraction n v (a y)) x =
      (AntiholomorphicContraction.Dolbeault.antiContraction n v).restrictScalars ℝ ∘L fderiv ℝ a x :=
    (((AntiholomorphicContraction.Dolbeault.antiContraction n v).restrictScalars ℝ).hasFDerivAt.comp x ha.hasFDerivAt).fderiv
  unfold Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime
  rw [hd]
  exact dolbeault_antiContraction_add n v (fderiv ℝ a x)

end

end OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicCartan.Dolbeault
