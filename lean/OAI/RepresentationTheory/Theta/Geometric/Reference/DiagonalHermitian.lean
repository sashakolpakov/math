import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Matrices
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization
import OAI.NumberTheory.ArithmeticGroups.Trace

/-! # Diagonal Hermitian -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.DiagonalHermitian

noncomputable section

section

/-! The nondegenerate field trace recovers the literal reference
Hermitian form, including the original rational scaling coefficient. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Matrices.TraceReconstruction

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem reference_trace_reconstruction (ψ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] ℚ)
    (hψ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reconstruction.TraceReconstruction.RosatiBalanced (E := E) ψ) (ξ b : E) (hξ : ξ ≠ 0)
    (e : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (he : ∀ x y, ψ (e x) (e y) = Algebra.trace ℚ E (ξ * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y))
    (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Matrices.TraceReconstruction.hermitianMatrix ξ ψ hψ) (e x) (e y) =
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y := by
  have hc : AlgebraicGeometry.AbelianModuli.ReferenceFamily.TraceReconstructionEq.TraceReconstruction.coefficient ψ (e x) (e y) = ξ * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y := by
    apply AlgebraicGeometry.AbelianModuli.ReferenceFamily.TraceReconstructionEq.TraceReconstruction.coefficient_eq_of_trace
    intro a
    rw [← e.map_smul, he, NumberTheory.ArithmeticGroups.Trace.CongruenceLevel.hermitian_smul_left]
    congr 1
    ring
  have hm := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Matrices.TraceReconstruction.hermitianMatrix_evaluate ξ ψ hψ (e x) (e y)
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Matrices.TraceReconstruction.hermitianMatrix ξ ψ hψ) (e x) (e y) =
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reconstruction.TraceReconstruction.hermitianCoefficient ξ ψ (e x) (e y) at hm
  rw [hm, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reconstruction.TraceReconstruction.hermitianCoefficient, hc, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul]

def referenceTraceScalar {s : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) : E :=
  (P.denominator : E) * P.imaginaryScalar

theorem referenceTraceScalar_formula {s : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    P.traceForm x y = Algebra.trace ℚ E (referenceTraceScalar P * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b x y) := by
  unfold AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.traceForm referenceTraceScalar
  simpa only [nsmul_eq_mul, mul_assoc] using
    (map_nsmul (Algebra.trace ℚ E) P.denominator (P.imaginaryScalar * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b x y)).symm

theorem referenceTraceScalar_ne_zero {s : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) :
    referenceTraceScalar P ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (ne_of_gt hP.2.2.2.2.2.2.2.2.1)
  · exact hP.2.2.2.2.2.2.1

end

/-! The trace scaling and diagonal matrix retain the literal original
reference Hermitian form and purely imaginary coefficient. -/

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem matrixHermitian_reference_diagonal (b : E) (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian (Matrix.diagonal ![1, 1, b]) x y = NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y := by
  simp [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian, Fin.sum_univ_succ, Matrix.diagonal,
    mul_comm, mul_left_comm, mul_assoc]

theorem referenceTraceScalar_conjugate {s : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) :
    AlgebraicGeometry.ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (referenceTraceScalar P) = -referenceTraceScalar P := by
  unfold referenceTraceScalar
  rw [map_mul, map_natCast]
  change (P.denominator : E) * NumberField.IsCMField.complexConj E P.imaginaryScalar = _
  rw [hP.2.2.2.2.2.2.2.1, mul_neg]

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.DiagonalHermitian
