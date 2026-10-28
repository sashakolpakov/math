import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity
import OAI.Geometry.ComplexBall.ArithmeticQuotientSplitUnitary
import OAI.RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace

/-! # Unitary Cross Matrix -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryCrossMatrix.Intrinsic

noncomputable section

/-! The conjugate embedding block is the inverse transpose relative to
the actual native cross-pairing matrix. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity OAI.RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (K : Type*) [Field K] [Algebra ℚ K]

omit [NumberField E] [NumberField.IsCMField E] in
theorem nativeMatrix_formMatrix : Intrinsic.Multiplicity.nativeMatrix E P = Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.formMatrix P.b := by
  apply congrArg Matrix.diagonal
  funext i
  fin_cases i <;> rfl

theorem unitary_cross_matrix (σ : E →ₐ[ℚ] K) (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    (g.val.val.map σ).transpose * (Intrinsic.Multiplicity.nativeMatrix E P).map σ *
      g.val.val.map (RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization.conjugateSplitEmbedding E K σ) = (Intrinsic.Multiplicity.nativeMatrix E P).map σ := by
  rw [nativeMatrix_formMatrix, Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.formMatrix,
    Matrix.diagonal_map (map_zero σ)]
  ext i j
  rw [Matrix.mul_apply]
  have h := congrArg σ ((Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitary_iff_columns
    (NumberField.IsCMField.complexConj E).toRingHom P.b g.val).mp g.property i j)
  by_cases hij : i = j <;>
    simpa [hij, RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization.conjugateSplitEmbedding_apply, mul_assoc, mul_left_comm, mul_comm] using h

theorem unitary_weighted_cross_matrix (σ : E →ₐ[ℚ] K) (θ : E)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    (g.val.val.map σ).transpose * (σ θ • (Intrinsic.Multiplicity.nativeMatrix E P).map σ) *
      g.val.val.map (RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization.conjugateSplitEmbedding E K σ) = σ θ • (Intrinsic.Multiplicity.nativeMatrix E P).map σ := by
  rw [Matrix.mul_smul, Matrix.smul_mul, unitary_cross_matrix]

theorem unitary_cross_inverseTranspose (σ : E →ₐ[ℚ] K) (θ : E)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    (σ θ • (Intrinsic.Multiplicity.nativeMatrix E P).map σ) * g.val.val.map (RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization.conjugateSplitEmbedding E K σ) =
      ((Matrix.SpecialLinearGroup.map σ.toRingHom g.val)⁻¹).val.transpose *
        (σ θ • (Intrinsic.Multiplicity.nativeMatrix E P).map σ) := by
  let A := Matrix.SpecialLinearGroup.map σ.toRingHom g.val
  have hi : (A⁻¹).val.transpose * A.val.transpose = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => (A⁻¹).val.transpose * M)
    (unitary_weighted_cross_matrix E P K σ θ g)
  change (A⁻¹).val.transpose * (A.val.transpose * (σ θ • (Intrinsic.Multiplicity.nativeMatrix E P).map σ) *
    g.val.val.map (RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization.conjugateSplitEmbedding E K σ)) = _ at h
  simpa only [← Matrix.mul_assoc, hi, Matrix.one_mul] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryCrossMatrix.Intrinsic
