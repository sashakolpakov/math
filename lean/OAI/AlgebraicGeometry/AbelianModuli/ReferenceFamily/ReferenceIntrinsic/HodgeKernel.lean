import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.MarkedAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.ComplexCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection

/-! # Hodge Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Complexifying the actual reference marking identifies the native
period projection with the original reference quotient. Its kernel is
exactly the specified period-family subspace. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP)

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeComplexReferenceMarking : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) ≃ₗ[ℂ]
    ComplexMultiplication.WeightOne.CM.Complexification (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :=
  M.nativeReferenceMarking.baseChange ℚ ℂ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceProjection (u : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection M.abelian (M.nativeComplexReferenceMarking u) =
      M.periodDifferential (F.projection (P.referenceComplexCoordinates hP u)) := by
  let L := (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection M.abelian).comp M.nativeComplexReferenceMarking.toLinearMap
  let d : Reference.Fiber.ReferenceTangent s →ₗ[ℂ] RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian := M.periodDifferential.toLinearMap
  let R := (d.comp F.projection).comp (P.referenceComplexCoordinates hP).toLinearMap
  change L u = R u
  induction u using TensorProduct.inductionOn with
  | add u v hu hv =>
    exact (L.map_add u v).trans ((congrArg₂ (· + ·) hu hv).trans (R.map_add u v).symm)
  | tmul c v =>
    have hR : R (c ⊗ₜ[ℚ] v) = c • M.periodDifferential (F.periodEmbedding v) :=
      (congrArg (d.comp F.projection) (P.referenceComplexCoordinates_tmul hP c v)).trans
        ((d.comp F.projection).map_smul c (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates P.embeddings v))
    change c • (M.nativeReferenceMarking v).val = R (c ⊗ₜ[ℚ] v)
    exact (congrArg (fun w : RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian => c • w)
      (M.nativeReferenceMarking_apply v)).trans hR.symm

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceKernel (u : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    M.nativeComplexReferenceMarking u ∈ (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection M.abelian).ker ↔
      P.referenceComplexCoordinates hP u ∈ P.periodFamily z.val := by
  change Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection M.abelian (M.nativeComplexReferenceMarking u) = 0 ↔ _
  rw [M.nativeReferenceProjection]
  have h : M.periodDifferential (F.projection (P.referenceComplexCoordinates hP u)) = 0 ↔
      F.projection (P.referenceComplexCoordinates hP u) = 0 := M.periodDifferential.map_eq_zero_iff
  exact h.trans ((congrArg (fun S : Submodule ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) =>
    P.referenceComplexCoordinates hP u ∈ S) F.kernel).to_iff)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
