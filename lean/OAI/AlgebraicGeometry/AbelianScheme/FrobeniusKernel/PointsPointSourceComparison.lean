import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsGeometricPointData
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointData

/-! # Points Point Source Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsPointSourceComparison.Construction

noncomputable section

/-!
Attach the constructed CMPoints geometric residue-field comparison to the
literal FrobeniusKernel point datum of the native reduction. Every polarized,
marked and integral-action component comes from the original family.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [NumberField.IsCMField E] [Field K] [NumberField K]
variable (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
variable {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
variable (hsplit : j.HasSplitCoordinates M.extendedEmbedding) (R : M.GoodIntegralReduction q j)
variable (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
variable (hlabels : ∀ (v : Fin M.s) (b : Bool),
  labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))
variable (a : M.Family) (x : ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a)

theorem l45FixedPointActionData_eq_pointDatum :
    PointsGeometricPointData.Construction.l45FixedPointActionData M R a x =
      ((CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a).pointDatum x).data := rfl

/-- The exact source datum used by FrobeniusKernel is the CMPoints geometric-fiber
datum transported through the constructed native field isomorphism. -/
def l45PointSourceDataIso : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso
    ((PointsGeometricPointData.Construction.l45FiberActionData M R a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x)).pullback
      (Spec.map (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom))
    ((CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a).pointDatum x).data :=
  PointsGeometricPointData.Construction.l45GeometricPointDataIso M R a x

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsPointSourceComparison.Construction
