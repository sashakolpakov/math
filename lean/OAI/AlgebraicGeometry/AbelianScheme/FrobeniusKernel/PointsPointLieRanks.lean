import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsPointSourceComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsGeometricPointScalars
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.LieFieldTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActionDataLieTransport

/-! # Points Point Lie Ranks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsPointLieRanks.Construction

noncomputable section

/-!
Transport the actual CMPoints geometric-fiber Lie-rank conclusions to
the literal fixed-field FrobeniusKernel point datum. The scalar character,
dual-number operations and full source-data comparison are all
constructed in the imported adapters.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [NumberField.IsCMField E] [Field K] [NumberField K]
variable (M : PELModuli.CMPoints.Models.RankThreePELModel E K) {q : ℕ} [Fact q.Prime] {j : M.QadicChoice q}
variable (R : M.GoodIntegralReduction q j) (a : M.Family)
variable (x : ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a) (τ : Gal(E/ℚ)) (r : ℕ)

def l45FixedLieCharacter : NumberField.RingOfIntegers E →+* ModuliPoint.Construction.residueClosure q :=
  (algebraMap (ZMod q) (ModuliPoint.Construction.residueClosure q)).comp
    (PadicInt.toZMod.comp (j.localCharacter M.extendedEmbedding τ))

theorem l45TransportedFiber_hasLieRank
    (hr : R.HasLieRank a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x) τ r) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank
      ((PointsGeometricPointData.Construction.l45FiberActionData M R a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x)).pullback
        (Spec.map (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom)).polarized.abelian
      ((PointsGeometricPointData.Construction.l45FiberActionData M R a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x)).pullback
        (Spec.map (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom)).action
      (l45FixedLieCharacter M (j := j) τ) r := by
  let y := PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x
  let f := Spec.map (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom
  let er := (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).commRingCatIsoToRingEquiv
  have h := LieFieldTransport.Construction.hasLieRank_fieldIso (PointsGeometricPointData.Construction.l45FiberActionData M R a y).polarized.abelian er
    (PointsGeometricPointData.Construction.l45FiberActionData M R a y).action
    (R.lieCharacter a y τ) r hr
  change AbelianModuli.ReferenceFamily.LieRanks.HasLieRank ((R.fiberAbelian a y).pullback f) ((R.fiberAction a y).pullback f)
    ((PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom.hom.comp (R.lieCharacter a y τ)) r at h
  have hc : (PointsGeometricPointLift.Construction.l45GeometricPointFieldIso M R a x).hom.hom.comp (R.lieCharacter a y τ) =
      l45FixedLieCharacter M (j := j) τ := PointsGeometricPointScalars.Construction.l45GeometricPointFieldIso_lieCharacter M R a x τ
  rw [hc] at h
  exact h

theorem l45FixedPoint_hasLieRank
    (hr : R.HasLieRank a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x) τ r) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (PointsGeometricPointData.Construction.l45FixedPointActionData M R a x).polarized.abelian
      (PointsGeometricPointData.Construction.l45FixedPointActionData M R a x).action (l45FixedLieCharacter M (j := j) τ) r :=
  ActionDataLieTransport.Construction.polarizedActionIso_hasLieRank (PointsGeometricPointData.Construction.l45GeometricPointDataIso M R a x)
    (l45FixedLieCharacter M (j := j) τ) r (l45TransportedFiber_hasLieRank M R a x τ r hr)

variable (hM : M.HasPrescribedBallPeriods)
variable (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
variable (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
variable (hlabels : ∀ (v : Fin M.s) (b : Bool),
  labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))

/-- The conclusion is attached to the literal native point datum,
rather than a replacement family with matching numerical dimensions. -/
theorem l45PointDatum_hasLieRank
    (hr : R.HasLieRank a (PointsGeometricPointLift.Construction.l45GeometricPointIndex M R a x) τ r) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank
      ((CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a).pointDatum x).data.polarized.abelian
      ((CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a).pointDatum x).data.action
      (l45FixedLieCharacter M (j := j) τ) r :=
  l45FixedPoint_hasLieRank M R a x τ r hr

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsPointLieRanks.Construction
