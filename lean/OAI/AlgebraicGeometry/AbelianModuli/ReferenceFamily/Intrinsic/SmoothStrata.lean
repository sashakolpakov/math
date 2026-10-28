import OAI.AlgebraicGeometry.ComplexPoints.Analytic.StratificationPointPartition
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.StratumSeparation

/-! # Smooth Strata -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SmoothStrata

noncomputable section

/-! Actual integral smooth pieces retain their native scheme inclusions,
and a finite stratification covers the original complex-valued points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (R : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricPiece X.hom)

def smoothPieceInclusion : R.toOver ⟶ X := R.toAmbient

instance smoothPiece_integral : IsIntegral R.toOver.left := R.integral

instance smoothPiece_smooth : Smooth R.toOver.hom := R.smooth

theorem smoothPiece_dimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension R.toOver.hom = R.complexDimension := rfl

instance smoothPieceInclusion_immersion : IsImmersion (smoothPieceInclusion X R).left := R.immersion

instance smoothPieceInclusion_mono : Mono (smoothPieceInclusion X R) :=
  Over.mono_of_mono_left _

theorem smoothPiece_secondCountable [SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] :
    SecondCountableTopology R.analyticSpace :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (smoothPieceInclusion X R)).secondCountableTopology

theorem smoothStratification_complexPoint_cover
    (Q : CycleClass.Geometric.IntegralSmoothStratification.IntegralSmoothGeometricStratification X.hom Set.univ) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ i : Fin Q.pieces.length, ∃ x : (Q.pieces.get i).analyticSpace,
      x ≫ smoothPieceInclusion X (Q.pieces.get i) = y := by
  have hy : y ∈ ⋃ i, Q.indexedAnalyticSupport i := by
    rw [Q.indexedAnalyticSupport_iUnion]
    trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
  change y ∈ (Q.pieces.get i).analyticSupport at hi
  rw [(Q.pieces.get i).analyticSupport_eq_range] at hi
  exact ⟨i, hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SmoothStrata
