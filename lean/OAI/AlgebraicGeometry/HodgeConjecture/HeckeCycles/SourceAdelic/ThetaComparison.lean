import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaDistinguishedBasis
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaCompactComponents
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaCriterion
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexFrame

/-! # Theta Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComparison.CM

noncomputable section

/-! The actual AdelicTheta Hodge subspace is exactly the original prescribed
source Lagrangian under the derived complex coordinate comparison. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexComponents.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

theorem components_mem (z : B.Domain) (w : GeometricSource.CM.Ambient E) :
    ThetaComplexComponents.CM.components E L w ∈ RepresentationTheory.Theta.Adelic.BallGeometryData.HodgeSubspace (Source.BallArithmetic.CM.data E L)
      (Source.BallNormalization.CM.equiv E B z) ↔ GeometricSource.CM.prescribed E B places d z.val w := by
  rw [Adelic.ThetaCriterion.CM.mem_iff]
  constructor
  · intro h v
    by_cases hv : v = places.distinguished
    · subst v
      rw [ite_eq_left rfl]
      have hd := Adelic.ThetaCriterion.CM.distinguished _ _ _ h 0
      exact ⟨(ThetaDistinguishedBasis.CM.Components.line_iff E L z.val w 0).mp hd.1,
        (ThetaDistinguishedBasis.CM.Components.annihilator_iff E L z.val w 0).mp hd.2⟩
    · rw [ite_eq_right hv]
      have hd := Adelic.ThetaCriterion.CM.compact _ _ _ h v hv 0
      exact (ThetaCompactComponents.CM.selected E L w v hv 0).mp hd
  · intro h
    apply Adelic.ThetaCriterion.CM.of_components
    · intro j
      have hd := h places.distinguished
      rw [ite_eq_left rfl] at hd
      exact ⟨(ThetaDistinguishedBasis.CM.Components.line_iff E L z.val w j).mpr hd.1,
        (ThetaDistinguishedBasis.CM.Components.annihilator_iff E L z.val w j).mpr hd.2⟩
    · intro v hv j
      change Fin places.count at v
      have hv' : v ≠ places.distinguished := hv
      have hd := h v
      rw [ite_eq_right hv'] at hd
      exact (ThetaCompactComponents.CM.selected E L w v hv' j).mpr hd

variable (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))

theorem equiv_mem (z : B.Domain) (w : GeometricSource.CM.Ambient E) :
    ThetaComplexFrame.CM.equiv E L T hT w ∈ RepresentationTheory.Theta.Adelic.BallGeometryData.HodgeSubspace (Source.BallArithmetic.CM.data E L)
      (Source.BallNormalization.CM.equiv E B z) ↔ GeometricSource.CM.prescribed E B places d z.val w := by
  rw [ThetaComplexFrame.CM.apply, components_mem]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComparison.CM
