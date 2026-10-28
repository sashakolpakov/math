import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELPhaseProjection

/-! # Active Projection Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveProjectionSupport.CM

noncomputable section

/-! The actual original source active symplectic action is the identity
at every other rational prime, by the proved original PEL coordinates. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)

include hb in
theorem other (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom
      (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
        (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f (a, 1))) = 1 :=
  Subtype.ext
    ((congrArg (fun M => M.map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom)
      (PELProjection.CM.matrix E P hb L f (a, 1))).trans
        ((congrArg (fun g => (CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix E P (ComplexAction.CM.Symplectic.frame E L.coordinates)
          (PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb g)).map
            (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom)
          (IntrinsicActiveClosure.CM.Intrinsic.active E L f a)).trans
            (PELPhaseProjection.CM.source_active E (OppositeCoordinates.CM.coordinates E L.coordinates)
              f P hb (ComplexAction.CM.Symplectic.frame E L.coordinates) a hpq)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveProjectionSupport.CM
