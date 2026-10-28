import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.IntrinsicActiveClosure
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.ProjectionTopology
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELFiniteGroup
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseCoordinates

/-! # PEL Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELProjection.CM

noncomputable section

/-! The actual source symplectic projection agrees with the actual PEL
action in the original rational frame, on the full active/away source.
The proof uses continuity and the proved rational-source density. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.PhaseCoordinates.TestTransport OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)

theorem rational_matrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E C
      (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E C) g)).val =
      CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix E P (ComplexAction.CM.Symplectic.frame E C)
        (PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E C) P hb
          (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E C) g)) := by
  apply Finite.MatrixRationalDetermination.CM.ext
  intro v
  let x := (ComplexAction.CM.Symplectic.frame E C).symm v
  have hv : ComplexAction.CM.Symplectic.frame E C x = v := (ComplexAction.CM.Symplectic.frame E C).apply_symm_apply v
  have hleft : (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (ComplexAction.CM.Symplectic.symplectic E C g)).val *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (ComplexAction.CM.Symplectic.frame E C x) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (ComplexAction.CM.Symplectic.frame E C (g.val.val *ᵥ x)) := by
    funext i
    exact (RingHom.map_mulVec (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (ComplexAction.CM.Symplectic.symplectic E C g).val (ComplexAction.CM.Symplectic.frame E C x) i).symm.trans
      (congrArg (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (congrFun (ComplexAction.CM.Symplectic.symplectic_apply E C g x) i))
  let m := PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E C) P hb
    (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E C) g)
  have hx : CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (ComplexAction.CM.Symplectic.frame E C) (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (ComplexAction.CM.Symplectic.frame E C x) := CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates_rational E (ComplexAction.CM.Symplectic.frame E C) x
  have hright : CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix E P (ComplexAction.CM.Symplectic.frame E C) m *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (ComplexAction.CM.Symplectic.frame E C x) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (ComplexAction.CM.Symplectic.frame E C (g.val.val *ᵥ x)) :=
    (CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix_mulVec E P (ComplexAction.CM.Symplectic.frame E C) m _).trans
      ((congrArg (CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseAction E P (ComplexAction.CM.Symplectic.frame E C) m) hx.symm).trans
        ((CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseAction_coordinates E P (ComplexAction.CM.Symplectic.frame E C) m _).trans
          ((congrArg (CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E (ComplexAction.CM.Symplectic.frame E C))
            (PELFiniteGroup.CM.Matrix.rational_vector E (OppositeCoordinates.CM.coordinates E C) P hb g x)).trans
              (CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates_rational E (ComplexAction.CM.Symplectic.frame E C) (g.val.val *ᵥ x)))))
  have he := (congrArg (fun z : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (GeometricSource.CM.Positions E places) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => z.val *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (ComplexAction.CM.Symplectic.frame E C x))
    (ReferenceActiveWeil.CM.ReferenceFiniteProjection.rational E C g)).trans (hleft.trans hright.symm)
  exact (congrArg (fun y => (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E C
    (RationalLocal.CM.finiteHom E (OppositeCoordinates.CM.coordinates E C) g)).val *ᵥ
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal y) hv).symm.trans
        (he.trans (congrArg (fun y => CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix E P (ComplexAction.CM.Symplectic.frame E C) m *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal y) hv))

variable {d : Gal(E/ℚ) → Bool} (L : GeometricSource.CM.LinePeriod E B places d)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

theorem matrix (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] ×
    FactorTheta.CM.RationalWeilFactorization.Away E L f) :
    (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates
      (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f a)).val =
      CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix E P (ComplexAction.CM.Symplectic.frame E L.coordinates)
        (PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb
          (IntrinsicActiveClosure.CM.Intrinsic.assemble E L f a)) := by
  apply Finite.MatrixRationalDetermination.CM.ext
  intro v
  have he := (RationalDensity.CM.dense E L f).equalizer
    ((SourceFinite.ProjectionTopology.CM.original_action E L.coordinates (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal v)).comp
      (IntrinsicActiveClosure.CM.Intrinsic.continuous E L f))
    (((CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseAction_continuous E P (ComplexAction.CM.Symplectic.frame E L.coordinates)).comp
      (((PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb).continuous.comp
        (IntrinsicActiveClosure.CM.Intrinsic.continuous E L f)).prodMk continuous_const)).congr
          (fun a => (CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix_mulVec E P (ComplexAction.CM.Symplectic.frame E L.coordinates) _ (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal v)).symm))
    (funext (fun g => by
      dsimp only [Function.comp_apply]
      have h := IntrinsicActiveClosure.CM.Intrinsic.rational E L f g
      exact (congrArg (fun x => (ReferenceActiveWeil.CM.ReferenceFiniteProjection.projection E L.coordinates x).val *ᵥ
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal v) h).trans
        ((congrArg (fun M => M *ᵥ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal v) (rational_matrix E L.coordinates P hb g)).trans
          (congrArg (fun x => CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix E P (ComplexAction.CM.Symplectic.frame E L.coordinates)
            (PELFiniteGroup.CM.pel E (OppositeCoordinates.CM.coordinates E L.coordinates) P hb x) *ᵥ
              RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal v) h).symm)))
  exact congrFun he a

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELProjection.CM
