import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ActiveFiniteMatrix
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatrixFixedCoordinates

/-! # PEL Phase Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELPhaseProjection.CM

noncomputable section

/-! Coordinate-wise fixedness under a finite PEL action identifies
its entire phase matrix at a prime. The actual source active factor
therefore has identity matrix at every other rational prime. -/

open scoped Classical _root_.Matrix _root_.NumberField

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  {J : Type*} [Fintype J] [DecidableEq J]
  (e : (Fin 3 → E) ≃ₗ[ℚ] (J → ℚ)) {p : ℕ} [Fact p.Prime]

theorem identity_of_coordinates (g : P.FiniteSpecialUnitary)
    (h : ∀ x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E, ∀ i : J,
      RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e (g.val x) i) =
        RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e x i)) :
    (CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix E P e g).map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom = 1 :=
  MatrixFixedCoordinates.CM.identity (CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e)
    (g.val.restrictScalars AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles).toLinearMap (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom h

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (F : IntermediateField ℚ ℂ) [NumberField F] [NumberField.IsCMField F]
  {B : GeometricSource.CM.BallDatum F} {places : GeometricSource.CM.Places F} (Q : GeometricSource.CM.SymplecticCoordinates F B places)
  {q : ℕ} [Fact q.Prime] (f : F →+* ℚ_[q])
  (P₀ : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum F s) (hb : P₀.b = B.b)
  (e₀ : (Fin 3 → F) ≃ₗ[ℚ] (J → ℚ))

theorem source_active (a : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) (hpq : p ≠ q) :
    (CMExtraction.PEL.PhaseCoordinates.TestTransport.pelPhaseMatrix F P₀ e₀ (Source.PELFiniteGroup.CM.pel F Q P₀ hb
      (Source.ActiveFiniteMatrix.CM.active F Q f a))).map (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom = 1 :=
  identity_of_coordinates P₀ e₀ _ (fun x i =>
    Source.ActiveFiniteMatrix.CM.other_coordinate F Q f P₀ hb a x
      ((LinearMap.proj i).comp (CMExtraction.CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates F e₀).toLinearMap) p hpq)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELPhaseProjection.CM
