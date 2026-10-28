import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.CoordinateSupport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CMPELReferenceVector

/-! # CMPEL Residual Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CMPELResidualCoordinates.Approximation

noncomputable section

/-! Away from q, the filled PEL operator has exactly the original
rational matrix coordinates on every rational vector. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PEL.CoordinateSupport.TestTransport OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (hb : IsCMField.complexConj E P.b = P.b) (hb0 : P.b ≠ 0)
  {J : Type*} [Fintype J] [DecidableEq J] (e : (Fin 3 → E) ≃ₗ[ℚ] (J → ℚ))

theorem cmFinitePEL_filled_rational_coordinate_other
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (x : Fin 3 → E) (j : J)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e
      ((CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0
        (RestrictedInsert.Approximation.restrictedInsertPlace _ (CM.ActivePlace.Approximation.cmActivePlace E σ) (RestrictedAwaySame.Approximation.restrictedForgetPlace _ (CM.ActivePlace.Approximation.cmActivePlace E σ)
          (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ P.b hb hb0)
            (Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation E δ hδ hδ0 P.b hb hb0 γ))))).val
          (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)) j) = algebraMap ℚ (Padic p) (e (γ.val.val *ᵥ x) j) := by
  have he := PEL.CoordinateSupport.Approximation.cmFinitePEL_filled_coordinate_other E σ δ hδ hδ0 P hb hb0
    (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ P.b hb hb0)
      (Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation E δ hδ hδ0 P.b hb hb0 γ)) (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)
    ((LinearMap.proj j).comp (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e).toLinearMap) p hpq
  have hr := congrArg (fun y : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E =>
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e y j))
      (CMPELReferenceVector.Approximation.cmFinitePELHomeomorph_original_vector E δ hδ hδ0 P hb hb0 γ x)
  have hc := congrArg (fun y : J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles => RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (y j))
    (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates_rational E e (γ.val.val *ᵥ x))
  exact he.trans (hr.trans (hc.trans ((RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).commutes _)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CMPELResidualCoordinates.Approximation
