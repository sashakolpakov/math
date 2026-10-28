import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FilledPEL
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CMPELResidualCoordinates

/-! # Residual Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ResidualCoordinates.ParameterChoices

noncomputable section

/-! The original filled native PEL element retains the original
rational coordinates at every prime away from q. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CMPELResidualCoordinates.Approximation

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  {J : Type*} [Fintype J] [DecidableEq J] (e : (Fin 3 → E) ≃ₗ[ℚ] (J → ℚ))

omit [IsGalois ℚ E] in
theorem nativeFilledPEL_other_coordinate (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU D.reference.b)
    (x : Fin 3 → E) (j : J) (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (CoefficientVectorCoordinates.TestTransport.coefficientVectorCoordinates E e
      ((FilledPEL.ParameterChoices.nativeFilledPEL E D hg γ).val (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x)) j) =
        algebraMap ℚ (Padic p) (e (γ.val.val *ᵥ x) j) :=
  CMPELResidualCoordinates.Approximation.cmFinitePEL_filled_rational_coordinate_other E (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false))
    D.reference.imaginaryScalar (OneTheta.Multiplicity.nativeOneDeltaImaginary E D.reference hg.reference_admissible)
    (OneTheta.Multiplicity.nativeOneDeltaNonzero E D.reference hg.reference_admissible) D.reference
    hg.reference_admissible.2.1 hg.reference_admissible.2.2.1 e γ x j p hpq

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ResidualCoordinates.ParameterChoices
