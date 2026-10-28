import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FinitePELHomeomorph
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LinearMapEvaluation

/-! # CMPEL Reference Vector -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CMPELReferenceVector.Approximation

noncomputable section

/-! The completed PEL identification sends every original rational
vector through the original rational unitary matrix. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LinearMapEvaluation.TestTransport OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (hb : IsCMField.complexConj E P.b = P.b) (hb0 : P.b ≠ 0)

theorem cmFinitePELHomeomorph_original_vector (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (x : Fin 3 → E) :
    (CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph E δ hδ hδ0 P hb hb0
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ P.b hb hb0)
        (Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation E δ hδ hδ0 P.b hb hb0 γ))).val
          (AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E x) = AbelianModuli.ReferenceFamily.AdelicData.finiteVectorEmbedding E (γ.val.val *ᵥ x) :=
  LinearMapEvaluation.TestTransport.linearMap_on_scalar_vectors (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E).toRingHom γ.val.val _
    (CM.FinitePELHomeomorph.Approximation.cmFinitePELHomeomorph_original E δ hδ hδ0 P hb hb0 γ) x

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CMPELReferenceVector.Approximation
